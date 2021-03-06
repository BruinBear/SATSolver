#include "sat_api.h"

/******************************************************************************
* We explain here the functions you need to implement
*
* Rules:
* --You cannot change any parts of the function signatures
* --You can/should define auxiliary functions to help implementation
* --You can implement the functions in different files if you wish
* --That is, you do not need to put everything in a single file
* --You should carefully read the descriptions and must follow each requirement
******************************************************************************/

void printstuff(SatState* sat_state)
{
	if (sat_state->vars[19].status == implied_neg)
	{
		//print_sat_state_clauses(sat_state);
		printf("- ");
		
		return;
		//getc(stdin);
		//exit(1);
	}
	if (sat_state->vars[19].status == implied_pos)
	{
		//print_sat_state_clauses(sat_state);
		printf("+ ");
		return;
		//getc(stdin);
		//exit(1);
	}
}


/******************************************************************************
* Variables
******************************************************************************/

//returns a variable structure for the corresponding index
Var* sat_index2var(c2dSize index, const SatState* sat_state) {
	return (sat_state->vars) + (index - 1);
}

//returns the index of a variable
c2dSize sat_var_index(const Var* var) {
	return var->index;
}

//returns the variable of a literal
Var* sat_literal_var(const Lit* lit) {
	return lit->var;
}

//returns 1 if the variable is instantiated, 0 otherwise
//a variable is instantiated either by decision or implication (by unit resolution)
BOOLEAN sat_instantiated_var(const Var* var) {
	return (var->status) != free_var;
}


//returns 1 if all the clauses mentioning the variable are subsumed, 0 otherwise
BOOLEAN sat_irrelevant_var(const Var* var) {
	const ClausePtrVector* cv = &(var->original_cnf_array);
	Clause** c = cv->clause;
	c2dSize size = cv->current;

	for (unsigned int i = 0; i < size; i++)
	{
		// this clause isn't subsumed
		if (count_subsumed_lit(c[i]) == 0)
			return false;
	}
	return true;

}

//returns the number of variables in the cnf of sat state
c2dSize sat_var_count(const SatState* sat_state) {
	return sat_state->num_vars;
}

//returns the number of clauses mentioning a variable
//a variable is mentioned by a clause if one of its literals appears in the clause
c2dSize sat_var_occurences(const Var* var) {
	return var->num_clause_has;
}

//returns the index^th clause that mentions a variable
//index starts from 0, and is less than the number of clauses mentioning the variable
//this cannot be called on a variable that is not mentioned by any clause
Clause* sat_clause_of_var(c2dSize index, const Var* var) {
	return var->original_cnf_array.clause[index];
}

/******************************************************************************
* Literals
******************************************************************************/

//returns a literal structure for the corresponding index
Lit* sat_index2literal(c2dLiteral index, const SatState* sat_state) {
	if (index > 0)
		return sat_state->vars[index - 1].pos_lit;
	else
		return sat_state->vars[-1 * index - 1].neg_lit;
}

//returns the index of a literal
c2dLiteral sat_literal_index(const Lit* lit) {
	return lit->index;
}

//returns the positive literal of a variable
Lit* sat_pos_literal(const Var* var) {
	return var->pos_lit;
}

//returns the negative literal of a variable
Lit* sat_neg_literal(const Var* var) {
	return var->neg_lit;
}

//returns 1 if the literal is implied, 0 otherwise
//a literal is implied by deciding its variable, or by inference using unit resolution
BOOLEAN sat_implied_literal(const Lit* lit) {
	if (lit->index > 0)
		return lit->var->status == implied_pos;
	else
		return lit->var->status == implied_neg;
}

//sets the literal to true, and then runs unit resolution
//returns a learned clause if unit resolution detected a contradiction, NULL otherwise
//
//if the current decision level is L in the beginning of the call, it should be updated 
//to L+1 so that the decision level of lit and all other literals implied by unit resolution is L+1
Clause* sat_decide_literal(Lit* lit, SatState* sat_state) {
	//printstuff(sat_state);
	// Set the level of lit
	lit->var->level = (sat_state->decided_literals == NULL) ? 2 : (sat_state->decided_literals->lit->var->level + 1);

	// Set reason to be NULL, since it's decided!
	lit->reason = NULL;

	// Set status of var
	if (lit->index > 0)
		lit->var->status = implied_pos;
	else
		lit->var->status = implied_neg;
	// Add lit to head of decision literals list in sat_state
	LitNode* lnode = (LitNode*)malloc(sizeof(LitNode));
	initialize_LitNode(lnode);
	if (lit->var->level == 1)
	{
		//printf("Called get_ticket_number with %d(Decided) at level 1\n", lit->index);
		//getc(stdin);
	}
	get_ticket_number(lit->var, sat_state);

	lnode->lit = lit;
	lnode->next = sat_state->decided_literals;
	sat_state->decided_literals = lnode;

	// Do unit res
	// If succeed, return NULL
	// else return asserting clause
	sat_state->call_stat = decide_call;

	// test
	if (sat_unit_resolution(sat_state)) {
		return NULL;
	}
	else {
		// BOOKMARK
		//printf("Decision caused conflict: %d\n", lit->index);
		//LitNode* lnode = sat_state->decided_literals;
		//printf("Decision literals...\n");
		//while (lnode != NULL)
		//{
		//	printf("%d<%d> ", lnode->lit->index, lnode->lit->var->level);
		//	lnode = lnode->next;
		//}
		//printf("\nImplied literals...\n");
		//lnode = sat_state->implied_literals;
		//while (lnode != NULL)
		//{
		//	printf("%d<%d> ", lnode->lit->index, lnode->lit->var->level);
		//	lnode = lnode->next;
		//}
		Clause* c = get_asserting_clause(sat_state);
		//printf("Learned clause...\n");
		//print_clause(c);
		return c;
	}
}

//undoes the last literal decision and the corresponding implications obtained by unit resolution
//
//if the current decision level is L in the beginning of the call, it should be updated 
//to L-1 before the call ends
void sat_undo_decide_literal(SatState* sat_state) {
	//printstuff(sat_state);
	//assert(sat_state != NULL);
	if (sat_state->decided_literals == NULL)
		return;

	LitNode* last_decision = sat_state->decided_literals;
	c2dSize last_level = last_decision->lit->var->level;


	// Unmark the last decision, set var status to free, and set level of literal to 1
	unmark_a_literal(sat_state, last_decision->lit);
	last_decision->lit->var->status = free_var;
	last_decision->lit->var->level = 1;
	
	// delete node from list
	sat_state->decided_literals = sat_state->decided_literals->next;
	unget_ticket_number(last_decision->lit->var, sat_state);
	free(last_decision);

	// For each implied literal at the last decision level, unmark it, set var status to free, and set level of literal to 1
	// and remove node from list
	LitNode* lnode = sat_state->implied_literals;
	LitNode* prev = NULL;
	while (lnode != NULL) {
		if (lnode->lit->var->level == last_level) {
			if (prev == NULL) {
				sat_state->implied_literals = NULL;
				LitNode* to_free = lnode;
				while (to_free != NULL) {
					if (to_free->lit->var->level != last_level)
					{
						//print_sat_state_clauses(sat_state);
						printf("Freed a lit not at last level!!!!");
						getc(stdin);
						exit(1);

					}
					unmark_a_literal(sat_state, to_free->lit);
					to_free->lit->var->status = free_var;
					to_free->lit->var->level = 1;
					LitNode* hold = to_free->next;
					unget_ticket_number(to_free->lit->var, sat_state);
					free(to_free);
					to_free = hold;
				}
				break;
			}
			else {
				LitNode* to_free = lnode;
				while (to_free != NULL) {
					if (to_free->lit->var->level != last_level)
					{
						//print_sat_state_clauses(sat_state);
						printf("Freed a lit not at last level!!!!");
						getc(stdin);
						exit(1);

					}
					unmark_a_literal(sat_state, to_free->lit);
					to_free->lit->var->status = free_var;
					to_free->lit->var->level = 1;
					LitNode* hold = to_free->next;
					unget_ticket_number(to_free->lit->var, sat_state);
					free(to_free);
					to_free = hold;
				}
				prev->next = NULL;
				break;
			}
		}
		prev = lnode;
		lnode = lnode->next;
	}
	return; //dummy valued
}
/******************************************************************************
* Clauses
******************************************************************************/

//returns a clause structure for the corresponding index
Clause* sat_index2clause(c2dSize index, const SatState* sat_state) {
	ClauseNode* ptr = sat_state->cnf_head;
	c2dSize idx = 1;
	while (ptr != NULL && index != idx)
	{
		idx++;
		ptr = ptr->next;
	}
	return ptr->clause;
}

//returns the index of a clause
c2dSize sat_clause_index(const Clause* clause) {
	return clause->index;
}

//returns the literals of a clause
Lit** sat_clause_literals(const Clause* clause) {
	return clause->literals;
}

//returns the number of literals in a clause
c2dSize sat_clause_size(const Clause* clause) {
	return clause->num_lits;
}

//returns 1 if the clause is subsumed, 0 otherwise
BOOLEAN sat_subsumed_clause(const Clause* clause) {
	return count_subsumed_lit(clause) != 0;
}

//returns the number of clauses in the cnf of sat state
c2dSize sat_clause_count(const SatState* sat_state) {
	return sat_state->num_orig_clauses;
}

//returns the number of learned clauses in a sat state (0 when the sat state is constructed)
c2dSize sat_learned_clause_count(const SatState* sat_state) {

	if (sat_state->cnf_tail == NULL)
		return 0;
	return (sat_state->cnf_tail->clause->index) - (sat_state->num_orig_clauses);
}

// True if clause2's literals are also clause1's literals
BOOLEAN clause1_includes_clause2(Clause* clause1, Clause* clause2)
{
	Lit** lit1 = clause1->literals;
	Lit** lit2 = clause2->literals;

	for (unsigned int i = 0; i < clause2->num_lits; i++)
	{
		BOOLEAN has_lit = false;
		for (unsigned int j = 0; j < clause1->num_lits; j++)
		{
			if (lit1[j] == lit2[i])
			{
				has_lit = true;
				break;
			}
		}
		if (has_lit == false)
			return false;
	}
	return true;
}

Clause* get_clause_duplicate(Clause* clause, SatState* sat_state)
{
	ClauseNode* ptr = sat_state->cnf_head;
	while (ptr != NULL)
	{
		// If our clause is the same as something in the cnf
		// It isn't useful!
		if (clause1_includes_clause2(clause, ptr->clause) 
			&& clause1_includes_clause2(ptr->clause, clause))
			return ptr->clause;
		ptr = ptr->next;
	}
	return NULL;
}


//adds clause to the set of learned clauses, and runs unit resolution
//returns a learned clause if unit resolution finds a contradiction, NULL otherwise
//
//this function is called on a clause returned by sat_decide_literal() or sat_assert_clause()
//moreover, it should be called only if sat_at_assertion_level() succeeds
Clause* sat_assert_clause(Clause* clause, SatState* sat_state) {
	// Assume clause isn't empty
	assert(clause != NULL);
	
	//print_clause(clause);
	//printf("\n");

	//Clause* dup = get_clause_duplicate(clause, sat_state);
	//// Do a check that we're not adding a clause that is already in the cnf
	//if (dup != NULL)
	//{
	//	//print_sat_state_clauses(sat_state);
	//	printf("Duplicate clause\n");
	//	print_clause(clause);
	//	printf("\n");

	//	printf("Conflicting clause\n");
	//	print_clause(sat_state->conflict_reason);
	//	
	//	free(clause->literals);
	//	free(clause);
	//	getc(stdin);
	//	exit(1);
	//	
	//	// Set the contradicting clause in sat_state to NULL
	//	sat_state->conflict_reason = NULL;

	//	// Do unit resolution
	//	// If unit resolution succeeded, return NULL
	//	// else return asserting clause
	//	sat_state->call_stat = learn_call;
	//	if (sat_unit_resolution(sat_state))
	//		return NULL;
	//	else
	//		return get_asserting_clause(sat_state);

	//}
	//else
	//{
	//	printf("Not dup\n");
	//}

	// Add assert clause to lit related clauses
	for (unsigned int i = 0; i < clause->num_lits; i++) {
		ClauseNode* new_node = (ClauseNode*)malloc(sizeof(ClauseNode));
		initialize_ClauseNode(new_node);
		new_node->clause = clause;

		Lit* l = clause->literals[i];
		new_node->next = l->clauses;
		l->clauses = new_node;
		if (l->clauses_tail == NULL)
		{
			l->clauses_tail = new_node;
		}
	}
	

	// Set the clause index
	if (sat_state->cnf_tail != NULL)
		clause->index = sat_state->cnf_tail->clause->index + 1;

	// Add the learned clause to the cnf
	ClauseNode* cnode = (ClauseNode*)malloc(sizeof(ClauseNode));
	initialize_ClauseNode(cnode);
	cnode->clause = clause;
	sat_state->cnf_tail = append_node_ClauseNode(cnode, sat_state->cnf_tail);


	// Set the contradicting clause in sat_state to NULL
	sat_state->conflict_reason = NULL;

	// Do unit resolution
	// If unit resolution succeeded, return NULL
	// else return asserting clause
	sat_state->call_stat = learn_call;
	if (sat_unit_resolution(sat_state))
		return NULL;
	else
	{
		//BOOKMARK
		//printf("\nAdding learned clause caused conflict\n");

		//printf("Learned clause:\n");
		//print_clause(clause);
		//LitNode* lnode = sat_state->decided_literals;
		//printf("Decision literals...\n");
		//while (lnode != NULL)
		//{
		//	printf("%d<%d> ", lnode->lit->index, lnode->lit->var->level);
		//	lnode = lnode->next;
		//}
		//printf("\nImplied literals...\n");
		//lnode = sat_state->implied_literals;
		//while (lnode != NULL)
		//{
		//	printf("%d<%d> ", lnode->lit->index, lnode->lit->var->level);
		//	lnode = lnode->next;
		//}



		return get_asserting_clause(sat_state);
	}
		


}


/******************************************************************************
* A SatState should keep track of pretty much everything you will need to
* condition/uncondition variables, perform unit resolution, and do clause learning
*
* Given an input cnf file you should construct a SatState
*
* This construction will depend on how you define a SatState
* Still, you should at least do the following:
* --read a cnf (in DIMACS format, possible with weights) from the file
* --initialize variables (n of them)
* --initialize literals  (2n of them)
* --initialize clauses   (m of them)
*
* Once a SatState is constructed, all of the functions that work on a SatState
* should be ready to use
*
* You should also write a function that frees the memory allocated by a
* SatState (sat_state_free)
******************************************************************************/

SatState* sat_state_new(const char* cnf_fname)
{
	FILE* file = fopen(cnf_fname, "r");
	if (file == NULL) return NULL;

	SatState* state = (SatState *)malloc(sizeof(SatState));
	initialize_SatState(state);


	size_t line_size = 50;

	char* line = (char *)malloc(line_size* sizeof(char));

	unsigned int num_counted_clauses = 0;

	while (getline(&line, &line_size, file) != -1)
	{
		if (line[0] == 'c' || line[0] == '0' || line[0] == '%')
		{
			continue;
		}

		if (line[0] == 'p')
		{
			char* token;
			token = strtok(line, " \n\r");
			token = strtok(NULL, " \n\r");
			state->num_vars = atoi(strtok(NULL, " \n\r"));
			state->num_orig_clauses = atoi(strtok(NULL, " \n\r"));
			//printf("Num vars = %d\n", state->num_vars);
			//printf("Num original cnf clauses = %d\n", state->num_orig_clauses);
			state->vars = (Var *)malloc((state->num_vars) * sizeof(Var));
			int num_vars = state->num_vars;
			Var* vars = state->vars;
			for (int i = 0; i < num_vars; i++)
			{
				initialize_Var(&(vars[i]));
				vars[i].index = i + 1;
				vars[i].state = state;
				vars[i].neg_lit->index = -(i + 1);
				vars[i].pos_lit->index = i + 1;
				vars[i].pos_lit->var = &(vars[i]);
				vars[i].neg_lit->var = &(vars[i]);

			}
			continue;
		}

		// Otherwise, create a clause
		Clause* clause = (Clause *)malloc(sizeof(Clause));
		initialize_Clause(clause);

		//// Walk through it once first to count number of literals in clause
		//// By counting the number of spaces in the line

		//int num_lits = 0;
		//for (int i = 0; line[i] != '\0'; i++)
		//{
		//	if (line[i] == ' ')
		//		num_lits++;
		//}

		//if (num_lits == 0)
		//{
		//	free(clause);
		//	continue;
		//}
		//printf(" %d ", num_lits);

		//// Walk through it again to point to the literals
		//clause->num_lits = num_lits;
		//clause->literals = (Lit **)malloc(num_lits*sizeof(Lit*));
		
		int i = 0;
		LitPtrVector lpv;
		initialize_LitPtrVector(&lpv);

		char* token = strtok(line, " \r\n");
		while (token != NULL)
		{
			if (token[0] == '0')
				break;
			int lit_index = atoi(token);
			Lit* lit;

			// Get the literal
			if (lit_index > 0) // pos lit
				lit = state->vars[lit_index - 1].pos_lit;
			else
				lit = state->vars[(-1 * lit_index) - 1].neg_lit;

			// Put into lit ptr vector
			add_LitPtrVector(&lpv, lit);

			// Put this clause to the vector of the variable
			add(&(lit->var->original_cnf_array), clause);
			lit->var->num_clause_has += 1;

			// Put this clause to the list of the literal
			ClauseNode* cnode = (ClauseNode*)malloc(sizeof(ClauseNode));
			initialize_ClauseNode(cnode);
			cnode->clause = clause;
			if (lit->clauses == NULL)
				lit->clauses = cnode;
			lit->clauses_tail = append_node_ClauseNode(cnode, lit->clauses_tail);


			token = strtok(NULL, " ");
			i++;

		}
		if (i == 0)
		{
			free(clause);
			continue;
		}
			
		num_counted_clauses++;
		clause->num_lits = lpv.current;
		//printf("%d ", clause->num_lits);
		clause->literals = lpv.lits;

		// for (int i = 0; i < num_lits; i++)
		// {
		// 	printf(" %d ", clause->literals[i]->index);
		// }

		// Special case: if num_lits = 1, then unit clause. 
		// Add this to the implied literal list
		if (i == 1)
		{
			Lit * unit_lit = clause->literals[0];
			// Set the variable to be implied as pos/neg
			// But check first that there is no crazy contradiction already.
			if (unit_lit->var->status != free_var)
			{
				if ((unit_lit->var->status == implied_pos && unit_lit->index < 0)
					|| (unit_lit->var->status == implied_neg && unit_lit->index > 0))
				{
					unit_lit->var->status = conflicting;
					state->conflict_reason = clause;
				}

			}
			else
			{
				if (unit_lit->index > 0)
					unit_lit->var->status = implied_pos;
				else
					unit_lit->var->status = implied_neg;

			}

			// Set the reason as this clause 
			// (note since level is initialized as 1, no change needs to be made)
			unit_lit->reason = clause;

			//Put into a LitNode and put into list of implied literals
			LitNode* imp_lit_node = (LitNode*)malloc(sizeof(LitNode));
			initialize_LitNode(imp_lit_node);
			get_ticket_number(unit_lit->var, state);
			imp_lit_node->lit = unit_lit;
			imp_lit_node->next = state->implied_literals;
			state->implied_literals = imp_lit_node;

		}
		// put the clause into the cnf list

		ClauseNode* clause_node = (ClauseNode *)malloc(sizeof(ClauseNode));
		initialize_ClauseNode(clause_node);
		clause_node->clause = clause;
		clause->index = (state->cnf_tail == NULL) ? 1 : (state->cnf_tail->clause->index) + 1;
		if (state->cnf_head == NULL)
			state->cnf_head = clause_node;
		//state->cnf_tail = append_node(clause_node, state->cnf_tail); 
		if (state->cnf_tail != NULL) {
			(state->cnf_tail)->next = clause_node;
		}
		state->cnf_tail = clause_node;
		//printf("DID I GET HERE?");

	}
	//printstuff(state);
	//printf("DID I FINISH MAKING SATSTATE");
	//printf("Num counted clauses is... %d\n", num_counted_clauses);
	//print_sat_state_clauses(state);
	return state;
}


//frees the SatState
void sat_state_free(SatState* sat_state) {


	for (unsigned int i = 0; i < sat_state->num_vars; i++)
	{
		// For each literal, delete the list clauses (whole list, just the nodes), if not NULL
		ClauseNode* pos_lit_c = sat_state->vars[i].pos_lit->clauses;
		ClauseNode* neg_lit_c = sat_state->vars[i].neg_lit->clauses;
		ClauseNode* ptr = pos_lit_c;
		while (ptr != NULL)
		{
			ptr = ptr->next;
			free(pos_lit_c);
			pos_lit_c = ptr;
		}
		ptr = neg_lit_c;
		while (ptr != NULL)
		{
			ptr = ptr->next;
			free(neg_lit_c);
			neg_lit_c = ptr;
		}

		// For each var, delete original_cnf_array (delete the array in this vector)
		free((sat_state->vars[i].original_cnf_array).clause);
	}

	// Delete vars array
	free(sat_state->vars);


	// For each clause node in cnf_head list (if not NULL)
	ClauseNode* cnf_c = sat_state->cnf_head;
	ClauseNode* cnf_next = cnf_c;
	while (cnf_next != NULL)
	{
		cnf_next = cnf_next->next;

		// free the Lit** literals in the clause
		free(cnf_c->clause->literals);

		// free the clause
		free(cnf_c);

		cnf_c = cnf_next;
	}


	// Delete decided_literals (whole list, just the nodes), if not NULL
	LitNode* lnode = sat_state->decided_literals;
	LitNode* lnode_next = lnode;
	while (lnode_next != NULL)
	{
		lnode_next = lnode_next->next;
		free(lnode);
		lnode = lnode_next;
	}

	// Delete implied_literals (whole list, just the nodes), if not NULL
	lnode = sat_state->implied_literals;
	lnode_next = lnode;
	while (lnode_next != NULL)
	{
		lnode_next = lnode_next->next;
		free(lnode);
		lnode = lnode_next;
	}


	// Delete sat_state
	free(sat_state);

	return; //dummy valued
}

/******************************************************************************
* Given a SatState, which should contain data related to the current setting
* (i.e., decided literals, subsumed clauses, decision level, etc.), this function
* should perform unit resolution at the current decision level
*
* It returns 1 if succeeds, 0 otherwise (after constructing an asserting
* clause)
*
* There are three possible places where you should perform unit resolution:
* (1) after deciding on a new literal (i.e., in sat_decide_literal())
* (2) after adding an asserting clause (i.e., in sat_assert_clause(...))
* (3) neither the above, which would imply literals appearing in unit clauses
*
* (3) would typically happen only once and before the other two cases
* It may be useful to distinguish between the above three cases
*
* Note if the current decision level is L, then the literals implied by unit
* resolution must have decision level L
*
* This implies that there must be a start level S, which will be the level
* where the decision sequence would be empty
*
* We require you to choose S as 1, then literals implied by (3) would have 1 as
* their decision level (this level will also be the assertion level of unit
* clauses)
*
* Yet, the first decided literal must have 2 as its decision level
******************************************************************************/

Lit* get_free_literal_from_clause(Clause* c) {
	for (unsigned int i = 0; i < c->num_lits; i++) {
		if (c->literals[i]->var->status == free_var) {
			return c->literals[i];
		}
	}
	return NULL;
}

LitNode* append(LitNode* head, LitNode* n) {
	LitNode* tmp = head;
	if (tmp != NULL) {
		while (tmp->next != NULL)
			tmp = tmp->next;
		tmp->next = n;
		return head;
	}
	else { // just one
		return n;
	}
}


// return true if no conflict
// else return false and assign a clause to conflict reason
BOOLEAN mark_a_literal(SatState* sat_state, Lit* lit) {
	// return true;
	
	//printstuff(sat_state);
	if (lit->index > 0) {
		lit->var->status = implied_pos;
	}
	else {
		lit->var->status = implied_neg;
	}
	if (lit->var->ticket == 0)
	{
		print_sat_state_clauses(sat_state);
		printf("\nLit %d got implied in mark_a_literal but didn't get ticket!\n", lit->index);
		getc(stdin);
	}

	ClauseNode* resolved_head = flip_lit(lit)->clauses;
	while (resolved_head != NULL) {
		if (count_subsumed_lit(resolved_head->clause) == 0 &&
			count_free_lit(resolved_head->clause) == 0) {//conflict
			sat_state->conflict_reason = resolved_head->clause;
			return false;
		}
		else if (count_subsumed_lit(resolved_head->clause) == 0 &&
			count_free_lit(resolved_head->clause) == 1){

			Lit* new_implied = get_free_literal_from_clause(resolved_head->clause);

			new_implied->var->level = lit->var->level;

			// set level
			// add the newly implied literal
			LitNode* lnode = (LitNode*)malloc(sizeof(LitNode));
			initialize_LitNode(lnode);
			if (new_implied->var->level == 1)
			{
				//print_sat_state_clauses(sat_state);
				//printf("\n\nReason for this is: %d", sat_state->call_stat);
				//printf("\n\nCalled get_ticket_number with %d(Implied by %d<%d>[%d](%d)) at level 1\n", new_implied->index, lit->index, lit->var->level, lit->var->ticket, lit->var->status);
				//getc(stdin);
			}
			get_ticket_number(new_implied->var, sat_state);
			lnode->lit = new_implied;
			lnode->lit->var->status = (lnode->lit->index>0) ? implied_pos : implied_neg;
			lnode->lit->reason = resolved_head->clause;
			sat_state->implied_literals = append(sat_state->implied_literals, lnode);
		}
		resolved_head = resolved_head->next;
	}

	return true;
}

void unmark_a_literal(SatState* sat_state, Lit* lit) {
	ClauseNode* resolved_head = flip_lit(lit)->clauses;
	while (resolved_head != NULL) {
		resolved_head = resolved_head->next;
	}
	lit->reason = NULL;
	lit->var->status = free_var;
	
}

c2dSize get_last_level(Clause* reason) {
  c2dSize last_level = 0;
  for (unsigned long i = 0; i < reason->num_lits; i++) {
    if (reason->literals[i]->var->level >  last_level) {
      last_level = reason->literals[i]->var->level;
    }
  }
  return last_level;
}

//applies unit resolution to the cnf of sat state
//returns 1 if unit resolution succeeds, 0 if it finds a contradiction
BOOLEAN sat_unit_resolution(SatState* sat_state) {
	// Test: Check the status of variable 20
	//printstuff(sat_state);

	if (sat_state == NULL)
	{
		//printf("SatState null at sat_unit_res!");
		//getc(stdin);
		exit(1);
	}
	if (sat_state->call_stat == first_call) {
		if (sat_state->conflict_reason != NULL)
		{
			return false;
		}

		LitNode* tmp = sat_state->implied_literals;
		while (tmp != NULL) {
			if (tmp->lit->var->ticket == 0)
			{
				printf("Marking a non-ticketed literal %d in first_call unit res\n", tmp->lit->index);
				getc(stdin);
			}
			if (!mark_a_literal(sat_state, tmp->lit)) {
				return 0;
			}
			tmp = tmp->next;
		}
		//print_sat_state_clauses(sat_state);
	}
	else if (sat_state->call_stat == decide_call) { // mark on a decision
		LitNode* tmp = sat_state->implied_literals;

		if (tmp != NULL) {
			while (tmp->next != NULL)
				tmp = tmp->next;
		}

		// bug
		if (sat_state->decided_literals->lit->var->ticket == 0)
		{
			printf("Marking a non-ticketed literal %d in decide_call unit res\n", sat_state->decided_literals->lit->index);
			getc(stdin);
		}
		if (!mark_a_literal(sat_state, sat_state->decided_literals->lit)) {
			return false;
		}
		// if originally no implied
		if (tmp == NULL) {
			tmp = sat_state->implied_literals;
		}
		else {
			tmp = tmp->next;
		}
		while (tmp != NULL) {
			if (tmp->lit->var->ticket == 0)
			{
				printf("Marking a non-ticketed literal %d in decide_call unit res\n", tmp->lit->index);
				getc(stdin);
			}
			if (!mark_a_literal(sat_state, tmp->lit)) {
				return 0;
			}
			tmp = tmp->next;
		}
		return 1;
	}
	else if (sat_state->call_stat == learn_call) {
		//printf("Learned call\n");

		Clause* c = sat_state->cnf_tail->clause;
		//print_clause(c);
		//printf("Num free: %d, Num subsume: %d\n", count_free_lit(c), count_subsumed_lit(c));

		if (count_subsumed_lit(c) != 0 && count_free_lit(c) == 0){ // conflict
			printf("Learned clause is conflicting!!!!\n");
			sat_state->conflict_reason = c;
			return 0;
		}
		else if (count_subsumed_lit(c) == 0 && count_free_lit(c) == 1) { // new imply
			LitNode* tmp = sat_state->implied_literals;
			// tmp is now the tail;
			if (tmp != NULL) {
				while (tmp->next != NULL)
					tmp = tmp->next;
			}
			//printf("Learned clause implies literal...%d\n", get_free_literal_from_clause(c)->index);

			Lit* going_to_mark = get_free_literal_from_clause(c);
			going_to_mark->var->level = get_last_level(c);
			going_to_mark->reason = c;
			
			// Get ticket number and add to implied literal queue in sat_state
			get_ticket_number(going_to_mark->var, sat_state);
			LitNode* going_to_mark_node = (LitNode*)malloc(sizeof(LitNode));
			initialize_LitNode(going_to_mark_node);
			going_to_mark_node->lit = going_to_mark;
			sat_state->implied_literals = append(sat_state->implied_literals, going_to_mark_node);
			
			if (going_to_mark->var->ticket == 0)
			{
				printf("Marking a non-ticketed literal %d in learned_call unit res\n", going_to_mark->index);
				getc(stdin);
			}
			
			if (!mark_a_literal(sat_state, going_to_mark)){
				return 0;
			}
			if (tmp == NULL) {
				tmp = sat_state->implied_literals;
			}
			else {
				tmp = tmp->next;
			}
			while (tmp != NULL) {
				if (tmp->lit->var->ticket == 0)
				{
					printf("Marking a non-ticketed literal %d in first_call unit res\n", tmp->lit->index);
					getc(stdin);
				}
				if (!mark_a_literal(sat_state, tmp->lit)) {
					return 0;
				}
				tmp = tmp->next;
			}
		}
	}
	return 1;
}

//undoes sat_unit_resolution(), leading to un-instantiating variables that have been instantiated
//after sat_unit_resolution()
void sat_undo_unit_resolution(SatState* sat_state) {
	LitNode* decided = sat_state->decided_literals;
	LitNode* implied = sat_state->implied_literals;
	while (decided != NULL) {
		decided->lit->var->status = free_var;
		decided = decided->next;
	}
	while (implied != NULL) {
		implied->lit->var->status = free_var;
		implied = implied->next;
	}
	return;
}

//returns 1 if the decision level of the sat state equals to the assertion level of clause,
//0 otherwise
//
//this function is called after sat_decide_literal() or sat_assert_clause() returns clause.
//it is used to decide whether the sat state is at the right decision level for adding clause.
BOOLEAN sat_at_assertion_level(const Clause* clause, const SatState* sat_state) {
	// Assume clause isn't NULL and has more than 0 literal
	assert(clause != NULL && clause->num_lits > 0);

	c2dSize decision_level;
	if (sat_state->decided_literals == NULL)
		decision_level = 1;
	else
		decision_level = sat_state->decided_literals->lit->var->level;

	//if (clause->num_lits == 1)
	//	return (1 == decision_level);

	//c2dSize assertion_level = 1;
	//c2dSize highest_level = 1;

	//// get highest level
	//for (unsigned int i = 0; i < clause->num_lits; i++)
	//{
	//	if ((clause->literals[i]->var->level)>highest_level)
	//		highest_level = (clause->literals[i]->var->level);
	//}

	//// get assertion_level
	//for (unsigned int i = 0; i < clause->num_lits; i++)
	//{
	//	if (((clause->literals[i]->var->level)>assertion_level)
	//		&& ((clause->literals[i]->var->level) != highest_level))
	//		assertion_level = (clause->literals[i]->var->level);
	//}
	//return decision_level == assertion_level;	
	//
	
	return decision_level == sat_state->assertion_level;
	// BOOKMARK

}

/******************************************************************************
* The functions below are already implemented for you and MUST STAY AS IS
******************************************************************************/

//returns the weight of a literal (which is 1 for our purposes)
c2dWmc sat_literal_weight(const Lit* lit) {
	return 1;
}

//returns 1 if a variable is marked, 0 otherwise
BOOLEAN sat_marked_var(const Var* var) {
	return var->mark;
}

//marks a variable (which is not marked already)
void sat_mark_var(Var* var) {
	var->mark = 1;
}

//unmarks a variable (which is marked already)
void sat_unmark_var(Var* var) {
	var->mark = 0;
}

//returns 1 if a clause is marked, 0 otherwise
BOOLEAN sat_marked_clause(const Clause* clause) {
	return clause->mark;
}

//marks a clause (which is not marked already)
void sat_mark_clause(Clause* clause) {
	clause->mark = 1;
}
//unmarks a clause (which is marked already)
void sat_unmark_clause(Clause* clause) {
	clause->mark = 0;
}

/******************************************************************************
* Added function
******************************************************************************/

void get_ticket_number(Var* v, SatState* sat_state)
{
	/*if (v->level == 1)
	{
		v->ticket = sat_state->ticket_number;
		print_sat_state_clauses(sat_state);
		printf(" %d<%d>[%d] ", v->index, v->level, v->ticket);
		getc(stdin);

	}*/

	v->ticket = sat_state->ticket_number;
	if (sat_state->ticket_number == 0)
	{
		printf("\nTicket num = 0!!!!!!");
		getc(stdin);
	}
	//printf(" %d<%d>[%d] ", v->index, v->level, v->ticket);
	sat_state->ticket_number += 1;
}

void unget_ticket_number(Var* v, SatState* sat_state)
{
	v->ticket = 0;
	v->status = free_var;
	//sat_state->ticket_number -= 1;
}

void initialize_Lit(Lit* l) {
	l->index = 1;
	l->clauses = NULL;
	l->clauses_tail = NULL;
	l->var = NULL;
	l->reason = NULL;
}

void initialize_LitNode(LitNode* l) { l->lit = NULL; l->next = NULL; }

void add(ClausePtrVector* cv, Clause* c)
{
	if (cv->clause == NULL)
	{
		cv->clause = (Clause**)malloc(cv->limit*sizeof(Clause*));
	}
	else if (cv->current == cv->limit)
	{
		cv->limit += 2;
		cv->clause = (Clause**)realloc(cv->clause, cv->limit*sizeof(Clause*));
		if (cv->clause == NULL)
		{
			exit(1);
		}

	}
	cv->clause[cv->current] = c;
	cv->current++;
}


void add_LitPtrVector(LitPtrVector* lv, Lit* l)
{
	if (lv->lits == NULL)
	{
		lv->lits = (Lit**)malloc(lv->limit*sizeof(Lit*));
	}
	else if (lv->current == lv->limit)
	{
		lv->limit += 2;
		lv->lits = (Lit**)realloc(lv->lits, lv->limit*sizeof(Lit*));
		if (lv->lits == NULL)
		{
			//printf("Not able to add more literal ptrs to this vector!!!\n");
			//getc(stdin);
			exit(1);
		}

	}
	lv->lits[lv->current] = l;
	lv->current++;
}


void initialize_ClausePtrVector(ClausePtrVector* c) {
	c->clause = NULL;
	c->limit = 5;
	c->current = 0;
}

void initialize_LitPtrVector(LitPtrVector* l) {
	l->lits = NULL;
	l->limit = 3;
	l->current = 0;
}

void initialize_Var(Var* v) {
	v->pos_lit = (Lit*)malloc(sizeof(Lit));
	v->neg_lit = (Lit*)malloc(sizeof(Lit));
	initialize_Lit(v->pos_lit);
	initialize_Lit(v->neg_lit);
	v->status = free_var;
	v->ticket = 0;
	v->num_clause_has = 0;
	v->state = NULL;
	v->level = 1;
  v->mark = 0;
	initialize_ClausePtrVector(&v->original_cnf_array);
}

void initialize_Clause(Clause * c) {
	c->literals = NULL;
	c->num_lits = 0;
	// c->subsuming_literal_count = 0;
	// c->free_literal_count = 0;
	c->watch1 = NULL;
	c->watch2 = NULL;
  c->mark = 0;
}

void initialize_ClauseNode(ClauseNode* c) {
	c->next = NULL;
	c->clause = NULL;
}

void initialize_SatState(SatState* s) {
	s->vars = NULL;
	s->num_vars = 0;
	s->cnf_head = NULL;
	s->cnf_tail = NULL;
	s->num_orig_clauses = 0;
	s->num_asserted_clauses = 0;
	s->assertion_level = 1;
	s->decided_literals = NULL;
	s->conflict_reason = NULL;
	s->implied_literals = NULL;
	s->implied_literals_tail = NULL;
	s->call_stat = first_call;
	s->ticket_number = 1;
}

LitNode* append_node_LitNode(LitNode* node, LitNode* tail) {
	if (tail != NULL) {
		tail->next = node;
	}
	return node;
}

ClauseNode* append_node_ClauseNode(ClauseNode* node, ClauseNode* tail) {
	if (tail != NULL) {
		tail->next = node;
	}
	return node;
}




Lit* flip_lit(Lit* lit) {
	if (lit->index > 0) {
		return sat_neg_literal(lit->var);
	}
	else {
		return sat_pos_literal(lit->var);
	}
}

BOOLEAN is_lit_duplicate(LitNode* head, Lit* lit) {
	while (head != NULL) {
		if (head->lit == lit) {
			return true;
		}
		head = head->next;
	}
	return false;
}


Clause* make_clause_from_lit(LitNode* head) {
	Clause* clause = (Clause *)malloc(sizeof(Clause));
	initialize_Clause(clause);
	unsigned int i = 0;
	LitNode* tmp = head;
	while (tmp != NULL) {
		i++;
		tmp = tmp->next;
	}
	clause->num_lits = i;
	clause->literals = (Lit **)malloc(clause->num_lits*sizeof(Lit*));
	i = 0;
	tmp = head;
	while (tmp != NULL) {
		clause->literals[i] = flip_lit(tmp->lit);
		tmp = tmp->next;
		i++;
	}
	return clause;
}


Clause* get_asserting_clause(SatState* sat_state) {
	//printstuff(sat_state);
	LitNode* q_head = NULL; // Note this has been used w/o being initilized
	LitNode* l_head = NULL; // Note this has been used w/o being initilized
	Clause* conflict_reason = sat_state->conflict_reason;
	
	unsigned long last_level = get_last_level(conflict_reason);
	// initialize from conflict
	for (unsigned long i = 0; i < conflict_reason->num_lits; i++) {

		LitNode* node = (LitNode*)malloc(sizeof(LitNode));
		initialize_LitNode(node);
		node->lit = flip_lit(conflict_reason->literals[i]);
		if (conflict_reason->literals[i]->var->level == last_level) { // last level node added to queue
			if (!is_lit_duplicate(q_head, node->lit)) {
				if (q_head == NULL) {
					q_head = node;
				}
				else {
					q_head = append(q_head, node);
				}
				LitNode* tmp = q_head;
				while (tmp != NULL) {
					tmp = tmp->next;
				}
			}
		}
		else {
			if (!is_lit_duplicate(l_head, node->lit)) { // not last level node added to list
				if (l_head == NULL) {
					l_head = node;
				}
				else {
					l_head = append(l_head, node);
				}
			}
		}
	}

	if (q_head == NULL)
	{
		q_head->next = l_head;
		Clause* c = make_clause_from_lit(q_head);
		return c;
	}

	// Constructing queue and list
	// If more than one literal at last level

	while (q_head->next != NULL)
	{
		// Get the highest ticket number in the q_head list
		LitNode* q_ptr = q_head;
		LitNode* prev_of_highest_ticket_lit = NULL;
		Lit* highest_ticket_lit = q_head->lit;
		while (q_ptr->next != NULL)
		{
			if (q_ptr->next->lit->var->ticket > highest_ticket_lit->var->ticket)
			{
				highest_ticket_lit = q_ptr->next->lit;
				prev_of_highest_ticket_lit = q_ptr;
			}
			q_ptr = q_ptr->next;
		}

		// The decided lit at highest level has higher ticket number than implied
		// This should not happen!
		if (highest_ticket_lit->reason == NULL) {
			//print_sat_state_clauses(sat_state);
			printf("Highest ticket lit has no reason...ticket=%d, level=%d\n", highest_ticket_lit->var->ticket, highest_ticket_lit->var->level);
			print_clause(conflict_reason);
			printf("Called because...");
			if (sat_state->call_stat == learn_call)
				printf("learned\n");
			else if (sat_state->call_stat == decide_call)
				printf("decide\n");
			else
				printf("first time\n");
			assert(false);
		}

		// Otherwise it's an implied lit
		Clause* reason = highest_ticket_lit->reason;
		for (unsigned long i = 0; i < reason->num_lits; i++) {
			if (highest_ticket_lit == reason->literals[i]) {
				continue;
			}
			LitNode* node = (LitNode*)malloc(sizeof(LitNode));
			initialize_LitNode(node);
			node->lit = flip_lit(reason->literals[i]);
			if (reason->literals[i]->var->level == last_level) { // last level node added to queue
				if (!is_lit_duplicate(q_head, node->lit)) {
					q_head = append(q_head, node);
				}
			}
			else {
				if (!is_lit_duplicate(l_head, node->lit)) { // not last level node added to list
					l_head = append(l_head, node);
				}
			}
		}


		// Remove the litnode after prev_of_highest_lit_node
		if (prev_of_highest_ticket_lit != NULL)
		{
			LitNode* to_free = prev_of_highest_ticket_lit->next;
			prev_of_highest_ticket_lit->next = to_free->next;
			free(to_free);
		}
		else
		{
			// Free the head
			LitNode* to_free = q_head;
			q_head = q_head->next;
			free(to_free);
		}

	}

	LitNode* tmp = l_head;
	while (tmp != NULL) {
		tmp = tmp->next;
	}

	tmp = q_head;
	while (tmp != NULL) {
		tmp = tmp->next;
	}
	q_head->next = l_head;
	Clause* clause = make_clause_from_lit(q_head);
//BOOKMARK
	// Get assertion level from this clause

	if (clause->num_lits == 1)
	{
		sat_state->assertion_level = 1;
		return clause;
	}

	c2dSize assertion_level = 1;
	c2dSize highest_level = 1;

	// Get highest level
	for (unsigned int i = 0; i < clause->num_lits; i++)
	{
		if ((clause->literals[i]->var->level)>highest_level)
			highest_level = (clause->literals[i]->var->level);
	}

	// Get assertion_level
	for (unsigned int i = 0; i < clause->num_lits; i++)
	{
		if (((clause->literals[i]->var->level)>assertion_level)
			&& ((clause->literals[i]->var->level) != highest_level))
			assertion_level = (clause->literals[i]->var->level);
	}

	sat_state->assertion_level = assertion_level;

	return clause;
}


unsigned int count_free_lit(Clause* c) {
	unsigned int count = 0;
	for (unsigned i = 0; i<c->num_lits; i++) {
		if (c->literals[i]->var->status == free_var) {
			count++;
		}
	}
	return count;
}


unsigned int count_subsumed_lit(Clause* c) {
	if (c == NULL)
	{
		//printf("Called count_subsumed_lit with NULL clause\n");
		//getc(stdin);
		exit(1);
	}
	unsigned int count = 0;
	for (unsigned i = 0; i<c->num_lits; i++) {
		if ((c->literals[i]->var->status == implied_pos
			&& c->literals[i]->index>0) ||
			(c->literals[i]->var->status == implied_neg
			&& c->literals[i]->index<0)) {
			count++;
		}
	}
	return count;
}

void print_clause(Clause* c) {
	for (unsigned int i = 0; i < c->num_lits; i++) {
		printf(" %d<%d>[%d]", c->literals[i]->index, c->literals[i]->var->level, c->literals[i]->var->ticket);
		if (c->literals[i]->var->status == free_var)
			printf("(free) ");
		else if (c->literals[i]->var->status == implied_pos)
			printf("(pos) ");
		else if (c->literals[i]->var->status == implied_neg)
			printf("(neg) ");
	}
	printf("\n");
}

void print_sat_state_clauses(SatState* sat_state) {
	printf("\n\nPrinting all clauses...\n");
	ClauseNode* cnf_ptr = sat_state->cnf_head;
	while (cnf_ptr != NULL)
	{
		Clause* c = cnf_ptr->clause;
		print_clause(c);
		cnf_ptr = cnf_ptr->next;
	}

	printf("\n\nPrinting all decided...\n");
	LitNode* n = sat_state->decided_literals;
	while (n != NULL) {
		printf(" %d<%d>[%d]", n->lit->index, n->lit->var->level, n->lit->var->ticket);
		n = n->next;
	}
	printf("\n");


	printf("\n\nPrinting all implied...\n");
	n = sat_state->implied_literals;
	while (n != NULL) {
		printf(" %d<%d>[%d]", n->lit->index, n->lit->var->level, n->lit->var->ticket);
		n = n->next;
	}
	printf("\n");

}

BOOLEAN assignment_is_sat(SatState* sat_state)
{
	ClauseNode* cnf_ptr = sat_state->cnf_head;
	while (cnf_ptr != NULL)
	{
		Lit** l = cnf_ptr->clause->literals;
		BOOLEAN clause_subsumed = false;
		for (unsigned int i = 0; i < cnf_ptr->clause->num_lits; i++)
		{
			if (l[i]->var->status == free_var)
			{
				return false;
			}
			if ((l[i]->var->status == implied_neg && l[i]->index < 0)
				|| (l[i]->var->status == implied_pos && l[i]->index > 0))
			{
				clause_subsumed = true;
				break;
			}
		}
		if (!clause_subsumed)
			return false;
		cnf_ptr = cnf_ptr->next;
	}
	return true;
}


/******************************************************************************
* end
******************************************************************************/
