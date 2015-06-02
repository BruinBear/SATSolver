#include "satapi.h"
#include "getline.h" // DELETE ME IN THE REAL THING
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
		if (c[i]->subsuming_literal_count == 0)
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

	// Set the level of lit
	lit->level = (sat_state->decided_literals == NULL) ? 2 : (sat_state->decided_literals->lit->level + 1);

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
	lnode->lit = lit;
	lnode->next = sat_state->decided_literals;
	sat_state->decided_literals = lnode;

	// Do unit res
	// If succeed, return NULL
	// else return asserting clause
	sat_state->call_stat = decide_call;
	if (sat_unit_resolution(sat_state))
		return NULL;
	else
		return get_asserting_clause(sat_state);
}

//undoes the last literal decision and the corresponding implications obtained by unit resolution
//
//if the current decision level is L in the beginning of the call, it should be updated 
//to L-1 before the call ends
void sat_undo_decide_literal(SatState* sat_state) {
	assert(sat_state != NULL);
	if (sat_state->decided_literals == NULL)
		return;

	LitNode* last_decision = sat_state->decided_literals;
	c2dSize last_level = last_decision->lit->level;

	// Unmark the last decision, set var status to free, and set level of literal to 1
	unmark_a_literal(sat_state, last_decision->lit);
	last_decision->lit->var->status = free_var;
	last_decision->lit->level = 1;

	// delete node from list
	sat_state->decided_literals = sat_state->decided_literals->next;
	free(last_decision);

	// For each implied literal at the last decision level, unmark it, set var status to free, and set level of literal to 1
	// and remove node from list
	LitNode* lnode = sat_state->implied_literals;
	LitNode* lnode_next = lnode;

	while (lnode_next != NULL)
	{
		lnode_next = lnode_next->next;
		if (lnode->lit->level == last_level)
		{

			unmark_a_literal(sat_state, lnode->lit);
			lnode->lit->var->status = free_var;
			lnode->lit->level = 1;

			free(lnode);

		}
		lnode = lnode_next;
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
	return clause->subsuming_literal_count != 0;
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




//adds clause to the set of learned clauses, and runs unit resolution
//returns a learned clause if unit resolution finds a contradiction, NULL otherwise
//
//this function is called on a clause returned by sat_decide_literal() or sat_assert_clause()
//moreover, it should be called only if sat_at_assertion_level() succeeds
Clause* sat_assert_clause(Clause* clause, SatState* sat_state) {
	// Assume clause isn't empty
	assert(clause != NULL);

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
		return get_asserting_clause(sat_state);


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
			printf("Num Vars is %d \n", state->num_vars);
			state->num_orig_clauses = atoi(strtok(NULL, " \n\r"));
			printf("Num Original Clauses is %d \n", state->num_orig_clauses);

			printf("Creating Vars...");
			state->vars = (Var *)malloc((state->num_vars) * sizeof(Var));
			printf("Created Vars\n");

			printf("Filling in Literals...");
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
			printf("Filled in Literals\n");

			continue;
		}

		// Otherwise, create a clause
		Clause* clause = (Clause *)malloc(sizeof(Clause));
		initialize_Clause(clause);

		// Walk through it once first to count number of literals in clause
		// By counting the number of spaces in the line

		int num_lits = 0;
		for (int i = 0; line[i] != '\0'; i++)
		{
			if (line[i] == ' ')
				num_lits++;
		}
		// This is the same as the number of free literals
		clause->free_literal_count = num_lits;

		printf("\nThe number of literals in clause is %d \n", num_lits);

		// Walk through it again to point to the literals
		clause->num_lits = num_lits;
		clause->literals = (Lit **)malloc(num_lits*sizeof(Lit*));
		int i = 0;

		char* token = strtok(line, " ");

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

			// Put into clause
			clause->literals[i] = lit;

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
		for (int i = 0; i < num_lits; i++)
		{
			printf(" %d ", clause->literals[i]->index);
		}

		// Special case: if num_lits = 1, then unit clause. 
		// Add this to the implied literal list
		if (num_lits == 1)
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

		printf("Added clause to cnf\n");
	}

	printf("\n\nPrinting all clauses...\n");
	ClauseNode* cnf_ptr = state->cnf_head;
	while (cnf_ptr != NULL)
	{
		for (unsigned int i = 0; i < cnf_ptr->clause->num_lits; i++)
			printf(" %d ", cnf_ptr->clause->literals[i]->index);
		printf("\n");
		cnf_ptr = cnf_ptr->next;
	}

	printf("\nPrinting, for every variable, the clauses that mention it\n");
	for (unsigned int i = 0; i < state->num_vars; i++)
	{
		printf("Variable %d: ", i + 1);
		for (unsigned int j = 0; j < (state->vars[i].original_cnf_array).current; j++)
		{
			printf(" Clause %d, ", (state->vars[i].original_cnf_array).clause[j]->index);
		}
		printf("\n");
	}

	printf("\nPrinting, for every literal, the clauses that mention it\n");
	for (unsigned int i = 0; i < state->num_vars; i++)
	{
		printf("Variable %d: ", i + 1);
		printf("\n  Positive:\n");
		ClauseNode* cnode_ptr = state->vars[i].pos_lit->clauses;
		while (cnode_ptr != NULL)
		{
			printf("   Clause %d,", cnode_ptr->clause->index);
			cnode_ptr = cnode_ptr->next;
		}
		printf("\n  Negative:\n");
		cnode_ptr = state->vars[i].neg_lit->clauses;
		while (cnode_ptr != NULL)
		{
			printf("   Clause %d,", cnode_ptr->clause->index);
			cnode_ptr = cnode_ptr->next;
		}
		printf("\n");
	}

	printf("\nPrinting literals that are implied already...\n");
	LitNode* lnode = state->implied_literals;
	while (lnode != NULL)
	{
		printf(" %d ", lnode->lit->index);
		lnode = lnode->next;
	}
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
			printf("\nFreed Positive Literal %d's Clause", i+1);
			free(pos_lit_c);
			pos_lit_c = ptr;
		}
		ptr = neg_lit_c;
		while (ptr != NULL)
		{
			ptr = ptr->next;
			printf("\nFreed Negative Literal %d's Clause", i+1);
			free(neg_lit_c);
			neg_lit_c = ptr;
		}

		// For each var, delete original_cnf_array (delete the array in this vector)
		free((sat_state->vars[i].original_cnf_array).clause);
		printf("\nFreed variable %d", i + 1);

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
	if (head != NULL) {
		while (head->next != NULL)
			head = head->next;
		head->next = n;
		return tmp;
	}
	else { // just one
		return n;
	}
}


// return true if no conflict
// else return false and assign a clause to conflict reason
BOOLEAN mark_a_literal(SatState* sat_state, Lit* lit) {
	if (lit->index > 0) {
		lit->var->status = implied_pos;
	}
	else {
		lit->var->status = implied_neg;
	}

	ClauseNode* subsumed_head = lit->clauses;
	ClauseNode* resolved_head = flip_lit(lit)->clauses;
	// increament subsumed clauses
	while (subsumed_head != NULL) {
		subsumed_head->clause->subsuming_literal_count++;
		subsumed_head->clause->free_literal_count--;
		subsumed_head = subsumed_head->next;
	}
	// resolve
	while (resolved_head != NULL) {
		resolved_head->clause->free_literal_count--;
		if (resolved_head->clause->subsuming_literal_count == 0 &&
			resolved_head->clause->free_literal_count == 0) {//conflict
			sat_state->conflict_reason = resolved_head->clause;
			return false;
		}
		else if (resolved_head->clause->subsuming_literal_count == 0 &&
			resolved_head->clause->free_literal_count == 1){
			Lit* new_implied = get_free_literal_from_clause(resolved_head->clause);
			new_implied->level = lit->level;
			// set level
			// add the newly implied literal
			LitNode* lnode = (LitNode*)malloc(sizeof(LitNode));
			initialize_LitNode(lnode);
			lnode->lit = new_implied;
			sat_state->implied_literals = append(sat_state->implied_literals, lnode);
		}
		resolved_head = resolved_head->next;
	}
	return true;
}

void unmark_a_literal(SatState* sat_state, Lit* lit) {
	ClauseNode* subsumed_head = lit->clauses;
	ClauseNode* resolved_head = flip_lit(lit)->clauses;
	// increament subsumed clauses
	while (subsumed_head != NULL) {
		subsumed_head->clause->subsuming_literal_count--;
		subsumed_head->clause->free_literal_count++;
		subsumed_head = subsumed_head->next;
	}
	// resolve
	while (resolved_head != NULL) {
		resolved_head->clause->free_literal_count++;
		resolved_head = resolved_head->next;
	}
}

//applies unit resolution to the cnf of sat state
//returns 1 if unit resolution succeeds, 0 if it finds a contradiction
BOOLEAN sat_unit_resolution(SatState* sat_state) {
	if (sat_state->call_stat == first_call) {
		LitNode* tmp = sat_state->implied_literals;
		while (tmp != NULL) {
			if (!mark_a_literal(sat_state, tmp->lit)) {
				return 0;
			}
			tmp = tmp->next;
		}
	}
	else if (sat_state->call_stat == decide_call) { // mark on a decision
		LitNode* tmp = sat_state->implied_literals;
		if (tmp != NULL) {
			while (tmp->next != NULL)
				tmp = tmp->next;
		}
		if (mark_a_literal(sat_state, sat_state->decided_literals->lit))
			return 0;
		// if originally no implied
		if (tmp == NULL) {
			tmp = sat_state->implied_literals;
		}
		else {
			tmp = tmp->next;
		}
		while (tmp != NULL) {
			if (!mark_a_literal(sat_state, tmp->lit)) {
				return 0;
			}
			tmp = tmp->next;
		}
	}
	else if (sat_state->call_stat == learn_call) {

		Clause* c = sat_state->cnf_tail->clause;
		if (c->subsuming_literal_count != 0 && c->free_literal_count == 0){ // conflict
			sat_state->conflict_reason = c;
			return 0;
		}
		else if (c->subsuming_literal_count != 0 && c->free_literal_count == 1) { // new imply
			LitNode* tmp = sat_state->implied_literals;
			// tmp is now the tail;
			if (tmp != NULL) {
				while (tmp->next != NULL)
					tmp = tmp->next;
			}
			if (!mark_a_literal(sat_state, get_free_literal_from_clause(c))){
				return 0;
			}
			if (tmp == NULL) {
				tmp = sat_state->implied_literals;
			}
			else {
				tmp = tmp->next;
			}
			while (tmp != NULL) {
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
	unsigned long level = sat_state->assertion_level;
	LitNode* decided = sat_state->decided_literals;
	LitNode* implied = sat_state->implied_literals;
	while (decided != NULL && decided->lit->level <= level) {
		decided = decided->next;
	}
	while (implied != NULL && implied->lit->level <= level) {
		implied = implied->next;
	}
	while (decided != NULL) {

	}
	while (implied != NULL) {

	}
	// ... TO DO ...

	return; //dummy valued
}

//returns 1 if the decision level of the sat state equals to the assertion level of clause,
//0 otherwise
//
//this function is called after sat_decide_literal() or sat_assert_clause() returns clause.
//it is used to decide whether the sat state is at the right decision level for adding clause.
BOOLEAN sat_at_assertion_level(const Clause* clause, const SatState* sat_state) {

	// Assume clause isn't NULL and has more than 1 literal
	assert(clause != NULL && clause->num_lits > 0);

	c2dSize decision_level;
	if (sat_state->decided_literals == NULL)
		decision_level = 1;
	else
		decision_level = sat_state->decided_literals->lit->level;

	if (clause->num_lits == 1)
		return (1 == decision_level);

	c2dSize assertion_level = (clause->literals[0]->level);
	c2dSize highest_level = (clause->literals[0]->level);

	if (clause->literals[0]->level > clause->literals[1]->level)
		assertion_level = clause->literals[1]->level;
	else
		highest_level = clause->literals[1]->level;


	for (unsigned int i = 2; i < clause->num_lits; i++)
	{
		if (clause->literals[i]->level > highest_level)
		{
			assertion_level = highest_level;
			highest_level = clause->literals[i]->level;
		}
		else if (clause->literals[i]->level > assertion_level)
		{
			assertion_level = clause->literals[i]->level;
		}
	}

	return decision_level == assertion_level;
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
void initialize_Lit(Lit* l) {
	l->index = 1;
	l->level = 1;
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
		cv->limit *= 2;
		cv->clause = (Clause**)realloc(cv->clause, cv->limit*sizeof(Clause*));
		if (cv->clause == NULL)
		{
			printf("Was not able to add a new element in vector!!\n");
			exit(1);
		}

	}
	cv->clause[cv->current] = c;
	cv->current++;
}


void initialize_ClausePtrVector(ClausePtrVector* c) {
	c->clause = NULL;
	c->limit = 5;
	c->current = 0;
}

void initialize_Var(Var* v) {
	v->pos_lit = (Lit*)malloc(sizeof(Lit));
	v->neg_lit = (Lit*)malloc(sizeof(Lit));
	initialize_Lit(v->pos_lit);
	initialize_Lit(v->neg_lit);
	v->status = free_var;
	v->num_clause_has = 0;
	v->state = NULL;
	initialize_ClausePtrVector(&v->original_cnf_array);
}

void initialize_Clause(Clause * c) {
	c->literals = NULL;
	c->num_lits = 0;
	c->subsuming_literal_count = 0;
	c->free_literal_count = 0;
	c->watch1 = NULL;
	c->watch2 = NULL;
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
	s->call_stat = first_call;
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


unsigned long get_last_level(Clause* reason) {
	unsigned long last_level = 0;
	for (unsigned long i = 0; i < reason->num_lits; i++) {
		if (reason->literals[i]->level > last_level) {
			last_level = reason->literals[i]->level;
		}
	}
	return last_level;
}

Clause* make_clause_from_lit(LitNode* a, LitNode* b) {
	Clause* clause = (Clause *)malloc(sizeof(Clause));
	initialize_Clause(clause);
	unsigned int i = 1;
	LitNode* tmp = b;
	while (tmp != NULL) {
		i++;
		tmp = tmp->next;
	}
	clause->num_lits = i;
	clause->literals = (Lit **)malloc(clause->num_lits*sizeof(Lit*));
	clause->literals[0] = a->lit;
	i = 1;
	tmp = b;
	while (b != NULL) {
		clause->literals[i] = tmp->lit;
		tmp = tmp->next;
		i++;
	}
	return clause;
}


Clause* get_asserting_clause(SatState* sat_state) {

	LitNode* q_head = NULL; // Note this has been used w/o being initilized
	LitNode* q_tail = NULL; // Note this has been used w/o being initilized
	LitNode* l_head = NULL; // Note this has been used w/o being initilized
	LitNode* l_tail = NULL; // Note this has been used w/o being initilized
	Clause* conflict_reason = sat_state->conflict_reason;
	unsigned long last_level = get_last_level(conflict_reason);
	// initialize from conflict
	for (unsigned long i = 0; i < conflict_reason->num_lits; i++) {
		LitNode* node = &((LitNode) { NULL, flip_lit(conflict_reason->literals[i]) });
		if (conflict_reason->literals[i]->level == last_level) { // last level node added to queue
			if (!is_lit_duplicate(q_head, node->lit)) {
				q_tail = append_node_LitNode(q_tail, node);
				if (q_head == NULL) {
					q_head = q_tail;
				}
			}
		}
		else {
			if (!is_lit_duplicate(l_head, node->lit)) { // not last level node added to list
				l_tail = append_node_LitNode(l_tail, node);
				if (l_head == NULL) {
					l_head = l_tail;
				}
			}
		}
	}

	// Constructing queue and list
	// If more than one literal at last level
	while (q_head->next != NULL) {
		Lit* head_lit = q_head->lit;

		BOOLEAN is_implied;
		if (head_lit->index > 0)
			is_implied = (head_lit->var->status == implied_pos);
		else
			is_implied = (head_lit->var->status == implied_neg);
		if (head_lit->reason == NULL && is_implied) {
			// if duplicate just truncate head
			if (is_lit_duplicate(q_head->next, q_head->lit)) {
				q_head = q_head->next;
			}
			// move the head to tail
			LitNode* tmp_node = q_head;
			q_head = q_head->next;
			tmp_node->next = NULL;
			q_tail = append_node_LitNode(tmp_node, q_tail);
		}
		else { // implied
			// advance head
			q_head = q_head->next;
			// add literals in the reason to last_level queue and literal list
			Clause* reason = head_lit->reason;
			for (unsigned long i = 0; i < reason->num_lits; i++) {
				LitNode* node = &((LitNode) { NULL, flip_lit(reason->literals[i]) });
				if (reason->literals[i]->level == last_level) { // last level node added to queue
					if (!is_lit_duplicate(q_head, node->lit)) {
						q_tail = append_node_LitNode(q_tail, node);
						if (q_head == NULL) {
							q_head = q_tail;
						}
					}
				}
				else {
					if (!is_lit_duplicate(l_head, node->lit)) { // not last level node added to list
						l_tail = append_node_LitNode(l_tail, node);
						if (l_head == NULL) {
							l_head = l_tail;
						}
					}
				}
			}
		}
	}
	return make_clause_from_lit(q_head, l_head);
}



/******************************************************************************
* end
******************************************************************************/
