#ifndef SATAPI_H_
#define SATAPI_H_

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

/******************************************************************************
 * sat_api.h shows the function prototypes you should implement to create libsat.a
 *
 * To use the sat library, a sat state should be constructed from an input cnf file
 *
 * The sat state supports functions that are usually used to implement a sat solver,
 * such as deciding variables and learning clauses. It also supports functions for
 * obtaining stats about the input cnf, such as the number of variables and clauses.
 *
 * The functions supported by a sat state are sufficient to implement a modern sat
 * solver (also known as CDC solver).
 *
 * A sat state has a "decision level", which is incremented when a literal is
 * decided, and decremented when a literal is undecided. Hence, each decided
 * literal is associated with a decision level. Similarly, literals which are implied
 * by unit resolution are also associated with a decision level.
 *
 * A learned clause is associated with an "assertion level". The clause can be 
 * asserted (added) to a state state only when the decision level of the sat 
 * state equals to the clause's assertion level.
 ******************************************************************************/

/******************************************************************************
* typedefs
******************************************************************************/

typedef char BOOLEAN; //signed

typedef unsigned long c2dSize;  //for variables, clauses, and various things
typedef signed long c2dLiteral; //for literals
typedef double c2dWmc;          //for (weighted) model count


/****************************************/
/** Our own defines **/

#define true 1
#define false 0

#define free 0
#define implied_pos 1 // the positive literal of the variable is implied
// by decision or unit res
#define implied_neg 2
#define conflicting 3 // Both implied_pos and implied_neg


#define first_call 1
#define decide_call 2
#define learn_call 3

typedef char litstat;
typedef char callstat;


/****************************************/

/******************************************************************************
* Basic structures
******************************************************************************/



typedef struct literal Lit;
typedef struct var Var;
typedef struct clause Clause;
typedef struct sat_state_t SatState;
typedef struct ClauseNode ClauseNode;
typedef struct LitNode LitNode;
typedef struct ClausePtrVector ClausePtrVector;


/******************************************************************************
* Literals:
* --You must represent literals using the following struct
* --Positive literals' indices range from 1 to n (n is the number of cnf variables)
* --Negative literals' indices range from -n to -1 (n is the number of cnf variables)
* --Index of a literal must be of type "c2dLiteral"
******************************************************************************/

struct literal {
	c2dLiteral index;
	unsigned long level = 1;
	ClauseNode* clauses = NULL;
	ClauseNode* clauses_tail = NULL;
	Var* var = NULL;
	Clause* reason = NULL; // the reason why literal was implied
	// NULL if literal is free or decided

};

void initialize(Lit* l) { 
	l->level = 1; 
	l->clauses = NULL; 
	l->clauses_tail = NULL;
	l->var = NULL; 
	l->reason = NULL; 
}

struct LitNode {
	LitNode* next = NULL;
	Lit* lit = NULL;
};
void initialize(LitNode* l) { l->lit = NULL; l->next = NULL; }

/******************************************************************************
* Variables:
* --You must represent variables using the following struct
* --Variable index must start at 1, and is no greater than the number of cnf variables
* --Index of a variable must be of type "c2dSize"
* --The field "mark" below and its related functions should not be changed
******************************************************************************/

struct ClausePtrVector
{
	Clause** clause = NULL;
	size_t limit = 5; // Total size of the vector
	size_t current = 0; //Number of vectors in it at present
	void add(Clause* c)
	{
		if (clause == NULL)
		{
			clause = (Clause**)malloc(limit*sizeof(Clause*));
		}
		else if (current == limit)
		{
			limit *= 2;
			clause = (Clause**)realloc(clause, limit*sizeof(Clause*));
			if (clause == NULL)
			{
				printf("Was not able to add a new element in vector!!\n");
				exit(1);
			}

		}
		clause[current] = c;
		current++;
	}
};


void initialize(ClausePtrVector* c) {
	c->clause = NULL;
	c->limit = 5;
	c->current = 0;
}

struct var {

	c2dSize index;

	Lit* pos_lit = NULL;
	Lit* neg_lit = NULL;
	BOOLEAN mark; //THIS FIELD MUST STAY AS IS

	litstat status = free; // free, implied_pos or implied_neg (by decision/unit resolution), 

	// TODO:
	// number of clauses which contains this var in original CNF
	// either literal of var counts, so take absolute value
	c2dSize num_clause_has  = 0;
	ClausePtrVector original_cnf_array;

	// Maybe we need this?
	SatState* state = NULL;

	
};

void initialize(Var* v) {
	v->pos_lit = (Lit*)malloc(sizeof(Lit));
	v->neg_lit = (Lit*)malloc(sizeof(Lit));
		initialize(v->pos_lit);
		initialize(v->neg_lit);
		v->status = free;
		v->num_clause_has = 0;
		v->state = NULL;
		initialize(&v->original_cnf_array);
	}
/******************************************************************************
* Clauses:
* --You must represent clauses using the following struct
* --Clause index must start at 1, and is no greater than the number of cnf clauses
* --Index of a clause must be of type "c2dSize"
* --A clause must have an array consisting of its literals
* --The index of literal array must start at 0, and is less than the clause size
* --The field "mark" below and its related functions should not be changed
******************************************************************************/

struct clause {
	c2dSize index;
	Lit** literals = NULL;
	c2dSize num_lits = 0;
	BOOLEAN mark; //THIS FIELD MUST STAY AS IS

	// the number of fixed literals that make this clause subsumed
	// 0 when not subsumed.
	unsigned long subsuming_literal_count = 0;
	 unsigned long free_literal_count = 0; 

	Lit* watch1 = NULL;
	Lit* watch2 = NULL;
};

void initialize(Clause * c) {
		c->literals = NULL;
		c->num_lits = 0;
		c->subsuming_literal_count = 0;
    		c->free_literal_count = 0;
		c->watch1 = NULL;
		c->watch2 = NULL;
}

struct ClauseNode {
	ClauseNode* next = NULL;
	Clause* clause = NULL;
};

void initialize(ClauseNode* c) {
	c->next = NULL;
	c->clause = NULL;
}


/******************************************************************************
* SatState:
* --The following structure will keep track of the data needed to
* condition/uncondition variables, perform unit resolution, and so on ...
******************************************************************************/

struct sat_state_t {
	Var* vars = NULL;
	c2dSize num_vars = 0;

	ClauseNode* cnf_head = NULL;
	ClauseNode* cnf_tail = NULL;
	c2dSize num_orig_clauses = 0;
	c2dSize num_asserted_clauses = 0;

	c2dSize assertion_level = 1;

	LitNode* decided_literals = NULL; // stack. The head literal is at
	// the highest decision level
	Clause* conflict_reason = NULL;
	LitNode* implied_literals = NULL; // stack.
  callstat call_stat = first_call;
};

void initialize(SatState* s) {
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

LitNode* append_node(LitNode* node, LitNode* tail) {
			 if (tail != NULL) {
				 tail->next = node;
			 }
			 return node;
}

ClauseNode* append_node(ClauseNode* node, ClauseNode* tail) {
	if (tail != NULL) {
		tail->next = node;
	}
	return node;
}

/******************************************************************************
 * API: 
 * --Using the above structures you must implement the following functions 
 * --Incomplete implementations of the functions can be found in sat_api.c
 * --These functions are all you need for the knowledge compiler
 * --You must implement each function below
 * --Note that most of the functions can be implemented in 1 line or so
 ******************************************************************************/

/******************************************************************************
 * function prototypes 
 ******************************************************************************/

/******************************************************************************
 * Variables
 ******************************************************************************/

//returns a variable structure for the corresponding index
Var* sat_index2var(c2dSize index, const SatState* sat_state);

//returns the index of a variable
c2dSize sat_var_index(const Var* var);

//returns the variable of a literal
Var* sat_literal_var(const Lit* lit);

//returns 1 if the variable is instantiated, 0 otherwise
//a variable is instantiated either by decision or implication (by unit resolution)
BOOLEAN sat_instantiated_var(const Var* var);

//returns 1 if all the clauses mentioning the variable are subsumed, 0 otherwise
BOOLEAN sat_irrelevant_var(const Var* var);

//returns the number of variables in the cnf of sat state
c2dSize sat_var_count(const SatState* sat_state);

//returns the number of clauses mentioning a variable
//a variable is mentioned by a clause if one of its literals appears in the clause
c2dSize sat_var_occurences(const Var* var);

//returns the index^th clause that mentions a variable
//index starts from 0, and is less than the number of clauses mentioning the variable
//this cannot be called on a variable that is not mentioned by any clause
Clause* sat_clause_of_var(c2dSize index, const Var* var);

/******************************************************************************
 * Literals 
 ******************************************************************************/

//returns a literal structure for the corresponding index
Lit* sat_index2literal(c2dLiteral index, const SatState* sat_state);

//returns the index of a literal
c2dLiteral sat_literal_index(const Lit* lit);

//returns the positive literal of a variable
Lit* sat_pos_literal(const Var* var);

//returns the negative literal of a variable
Lit* sat_neg_literal(const Var* var);

//returns 1 if the literal is implied, 0 otherwise
//a literal is implied by deciding its variable, or by inference using unit resolution
BOOLEAN sat_implied_literal(const Lit* lit);


//sets the literal to true, and then runs unit resolution
//returns a learned clause if unit resolution detected a contradiction, NULL otherwise
Clause* sat_decide_literal(Lit* lit, SatState* sat_state);

//undoes the last literal decision and the corresponding implications obtained by unit resolution
void sat_undo_decide_literal(SatState* sat_state);

/******************************************************************************
 * Clauses 
 ******************************************************************************/

//returns a clause structure for the corresponding index
Clause* sat_index2clause(c2dSize index, const SatState* sat_state);

//returns the index of a clause
c2dSize sat_clause_index(const Clause* clause);

//returns the literals of a clause
Lit** sat_clause_literals(const Clause* clause);

//returns the number of literals in a clause
c2dSize sat_clause_size(const Clause* clause);

//returns 1 if the clause is subsumed, 0 otherwise
BOOLEAN sat_subsumed_clause(const Clause* clause);

//returns the number of clauses in the cnf of sat state
c2dSize sat_clause_count(const SatState* sat_state);

//returns the number of learned clauses in a sat state (0 when the sat state is constructed)
c2dSize sat_learned_clause_count(const SatState* sat_state);

//adds clause to the set of learned clauses, and runs unit resolution
//returns a learned clause if unit resolution finds a contradiction, NULL otherwise
//
//this function is called on a clause returned by sat_decide_literal() or sat_assert_clause()
//moreover, it should be called only if sat_at_assertion_level() succeeds
Clause* sat_assert_clause(Clause* clause, SatState* sat_state);

/******************************************************************************
 * SatState
 ******************************************************************************/

//constructs a SatState from an input cnf file
SatState* sat_state_new(const char* file_name);

//frees the SatState
void sat_state_free(SatState* sat_state);

//applies unit resolution to the cnf of sat state
//returns 1 if unit resolution succeeds, 0 if it finds a contradiction
BOOLEAN sat_unit_resolution(SatState* sat_state);

//undoes sat_unit_resolution(), leading to un-instantiating variables that have been instantiated
//after sat_unit_resolution()
void sat_undo_unit_resolution(SatState* sat_state);

//returns 1 if the decision level of the sat state equals to the assertion level of clause,
//0 otherwise
//
//this function is called after sat_decide_literal() or sat_assert_clause() returns clause.
//it is used to decide whether the sat state is at the right decision level for adding clause.
BOOLEAN sat_at_assertion_level(const Clause* clause, const SatState* sat_state);

/******************************************************************************
 * The functions below are already implemented for you and MUST STAY AS IS
 ******************************************************************************/

//returns the weight of a literal (which is simply 1 for our purposes)
c2dWmc sat_literal_weight(const Lit* lit);

//returns 1 if a variable is marked, 0 otherwise
BOOLEAN sat_marked_var(const Var* var);

//marks a variable (which is not marked already)
void sat_mark_var(Var* var);

//unmarks a variable (which is marked already)
void sat_unmark_var(Var* var);

//returns 1 if a clause is marked, 0 otherwise
BOOLEAN sat_marked_clause(const Clause* clause);

//marks a clause (which is not marked already)
void sat_mark_clause(Clause* clause);

//unmarks a clause (which is marked already)
void sat_unmark_clause(Clause* clause);


/*******************************/
/**  Extra helping functions  **/
/*******************************/

// Add toBeAdded in front of head
void add_lit_h(LitNode** head, Lit* toBeAdded);
Clause* get_asserting_clause(SatState* sat_state);





#endif //SATAPI_H_

/******************************************************************************
 * end
 ******************************************************************************/

