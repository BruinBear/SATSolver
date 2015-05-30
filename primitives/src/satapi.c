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

/******************************************************************************
 * Variables
 ******************************************************************************/

//returns a variable structure for the corresponding index
Var* sat_index2var(c2dSize index, const SatState* sat_state) {
   return &(sat_state->vars[index - 1];
  
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
  return (((var->pos_lit)->status) != free);
}

//returns 1 if all the clauses mentioning the variable are subsumed, 0 otherwise
BOOLEAN sat_irrelevant_var(const Var* var) {
  ClauseNode* pos_head = var->pos_lit.clauses;
  ClauseNode* neg_head = var->neg_lit.clauses;
  while(pos_head != NULL) {
    if(pos_head->clause->subsuming_literal_count != 0)
      return 0;
    pos_head = pos_head->next;
  }
    while(neg_head != NULL) {
    if(neg_head->clause->subsuming_literal_count != 0)
      return 0;
    neg_head = neg_head->next;
  }
  return 1;
}

//returns the number of variables in the cnf of sat state
c2dSize sat_var_count(const SatState* sat_state) {
   return sat_state->num_vars;
}

//returns the number of clauses mentioning a variable
//a variable is mentioned by a clause if one of its literals appears in the clause
c2dSize sat_var_occurences(const Var* var) {

  // ... TO DO ..
  
  return 0; //dummy valued
}

//returns the index^th clause that mentions a variable
//index starts from 0, and is less than the number of clauses mentioning the variable
//this cannot be called on a variable that is not mentioned by any clause
Clause* sat_clause_of_var(c2dSize index, const Var* var) {

  // ... TO DO ..
  
  return NULL; //dummy valued
}

/******************************************************************************
 * Literals 
 ******************************************************************************/

//returns a literal structure for the corresponding index
Lit* sat_index2literal(c2dLiteral index, const SatState* sat_state) {
  if (index > 0)
      return &((sat_state->vars[index - 1])->pos_lit);
  return &((sat_state->vars[-1*index - 1])->neg_lit);
}

//returns the index of a literal
c2dLiteral sat_literal_index(const Lit* lit) {
   return lit->index;
}

//returns the positive literal of a variable
Lit* sat_pos_literal(const Var* var) {
   return &(var->pos_lit);
}

//returns the negative literal of a variable
Lit* sat_neg_literal(const Var* var) {
   return &(var->neg_lit);
}

//returns 1 if the literal is implied, 0 otherwise
//a literal is implied by deciding its variable, or by inference using unit resolution
BOOLEAN sat_implied_literal(const Lit* lit) {
   return (lit->status == implied);
}

//sets the literal to true, and then runs unit resolution
//returns a learned clause if unit resolution detected a contradiction, NULL otherwise
//
//if the current decision level is L in the beginning of the call, it should be updated 
//to L+1 so that the decision level of lit and all other literals implied by unit resolution is L+1
Clause* sat_decide_literal(Lit* lit, SatState* sat_state) {
   if (sat_state->decided_literals == NULL)
      lit->level = 2;
   else
      lit->level = ((sat_state->decided_literals)->lit)->level;
   add_lit_h(&(sat_state->decided_literals), lit);
   if (sat_unit_resolution(sat_state))
     return NULL; // Unit resol succeeded
   return get_asserting(sat_state);
}

//undoes the last literal decision and the corresponding implications obtained by unit resolution
//
//if the current decision level is L in the beginning of the call, it should be updated 
//to L-1 before the call ends
void sat_undo_decide_literal(SatState* sat_state) {

  // ... TO DO ...
  
  return; //dummy valued
}

/******************************************************************************
 * Clauses 
 ******************************************************************************/

//returns a clause structure for the corresponding index
Clause* sat_index2clause(c2dSize index, const SatState* sat_state) {

  // ... TO DO ...
  
  return NULL; //dummy valued
}

//returns the index of a clause
c2dSize sat_clause_index(const Clause* clause) {

  // ... TO DO ...
  
  return 0; //dummy valued
}

//returns the literals of a clause
Lit** sat_clause_literals(const Clause* clause) {

  // ... TO DO ...
  
  return NULL; //dummy valued
}

//returns the number of literals in a clause
c2dSize sat_clause_size(const Clause* clause) {

  // ... TO DO ...
  
  return 0; //dummy valued
}

//returns 1 if the clause is subsumed, 0 otherwise
BOOLEAN sat_subsumed_clause(const Clause* clause) {

  // ... TO DO ...
  
  return 0; //dummy valued
}

//returns the number of clauses in the cnf of sat state
c2dSize sat_clause_count(const SatState* sat_state) {

  // ... TO DO ...
  
  return 0; //dummy valued
}

//returns the number of learned clauses in a sat state (0 when the sat state is constructed)
c2dSize sat_learned_clause_count(const SatState* sat_state) {

  // ... TO DO ...
  
  return 0; //dummy valued
}




//adds clause to the set of learned clauses, and runs unit resolution
//returns a learned clause if unit resolution finds a contradiction, NULL otherwise
//
//this function is called on a clause returned by sat_decide_literal() or sat_assert_clause()
//moreover, it should be called only if sat_at_assertion_level() succeeds
Clause* sat_assert_clause(Clause* clause, SatState* sat_state) {

  // ... TO DO ...
  
  return NULL; //dummy valued
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

//constructs a SatState from an input cnf file
SatState* sat_state_new(const char* file_name) {

  // ... TO DO ...
  
  return NULL; //dummy valued
}

//frees the SatState
void sat_state_free(SatState* sat_state) {

  // ... TO DO ...
  
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

//applies unit resolution to the cnf of sat state
//returns 1 if unit resolution succeeds, 0 if it finds a contradiction
BOOLEAN sat_unit_resolution(SatState* sat_state) {

  // ... TO DO ...
  
  return 0; //dummy valued
}

//undoes sat_unit_resolution(), leading to un-instantiating variables that have been instantiated
//after sat_unit_resolution()
void sat_undo_unit_resolution(SatState* sat_state) {

  // ... TO DO ...
  
  return; //dummy valued
}

//returns 1 if the decision level of the sat state equals to the assertion level of clause,
//0 otherwise
//
//this function is called after sat_decide_literal() or sat_assert_clause() returns clause.
//it is used to decide whether the sat state is at the right decision level for adding clause.
BOOLEAN sat_at_assertion_level(const Clause* clause, const SatState* sat_state) {

  // ... TO DO ...
  
  return 0; //dummy valued
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
Lit* flip_lit(Lit* lit) {
  if(lit->index > 0) {
    return sat_neg_literal(lit->var);
  } else {
    return sat_pos_literal(lit->var);
  }
}

BOOLEAN is_lit_duplicate(LitNode* head, Lit* lit) {
  while(head!=NULL) {
    if(head->lit == lit) {
      return true;
    } 
    head = head->next;
  }
  return false;
}

LitNode* append_node(LitNode* node, LitNode* tail) {
  if(tail != NULL) {
    tail->next = node;
  }
  return node;
}

unsigned long get_last_level(Clause* reason) {
  unsigned long last_level = 0;
  for(unsigned long i = 0; i < reason->lit_size; i++) {
    if(reason->literals[i]->level > last_level) {
      last_level = reason->literals[i]->level;
    }
  }
  return last_level;
}


Clause* make_clause_from_lit(LitNode* a, LitNode* b) {

}


Clause* get_asserting_clause(Sat_State* sat_state) {
                                
  LitNode* q_head;
  LitNode* q_tail;
  LitNode* l_head;
  LitNode* l_tail;
  Clause* conflict_reason = sat_state->conflict_reason;
  unsigned long last_level = get_last_level(conflict_reason);
  // initialize from conflict
  for(unsigned long i = 0; i < conflict_reason->lit_size; i++) {
    LitNode* node = &((LitNode) {NULL, flip_lit(conflict_reason->literals[i])});
    if(conflict_reason->literals[i]->level == last_level) { // last level node added to queue
      if(!is_lit_duplicate(q_head, node)) {
        q_tail = append_node(q_tail, node);
        if(q_head == NULL) {
          q_head = q_tail;
        }
      }
    } else {
      if(!is_lit_duplicate(l_head, node)) { // not last level node added to list
        l_tail = append_node(l_tail, node);
        if(l_head == NULL) {
          l_head = l_tail;
        }
      }
    }
  }

  // Constructing queue and list
  // If more than one literal at last level
  while(q_head->next != NULL) {
    Lit* head_lit = q_head->lit;

    if(head_lit->reason == NULL && head_lit->status == implied) {
      // if duplicate just truncate head
      if(is_lit_duplicate(q_head->next, q_head->lit)) {
        q_head = q_head->next;
      }
      // move the head to tail
      LitNode* tmp_node = q_head;
      q_head = q_head->next;
      tmp_node->next = NULL;
      q_tail = append_node(tmp_node, q_tail);
    } else { // implied
      // advance head
      q_head = q_head->next;
      // add literals in the reason to last_level queue and literal list
      Clause* reason = head_lit->reason;
      for(unsigned long i = 0; i < reason->lit_size; i++) {
        LitNode* node = &((LitNode) {NULL, flip_lit(reason->literals[i])});
        if(reason->literals[i]->level == last_level) { // last level node added to queue
          if(!is_lit_duplicate(q_head, node)) {
            q_tail = append_node(q_tail, node);
            if(q_head == NULL) {
              q_head = q_tail;
            }
          }
        } else {
          if(!is_lit_duplicate(l_head, node)) { // not last level node added to list
            l_tail = append_node(l_tail, node);
            if(l_head == NULL) {
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
