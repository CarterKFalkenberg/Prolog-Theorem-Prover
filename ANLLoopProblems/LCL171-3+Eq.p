%--------------------------------------------------------------------------
% File     : LCL171-3 : TPTP v7.3.0. Released v2.3.0.
% Domain   : Logic Calculi (Propositional)
% Problem  : Principia Mathematica 2.03
% Version  : [WR27] axioms.
% English  :

% Refs     : [WR27]  Whitehead & Russell (1927), Principia Mathematica
% Source   : [WR27]
% Names    : Problem 2.03 [WR27]

% Status   : Unsatisfiable
% Rating   : 0.00 v5.3.0, 0.08 v5.2.0, 0.00 v2.3.0
% Syntax   : Number of clauses     :    9 (   0 non-Horn;   7 unit;   3 RR)
%            Number of atoms       :   12 (   1 equality)
%            Maximal clause size   :    3 (   1 average)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    5 (   2 constant; 0-2 arity)
%            Number of variables   :   16 (   1 singleton)
%            Maximal term depth    :    4 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_HRN

% Comments :
%--------------------------------------------------------------------------
%----Include axioms of propositional logic
%------------------------------------------------------------------------------
cnf(reflexivity,axiom,
    ( A = A )).

cnf(symmetry,axiom,
    ( A != B | B = A )).

cnf(transitivity,axiom,
    ( A != B | B != C | A = C )).

cnf(implies_substitution_1,axiom,
    ( A != B | implies(A,C) = implies(B,C) )).

cnf(implies_substitution_2,axiom,
    ( A != B | implies(C,A) = implies(C,B) )).

cnf(not_substitution_1,axiom,
    ( A != B | not(A) = not(B) )).

cnf(or_substitution_1,axiom,
    ( A != B | or(A,C) = or(B,C) )).

cnf(or_substitution_2,axiom,
    ( A != B | or(C,A) = or(C,B) )).

cnf(axiom_substitution_1,axiom,
    ( A != B | ~ axiom(A) | axiom(B) )).

cnf(theorem_substitution_1,axiom,
    ( A != B | ~ theorem(A) | theorem(B) )).
    
cnf(axiom_1_2,axiom,
    ( axiom(implies(or(A,A),A)) )).

cnf(axiom_1_3,axiom,
    ( axiom(implies(A,or(B,A))) )).

cnf(axiom_1_4,axiom,
    ( axiom(implies(or(A,B),or(B,A))) )).

cnf(axiom_1_5,axiom,
    ( axiom(implies(or(A,or(B,C)),or(B,or(A,C)))) )).

cnf(axiom_1_6,axiom,
    ( axiom(implies(implies(A,B),implies(or(C,A),or(C,B)))) )).

cnf(implies_definition,axiom,
    ( implies(X,Y) = or(not(X),Y) )).

cnf(rule_1,axiom,
    ( theorem(X)
    | ~ axiom(X) )).

cnf(rule_2,axiom,
    ( theorem(X)
    | ~ theorem(implies(Y,X))
    | ~ theorem(Y) )).

% input_clause(rule_3,axiom,
%     [++theorem(implies(X,Z)),
%      --theorem(implies(X,Y)),
%      --theorem(implies(Y,Z))]).
%------------------------------------------------------------------------------
%--------------------------------------------------------------------------
cnf(prove_this,negated_conjecture,
    ( ~ theorem(implies(implies(p,not(q)),implies(q,not(p)))) )).

%--------------------------------------------------------------------------
