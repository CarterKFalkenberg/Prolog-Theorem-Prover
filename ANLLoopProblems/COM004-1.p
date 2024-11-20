%--------------------------------------------------------------------------
% File     : COM004-1 : TPTP v7.3.0. Released v1.1.0.
% Domain   : Computing Theory
% Problem  : Part of completeness of resolution
% Version  : Especial.
% English  : Part of [Bun83]'s proof of the completeness of resolution uses
%            the notion of failure nodes. This proves a special case when a
%            parent is the empty failure node.

% Refs     : [Bun83] Bundy (1983), The Computer Modelling of Mathematical R
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.3.0, 0.08 v5.2.0, 0.00 v3.3.0, 0.14 v3.1.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :    9 (   0 non-Horn;   8 unit;   6 RR)
%            Number of atoms       :   13 (   2 equality)
%            Maximal clause size   :    5 (   1 average)
%            Number of predicates  :    4 (   0 propositional; 2-2 arity)
%            Number of functors    :   10 (   5 constant; 0-2 arity)
%            Number of variables   :   10 (   1 singleton)
%            Maximal term depth    :    3 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_HRN

% Comments :
%--------------------------------------------------------------------------
cnf(make_node,axiom,
    ( failure_node(parent_of(X,Y),or(C,D))
    | ~ failure_node(X,or(C,P))
    | ~ failure_node(Y,or(D,Q))
    | ~ contradictory(P,Q)
    | ~ siblings(X,Y) )).

cnf(not_x_contradicts_x,axiom,
    ( contradictory(negate(X),X) )).

cnf(x_contradicts_not_x,axiom,
    ( contradictory(X,negate(X)) )).

cnf(n_left_and_n_right_are_siblings,axiom,
    ( siblings(left_child_of(X),right_child_of(X)) )).

%----Stuff for the theorem
cnf(n_left_is_atom,hypothesis,
    ( failure_node(n_left,or(empty,atom)) )).

cnf(n_right_is_not_atom,hypothesis,
    ( failure_node(n_right,or(empty,negate(atom))) )).

cnf(n_left_equals_left_child_of_n,hypothesis,
    ( n_left = left_child_of(n) )).

cnf(n_right_equals_right_child_of_n,hypothesis,
    ( n_right = right_child_of(n) )).

%----The goal to be proved.
cnf(goal_is_there_an_empty_node,negated_conjecture,
    ( ~ failure_node(Z,or(empty,empty)) )).

%--------------------------------------------------------------------------

