%--------------------------------------------------------------------------
% File     : KRS005-1 : TPTP v7.3.0. Released v2.0.0.
% Domain   : Knowledge Representation
% Problem  : Paramasivam problem T-Box 2a
% Version  : Especial.
% English  : Inconsistent concept definition; e exists.

% Refs     : [PP95]  Paramasivam & Plaisted (1995), Automated Deduction Tec
% Source   : [PP95]
% Names    : Problem 2(a) [PP95]

% Status   : Satisfiable
% Rating   : 0.00 v3.1.0, 0.14 v2.7.0, 0.00 v2.2.1, 0.25 v2.2.0, 0.33 v2.1.0
% Syntax   : Number of clauses     :    8 (   2 non-Horn;   1 unit;   8 RR)
%            Number of atoms       :   24 (   0 equality)
%            Maximal clause size   :    6 (   3 average)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    5 (   1 constant; 0-2 arity)
%            Number of variables   :   14 (   0 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_SAT_RFO_NEQ

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    ( e(exist) )).

cnf(clause_2,axiom,
    ( equalish(X5,u0r4(X1))
    | ~ e(X1)
    | ~ r(X1,X5) )).

cnf(clause_3,axiom,
    ( r(X1,u0r4(X1))
    | ~ e(X1) )).

cnf(clause_4,axiom,
    ( ~ e(X1)
    | ~ equalish(u0r3(X1),u0r2(X1)) )).

cnf(clause_5,axiom,
    ( r(X1,u0r2(X1))
    | ~ e(X1) )).

cnf(clause_6,axiom,
    ( r(X1,u0r3(X1))
    | ~ e(X1) )).

cnf(clause_7,axiom,
    ( e(X1)
    | equalish(X3,X2)
    | ~ r(X1,X3)
    | ~ r(X1,X2)
    | ~ r(X1,X4)
    | ~ equalish(u0r1(X4,X1),X4) )).

cnf(clause_8,axiom,
    ( e(X1)
    | equalish(X3,X2)
    | r(X1,u0r1(X4,X1))
    | ~ r(X1,X3)
    | ~ r(X1,X2)
    | ~ r(X1,X4) )).

%--------------------------------------------------------------------------
