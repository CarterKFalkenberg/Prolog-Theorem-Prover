%--------------------------------------------------------------------------
% File     : FLD001-3 : TPTP v7.3.0. Bugfixed v2.1.0.
% Domain   : Field Theory (Ordered fields)
% Problem  : Transformation additive relation --> multiplicative relation
% Version  : [Dra93] axioms : Especial.
%            Theorem formulation : Functional with re axiom set.
% English  :

% Refs     : [Dra93] Draeger (1993), Anwendung des Theorembeweisers SETHEO
% Source   : [Dra93]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.5.0, 0.12 v5.4.0, 0.10 v5.2.0, 0.00 v5.0.0, 0.07 v4.1.0, 0.00 v4.0.1, 0.20 v4.0.0, 0.14 v3.4.0, 0.25 v3.3.0, 0.33 v3.1.0, 0.17 v2.7.0, 0.00 v2.6.0, 0.33 v2.5.0, 0.00 v2.4.0, 0.20 v2.3.0, 0.00 v2.2.1, 0.67 v2.1.0
% Syntax   : Number of clauses     :   30 (   3 non-Horn;   7 unit;  30 RR)
%            Number of atoms       :   81 (   0 equality)
%            Maximal clause size   :    5 (   3 average)
%            Number of predicates  :    4 (   0 propositional; 1-3 arity)
%            Number of functors    :    8 (   4 constant; 0-2 arity)
%            Number of variables   :   73 (   0 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
% Bugfixes : v2.1.0 - Bugfix in FLD002-0.ax
%--------------------------------------------------------------------------
%--------------------------------------------------------------------------
cnf(associativity_addition_1,axiom,
    ( sum(X,V,W)
    | ~ sum(X,Y,U)
    | ~ sum(Y,Z,V)
    | ~ sum(U,Z,W) )).

cnf(associativity_addition_2,axiom,
    ( sum(U,Z,W)
    | ~ sum(X,Y,U)
    | ~ sum(Y,Z,V)
    | ~ sum(X,V,W) )).

cnf(existence_of_identity_addition,axiom,
    ( sum(additive_identity,X,X)
    | ~ defined(X) )).

cnf(existence_of_inverse_addition,axiom,
    ( sum(additive_inverse(X),X,additive_identity)
    | ~ defined(X) )).

cnf(commutativity_addition,axiom,
    ( sum(Y,X,Z)
    | ~ sum(X,Y,Z) )).

cnf(associativity_multiplication_1,axiom,
    ( product(X,V,W)
    | ~ product(X,Y,U)
    | ~ product(Y,Z,V)
    | ~ product(U,Z,W) )).

cnf(associativity_multiplication_2,axiom,
    ( product(U,Z,W)
    | ~ product(X,Y,U)
    | ~ product(Y,Z,V)
    | ~ product(X,V,W) )).

cnf(existence_of_identity_multiplication,axiom,
    ( product(multiplicative_identity,X,X)
    | ~ defined(X) )).

cnf(existence_of_inverse_multiplication,axiom,
    ( product(multiplicative_inverse(X),X,multiplicative_identity)
    | sum(additive_identity,X,additive_identity)
    | ~ defined(X) )).

cnf(commutativity_multiplication,axiom,
    ( product(Y,X,Z)
    | ~ product(X,Y,Z) )).

cnf(distributivity_1,axiom,
    ( sum(C,D,B)
    | ~ sum(X,Y,A)
    | ~ product(A,Z,B)
    | ~ product(X,Z,C)
    | ~ product(Y,Z,D) )).

cnf(distributivity_2,axiom,
    ( product(A,Z,B)
    | ~ sum(X,Y,A)
    | ~ product(X,Z,C)
    | ~ product(Y,Z,D)
    | ~ sum(C,D,B) )).

cnf(well_definedness_of_addition,axiom,
    ( defined(add(X,Y))
    | ~ defined(X)
    | ~ defined(Y) )).

cnf(well_definedness_of_additive_identity,axiom,
    ( defined(additive_identity) )).

cnf(well_definedness_of_additive_inverse,axiom,
    ( defined(additive_inverse(X))
    | ~ defined(X) )).

cnf(well_definedness_of_multiplication,axiom,
    ( defined(multiply(X,Y))
    | ~ defined(X)
    | ~ defined(Y) )).

cnf(well_definedness_of_multiplicative_identity,axiom,
    ( defined(multiplicative_identity) )).

cnf(well_definedness_of_multiplicative_inverse,axiom,
    ( defined(multiplicative_inverse(X))
    | ~ defined(X)
    | sum(additive_identity,X,additive_identity) )).

cnf(totality_of_addition,axiom,
    ( sum(X,Y,add(X,Y))
    | ~ defined(X)
    | ~ defined(Y) )).

cnf(totality_of_multiplication,axiom,
    ( product(X,Y,multiply(X,Y))
    | ~ defined(X)
    | ~ defined(Y) )).

cnf(antisymmetry_of_order_relation,axiom,
    ( sum(additive_identity,X,Y)
    | ~ less_or_equal(X,Y)
    | ~ less_or_equal(Y,X) )).

cnf(transitivity_of_order_relation,axiom,
    ( less_or_equal(X,Z)
    | ~ less_or_equal(X,Y)
    | ~ less_or_equal(Y,Z) )).

cnf(totality_of_order_relation,axiom,
    ( less_or_equal(X,Y)
    | less_or_equal(Y,X)
    | ~ defined(X)
    | ~ defined(Y) )).

cnf(compatibility_of_order_relation_and_addition,axiom,
    ( less_or_equal(U,V)
    | ~ less_or_equal(X,Y)
    | ~ sum(X,Z,U)
    | ~ sum(Y,Z,V) )).

cnf(compatibility_of_order_relation_and_multiplication,axiom,
    ( less_or_equal(additive_identity,Z)
    | ~ less_or_equal(additive_identity,X)
    | ~ less_or_equal(additive_identity,Y)
    | ~ product(X,Y,Z) )).

cnf(different_identities,axiom,
    ( ~ sum(additive_identity,additive_identity,multiplicative_identity) )).

%--------------------------------------------------------------------------
%--------------------------------------------------------------------------
cnf(a_is_defined,hypothesis,
    ( defined(a) )).

cnf(b_is_defined,hypothesis,
    ( defined(b) )).

cnf(sum_3,hypothesis,
    ( sum(additive_identity,a,b) )).

cnf(not_product_4,negated_conjecture,
    ( ~ product(multiplicative_identity,a,b) )).

%--------------------------------------------------------------------------
