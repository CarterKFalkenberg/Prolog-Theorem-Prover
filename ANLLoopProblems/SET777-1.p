%--------------------------------------------------------------------------
% File     : SET777-1 : TPTP v7.3.0. Released v2.5.0.
% Domain   : Set Theory
% Problem  : Set theory membership and subsets axioms
% Version  : [LS74] axioms.
% English  :

% Refs     : [LS74]  Lawrence & Starkey (1974), Experimental tests of resol
% Source   : [SPRFN]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v3.1.0, 0.14 v2.7.0, 0.00 v2.5.0
% Syntax   : Number of clauses     :    6 (   1 non-Horn;   0 unit;   5 RR)
%            Number of atoms       :   14 (   0 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    3 (   0 propositional; 2-2 arity)
%            Number of functors    :    1 (   0 constant; 2-2 arity)
%            Number of variables   :   13 (   0 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_SAT_RFO_NEQ

% Comments :
%--------------------------------------------------------------------------
%----Include Set theory membership and subsets axioms
%--------------------------------------------------------------------------
cnf(membership_in_subsets,axiom,
    ( ~ member(Element,Subset)
    | ~ subset(Subset,Superset)
    | member(Element,Superset) )).

cnf(subsets_axiom1,axiom,
    ( subset(Subset,Superset)
    | member(member_of_1_not_of_2(Subset,Superset),Subset) )).

cnf(subsets_axiom2,axiom,
    ( ~ member(member_of_1_not_of_2(Subset,Superset),Superset)
    | subset(Subset,Superset) )).

cnf(set_equal_sets_are_subsets1,axiom,
    ( ~ equal_sets(Subset,Superset)
    | subset(Subset,Superset) )).

cnf(set_equal_sets_are_subsets2,axiom,
    ( ~ equal_sets(Superset,Subset)
    | subset(Subset,Superset) )).

cnf(subsets_are_set_equal_sets,axiom,
    ( ~ subset(Set1,Set2)
    | ~ subset(Set2,Set1)
    | equal_sets(Set2,Set1) )).

%--------------------------------------------------------------------------
%--------------------------------------------------------------------------
