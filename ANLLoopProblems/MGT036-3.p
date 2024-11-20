%--------------------------------------------------------------------------
% File     : MGT036-3 : TPTP v7.3.0. Released v2.4.0.
% Domain   : Management (Organisation Theory)
% Problem  : First movers never outcompete efficient producers.
% Version  : [PM93] axioms.
% English  :

% Refs     : [PM93]  Peli & Masuch (1993), The Logic of Propogation Strateg
%          : [PM94]  Peli & Masuch (1994), The Logic of Propogation Strateg
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.10 v5.2.0, 0.00 v2.4.0
% Syntax   : Number of clauses     :    9 (   0 non-Horn;   4 unit;   9 RR)
%            Number of atoms       :   23 (   0 equality)
%            Maximal clause size   :    5 (   3 average)
%            Number of predicates  :    5 (   0 propositional; 1-4 arity)
%            Number of functors    :    6 (   5 constant; 0-2 arity)
%            Number of variables   :   18 (   0 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : Created with tptp2X -f tptp -t clausify:otter MGT036+3.p
%--------------------------------------------------------------------------
cnf(mp_symmetry_of_subpopulations_1,axiom,
    ( ~ environment(A)
    | ~ subpopulations(B,C,A,D)
    | subpopulations(C,B,A,D) )).

cnf(d2_2,hypothesis,
    ( ~ environment(A)
    | ~ subpopulations(B,C,A,D)
    | ~ greater_or_equal(growth_rate(C,D),zero)
    | ~ greater(zero,growth_rate(B,D))
    | outcompetes(C,B,D) )).

cnf(d2_3,hypothesis,
    ( ~ environment(A)
    | ~ subpopulations(B,C,A,D)
    | ~ outcompetes(C,B,D)
    | greater_or_equal(growth_rate(C,D),zero) )).

cnf(d2_4,hypothesis,
    ( ~ environment(A)
    | ~ subpopulations(B,C,A,D)
    | ~ outcompetes(C,B,D)
    | greater(zero,growth_rate(B,D)) )).

cnf(a13_star_5,hypothesis,
    ( environment(sk1) )).

cnf(a13_star_6,hypothesis,
    ( subpopulations(first_movers,efficient_producers,sk1,sk2) )).

cnf(a13_star_7,hypothesis,
    ( greater_or_equal(growth_rate(first_movers,sk2),zero) )).

cnf(a13_star_8,hypothesis,
    ( greater(zero,growth_rate(efficient_producers,sk2)) )).

cnf(prove_t5_star_9,negated_conjecture,
    ( ~ environment(A)
    | ~ subpopulations(first_movers,efficient_producers,A,B)
    | ~ outcompetes(first_movers,efficient_producers,B) )).

%--------------------------------------------------------------------------
