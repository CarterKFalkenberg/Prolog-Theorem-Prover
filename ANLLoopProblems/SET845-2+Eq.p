%------------------------------------------------------------------------------
% File     : SET845-2 : TPTP v7.3.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.3.0, 0.08 v5.2.0, 0.00 v5.1.0, 0.14 v4.1.0, 0.22 v4.0.1, 0.33 v3.7.0, 0.17 v3.3.0, 0.14 v3.2.0
% Syntax   : Number of clauses     :    7 (   0 non-Horn;   4 unit;   6 RR)
%            Number of atoms       :   11 (   3 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    3 (   0 propositional; 2-3 arity)
%            Number of functors    :    7 (   3 constant; 0-3 arity)
%            Number of variables   :   23 (  17 singleton)
%            Maximal term depth    :    3 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_HRN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(reflexivity,axiom,
    ( A = A )).

cnf(symmetry,axiom,
    ( A != B | B = A )).

cnf(transitivity,axiom,
    ( A != B | B != C | A = C )).

cnf(c_Union_substitution_1,axiom,
    ( A != B | c_Union(A,C) = c_Union(B,C) )).

cnf(c_Union_substitution_2,axiom,
    ( A != B | c_Union(C,A) = c_Union(C,B) )).

cnf(c_Zorn_OTFin_substitution_1,axiom,
    ( A != B | c_Zorn_OTFin(A,C) = c_Zorn_OTFin(B,C) )).

cnf(c_Zorn_OTFin_substitution_2,axiom,
    ( A != B | c_Zorn_OTFin(C,A) = c_Zorn_OTFin(C,B) )).

cnf(c_Zorn_Osucc_substitution_1,axiom,
    ( A != B | c_Zorn_Osucc(A,C,D) = c_Zorn_Osucc(B,C,D) )).

cnf(c_Zorn_Osucc_substitution_2,axiom,
    ( A != B | c_Zorn_Osucc(C,A,D) = c_Zorn_Osucc(C,B,D) )).

cnf(c_Zorn_Osucc_substitution_3,axiom,
    ( A != B | c_Zorn_Osucc(C,D,A) = c_Zorn_Osucc(C,D,B) )).

cnf(tc_set_substitution_1,axiom,
    ( A != B | tc_set(A) = tc_set(B) )).

cnf(c_in_substitution_1,axiom,
    ( A != B | ~ c_in(A,C,D) | c_in(B,C,D) )).

cnf(c_in_substitution_2,axiom,
    ( A != B | ~ c_in(C,A,D) | c_in(C,B,D) )).

cnf(c_in_substitution_3,axiom,
    ( A != B | ~ c_in(C,D,A) | c_in(C,D,B) )).

cnf(c_lessequals_substitution_1,axiom,
    ( A != B | ~ c_lessequals(A,C,D) | c_lessequals(B,C,D) )).

cnf(c_lessequals_substitution_2,axiom,
    ( A != B | ~ c_lessequals(C,A,D) | c_lessequals(C,B,D) )).

cnf(c_lessequals_substitution_3,axiom,
    ( A != B | ~ c_lessequals(C,D,A) | c_lessequals(C,D,B) )).
    
cnf(cls_Set_OUnion__upper_0,axiom,
    ( ~ c_in(V_B,V_A,tc_set(T_a))
    | c_lessequals(V_B,c_Union(V_A,T_a),tc_set(T_a)) )).

cnf(cls_Set_Osubset__antisym_0,axiom,
    ( ~ c_lessequals(V_B,V_A,tc_set(T_a))
    | ~ c_lessequals(V_A,V_B,tc_set(T_a))
    | V_A = V_B )).

cnf(cls_Zorn_OAbrial__axiom1_0,axiom,
    ( c_lessequals(V_x,c_Zorn_Osucc(V_S,V_x,T_a),tc_set(tc_set(T_a))) )).

cnf(cls_Zorn_OTFin_OsuccI_0,axiom,
    ( ~ c_in(V_x,c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a)))
    | c_in(c_Zorn_Osucc(V_S,V_x,T_a),c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a))) )).

cnf(cls_conjecture_0,negated_conjecture,
    ( c_in(v_m,c_Zorn_OTFin(v_S,t_a),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_1,negated_conjecture,
    ( v_m = c_Union(c_Zorn_OTFin(v_S,t_a),tc_set(t_a)) )).

cnf(cls_conjecture_2,negated_conjecture,
    ( v_m != c_Zorn_Osucc(v_S,v_m,t_a) )).

%------------------------------------------------------------------------------
