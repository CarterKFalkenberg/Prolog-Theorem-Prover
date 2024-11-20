%------------------------------------------------------------------------------
% File     : SWV307-2 : TPTP v7.3.0. Released v3.2.0.
% Domain   : Software Verification (Security)
% Problem  : Cryptographic protocol problem for Otway Rees
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.3.0, 0.08 v5.2.0, 0.00 v4.1.0, 0.11 v4.0.1, 0.17 v3.3.0, 0.14 v3.2.0
% Syntax   : Number of clauses     :    6 (   0 non-Horn;   3 unit;   6 RR)
%            Number of atoms       :    9 (   1 equality)
%            Maximal clause size   :    2 (   2 average)
%            Number of predicates  :    2 (   0 propositional; 2-3 arity)
%            Number of functors    :   15 (   7 constant; 0-2 arity)
%            Number of variables   :   14 (  14 singleton)
%            Maximal term depth    :    5 (   2 average)
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

cnf(c_Event_Oknows_substitution_1,axiom,
    ( A != B | c_Event_Oknows(A,C) = c_Event_Oknows(B,C) )).

cnf(c_Event_Oknows_substitution_2,axiom,
    ( A != B | c_Event_Oknows(C,A) = c_Event_Oknows(C,B) )).

cnf(c_Event_Oused_substitution_1,axiom,
    ( A != B | c_Event_Oused(A) = c_Event_Oused(B) )).

cnf(c_Message_Omsg_OAgent_substitution_1,axiom,
    ( A != B | c_Message_Omsg_OAgent(A) = c_Message_Omsg_OAgent(B) )).

cnf(c_Message_Omsg_OCrypt_substitution_1,axiom,
    ( A != B | c_Message_Omsg_OCrypt(A,C) = c_Message_Omsg_OCrypt(B,C) )).

cnf(c_Message_Omsg_OCrypt_substitution_2,axiom,
    ( A != B | c_Message_Omsg_OCrypt(C,A) = c_Message_Omsg_OCrypt(C,B) )).

cnf(c_Message_Omsg_OMPair_substitution_1,axiom,
    ( A != B | c_Message_Omsg_OMPair(A,C) = c_Message_Omsg_OMPair(B,C) )).

cnf(c_Message_Omsg_OMPair_substitution_2,axiom,
    ( A != B | c_Message_Omsg_OMPair(C,A) = c_Message_Omsg_OMPair(C,B) )).

cnf(c_Message_Omsg_ONonce_substitution_1,axiom,
    ( A != B | c_Message_Omsg_ONonce(A) = c_Message_Omsg_ONonce(B) )).

cnf(c_Message_Oparts_substitution_1,axiom,
    ( A != B | c_Message_Oparts(A) = c_Message_Oparts(B) )).

cnf(c_Public_OshrK_substitution_1,axiom,
    ( A != B | c_Public_OshrK(A) = c_Public_OshrK(B) )).

cnf(c_in_substitution_1,axiom,
    ( A != B | ~ c_in(A,C,D) | c_in(B,C,D) )).

cnf(c_in_substitution_2,axiom,
    ( A != B | ~ c_in(C,A,D) | c_in(C,B,D) )).

cnf(c_in_substitution_3,axiom,
    ( A != B | ~ c_in(C,D,A) | c_in(C,D,B) )).
    
cnf(cls_conjecture_2,negated_conjecture,
    ( ~ c_in(c_Message_Omsg_ONonce(v_NB),c_Event_Oused(v_evs2),tc_Message_Omsg) )).

cnf(cls_conjecture_4,negated_conjecture,
    ( c_in(c_Message_Omsg_OCrypt(c_Public_OshrK(v_A),c_Message_Omsg_OMPair(v_NA,c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(v_A),c_Message_Omsg_OAgent(v_B)))),c_Message_Oparts(c_Event_Oknows(c_Message_Oagent_OSpy,v_evs2)),tc_Message_Omsg) )).

cnf(cls_conjecture_6,negated_conjecture,
    ( v_NA = c_Message_Omsg_ONonce(v_NB) )).

cnf(cls_Event_Oc_A_58_Aparts_A_Iknows_ASpy_Aevs1_J_A_61_61_62_Ac_A_58_Aused_Aevs1_0,axiom,
    ( ~ c_in(V_c,c_Message_Oparts(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | c_in(V_c,c_Event_Oused(V_evs),tc_Message_Omsg) )).

cnf(cls_Message_OMPair__parts_1,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oparts(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oparts(V_H),tc_Message_Omsg) )).

cnf(cls_Message_Oparts_OBody__dest_0,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Oparts(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oparts(V_H),tc_Message_Omsg) )).

%------------------------------------------------------------------------------
