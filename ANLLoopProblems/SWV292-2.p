%------------------------------------------------------------------------------
% File     : SWV292-2 : TPTP v8.2.0. Released v3.2.0.
% Domain   : Software Verification (Security)
% Problem  : Cryptographic protocol problem for Otway Rees
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.08 v8.2.0, 0.14 v8.1.0, 0.00 v7.5.0, 0.17 v7.4.0, 0.00 v7.1.0, 0.17 v7.0.0, 0.38 v6.3.0, 0.14 v6.2.0, 0.11 v6.1.0, 0.00 v5.5.0, 0.12 v5.4.0, 0.10 v5.2.0, 0.00 v5.0.0, 0.29 v4.1.0, 0.12 v4.0.1, 0.40 v4.0.0, 0.43 v3.4.0, 0.50 v3.3.0, 0.33 v3.2.0
% Syntax   : Number of clauses     :   16 (   5 unt;   2 nHn;  16 RR)
%            Number of literals    :   32 (   0 equ;  16 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    9 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 3-3 aty)
%            Number of functors    :   32 (  32 usr;  15 con; 0-3 aty)
%            Number of variables   :   29 (   4 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_conjecture_0,negated_conjecture,
    ~ c_in(v_A,c_Event_Obad,tc_Message_Oagent) ).

cnf(cls_conjecture_1,negated_conjecture,
    c_in(v_evs4,c_OtwayRees_Ootway,tc_List_Olist(tc_Event_Oevent)) ).

cnf(cls_conjecture_4,negated_conjecture,
    c_in(c_Event_Oevent_OGets(v_Ba,c_Message_Omsg_OMPair(c_Message_Omsg_ONonce(v_NAa),c_Message_Omsg_OMPair(v_X,c_Message_Omsg_OCrypt(c_Public_OshrK(v_Ba),c_Message_Omsg_OMPair(c_Message_Omsg_ONonce(v_NB),c_Message_Omsg_OKey(v_K)))))),c_List_Oset(v_evs4,tc_Event_Oevent),tc_Event_Oevent) ).

cnf(cls_conjecture_5,negated_conjecture,
    c_in(c_Message_Omsg_OCrypt(c_Public_OshrK(v_A),c_Message_Omsg_OMPair(v_NA,c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(v_A),c_Message_Omsg_OAgent(v_B)))),c_Message_Oparts(c_insert(v_X,c_Event_Oknows(c_Message_Oagent_OSpy,v_evs4),tc_Message_Omsg)),tc_Message_Omsg) ).

cnf(cls_conjecture_6,negated_conjecture,
    ~ c_in(c_Event_Oevent_OSays(v_A,v_B,c_Message_Omsg_OMPair(v_NA,c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(v_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(v_B),c_Message_Omsg_OCrypt(c_Public_OshrK(v_A),c_Message_Omsg_OMPair(v_NA,c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(v_A),c_Message_Omsg_OAgent(v_B)))))))),c_List_Oset(v_evs4,tc_Event_Oevent),tc_Event_Oevent) ).

cnf(cls_conjecture_7,negated_conjecture,
    ( c_in(c_Event_Oevent_OSays(v_A,v_B,c_Message_Omsg_OMPair(v_NA,c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(v_A),c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(v_B),c_Message_Omsg_OCrypt(c_Public_OshrK(v_A),c_Message_Omsg_OMPair(v_NA,c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(v_A),c_Message_Omsg_OAgent(v_B)))))))),c_List_Oset(v_evs4,tc_Event_Oevent),tc_Event_Oevent)
    | ~ c_in(c_Message_Omsg_OCrypt(c_Public_OshrK(v_A),c_Message_Omsg_OMPair(v_NA,c_Message_Omsg_OMPair(c_Message_Omsg_OAgent(v_A),c_Message_Omsg_OAgent(v_B)))),c_Message_Oparts(c_Event_Oknows(c_Message_Oagent_OSpy,v_evs4)),tc_Message_Omsg) ) ).

cnf(cls_Event_OSays__imp__analz__Spy__dest_0,axiom,
    ( ~ c_in(c_Event_Oevent_OSays(V_A,V_B,V_X),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | c_in(V_X,c_Message_Oanalz(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg) ) ).

cnf(cls_Message_OCrypt__synth_0,axiom,
    ( ~ c_in(c_Message_Omsg_OCrypt(V_K,V_X),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OCrypt(V_K,V_X),V_H,tc_Message_Omsg)
    | c_in(c_Message_Omsg_OKey(V_K),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_OFake__parts__insert__in__Un__dest_0,axiom,
    ( ~ c_in(V_Z,c_Message_Oparts(c_insert(V_X,V_H,tc_Message_Omsg)),tc_Message_Omsg)
    | ~ c_in(V_X,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(V_Z,c_union(c_Message_Osynth(c_Message_Oanalz(V_H)),c_Message_Oparts(V_H),tc_Message_Omsg),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__analz_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_Y,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__synth__analz__iff1_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(c_Message_Oanalz(V_H)),tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz__into__parts__dest_0,axiom,
    ( ~ c_in(V_c,c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_c,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Osynth_OInj_0,axiom,
    ( ~ c_in(V_X,V_H,tc_Message_Omsg)
    | c_in(V_X,c_Message_Osynth(V_H),tc_Message_Omsg) ) ).

cnf(cls_OtwayRees_OGets__imp__Says__dest_0,axiom,
    ( ~ c_in(V_evs,c_OtwayRees_Ootway,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Event_Oevent_OGets(V_B,V_X),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent)
    | c_in(c_Event_Oevent_OSays(v_sko__usf(V_B,V_X,V_evs),V_B,V_X),c_List_Oset(V_evs,tc_Event_Oevent),tc_Event_Oevent) ) ).

cnf(cls_OtwayRees_OSpy__see__shrK__D__dest_0,axiom,
    ( ~ c_in(V_evs,c_OtwayRees_Ootway,tc_List_Olist(tc_Event_Oevent))
    | ~ c_in(c_Message_Omsg_OKey(c_Public_OshrK(V_A)),c_Message_Oparts(c_Event_Oknows(c_Message_Oagent_OSpy,V_evs)),tc_Message_Omsg)
    | c_in(V_A,c_Event_Obad,tc_Message_Oagent) ) ).

cnf(cls_Set_OUnE_0,axiom,
    ( ~ c_in(V_c,c_union(V_A,V_B,T_a),T_a)
    | c_in(V_c,V_B,T_a)
    | c_in(V_c,V_A,T_a) ) ).

%------------------------------------------------------------------------------
