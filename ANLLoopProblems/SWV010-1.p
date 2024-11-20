%--------------------------------------------------------------------------
% File     : SWV010-1 : TPTP v7.3.0. Released v2.4.0.
% Domain   : Software Verification
% Problem  : Fact 1 of the Neumann-Stubblebine analysis
% Version  : [Wei99] axioms.
% English  :

% Refs     : [Wei99] Weidenbach (1999), Towards and Automatic Analysis of S
%            [Bau99] Baumgartner (1999), FTP'2000 - Problem Sets
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v2.5.0, 0.17 v2.4.0
% Syntax   : Number of clauses     :    8 (   0 non-Horn;   5 unit;   8 RR)
%            Number of atoms       :   15 (   0 equality)
%            Maximal clause size   :    4 (   2 average)
%            Number of predicates  :    4 (   0 propositional; 1-1 arity)
%            Number of functors    :   15 (   6 constant; 0-4 arity)
%            Number of variables   :   15 (   1 singleton)
%            Maximal term depth    :    6 (   3 average)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created by tptp2X -f tptp -t cnf:otter SWV010+1.p
%--------------------------------------------------------------------------
cnf(a_sent_message_i_to_b_3,axiom,
    ( message(sent(a,b,pair(a,an_a_nonce))) )).

cnf(a_stored_message_i_4,axiom,
    ( a_stored(pair(b,an_a_nonce)) )).

cnf(a_forwards_secure_5,axiom,
    ( message(sent(a,A,pair(E,encrypt(F,C))))
    | ~ a_stored(pair(A,B))
    | ~ message(sent(t,a,triple(encrypt(quadruple(A,B,C,D),at),E,F))) )).

cnf(nonce_a_is_fresh_to_b_9,axiom,
    ( fresh_to_b(an_a_nonce) )).

cnf(b_creates_freash_nonces_in_time_10,axiom,
    ( message(sent(b,t,triple(b,generate_b_nonce(B),encrypt(triple(A,B,generate_expiration_time(B)),bt))))
    | ~ fresh_to_b(B)
    | ~ message(sent(A,b,pair(A,B))) )).

cnf(t_holds_key_at_for_a_13,axiom,
    ( t_holds(key(at,a)) )).

cnf(t_holds_key_bt_for_b_14,axiom,
    ( t_holds(key(bt,b)) )).

cnf(server_t_generates_key_16,axiom,
    ( message(sent(t,C,triple(encrypt(quadruple(A,D,generate_key(D),E),G),encrypt(triple(C,generate_key(D),E),F),B)))
    | ~ message(sent(A,t,triple(A,B,encrypt(triple(C,D,E),F))))
    | ~ t_holds(key(G,C))
    | ~ t_holds(key(F,A)) )).

%--------------------------------------------------------------------------
