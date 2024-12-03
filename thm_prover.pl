run:-
    %consult('ANLLoopAnswer'),
    % SAT
    /* prove('ANLLoopProblems/KRS005-1.p',1),
    prove('ANLLoopProblems/NLP043-1.p',1),
    prove('ANLLoopProblems/SET777-1.p',1),
    prove('ANLLoopProblems/SWV010-1.p',1),
    prove('ANLLoopProblems/SYN059-1.p',1), */
    % EASY
    prove('ANLLoopProblems/PUZ001-1.p',60),
    prove('ANLLoopProblems/PUZ011-1.p',60),
    prove('ANLLoopProblems/SYN003-1.006.p',60),
    prove('ANLLoopProblems/SYN009-3.p',60),
    prove('ANLLoopProblems/SYN068-1.p',60),
    % MED
    prove('ANLLoopProblems/COM003-2.p',60),
    prove('ANLLoopProblems/KRS002-1.p',60),
    prove('ANLLoopProblems/MGT036-3.p',60),
    % all above are currently solved with model resolution + tautology + factoring + subsumption + proof output
    /* prove('ANLLoopProblems/SWV292-2.p',60),
    prove('ANLLoopProblems/SYN328-1.p',60). */
    % HARD
   /*  prove('ANLLoopProblems/ALG002-1.p',60),
    prove('ANLLoopProblems/GRP001-5.p',60),
    prove('ANLLoopProblems/FLD001-3.p',60),
    prove('ANLLoopProblems/LCL064-1.p',60),
    prove('ANLLoopProblems/PUZ031-1.p',60).  */
    % EQUALITY
    %prove('ANLLoopProblems/COM004-1.p',5), % can't solve
   %prove('ANLLoopProblems/COM004-1+Eq.p',5),
    %prove('ANLLoopProblems/LCL171-3.p',5),
   %prove('ANLLoopProblems/LCL171-3+Eq.p',5), % can't solve
    prove('ANLLoopProblems/PUZ020-1.p',5),
   %prove('ANLLoopProblems/PUZ020-1+Eq.p',5),
    prove('ANLLoopProblems/SET845-2.p',5),
   %prove('ANLLoopProblems/SET845-2+Eq.p',5),
    prove('ANLLoopProblems/SWV307-2.p',5).
   %prove('ANLLoopProblems/SWV307-2+Eq.p',5).
%==================================================================================================
%----General ANL Loop style theorem prover. This is the overall control code, non-specific to a 
%----particular calculus
%==================================================================================================
%Eclipse :-use_module(library(iso)).
%Eclipse :-use_module(library(numbervars)).
%Eclipse :-set_flag(occur_check,on).
:-use_module(library(time)).    %%swi
:-use_module(library(apply)).
:-set_prolog_flag(occurs_check,true).      %%swi
%--------------------------------------------------------------------------------------------------
%-----Operator definitions for clauses
%----Postfix for !=
:-op(100,xf,'!').
:-op(405,xfx,'=').
:-op(410,fy,~).
% :-op(502,xfy,'|').
%FOR SWI 
:-(system_mode(true),op(502,xfy,'|'),system_mode(false)).
%--------------------------------------------------------------------------------------------------
:-dynamic cnf/3.
:-dynamic cnf_old/3.
:-nb_setval(next_id, 1).
%==================================================================================================
%----Overall control of ANL loop
%==================================================================================================
tptp_directory('/home/tptp/TPTP').
%--------------------------------------------------------------------------------------------------
%----Entry point to prover. Read clauses and call ANL loop
prove(FileName,TimeLimit):-
    write('%--------------------------------------------------------'),nl,
    write('% ANLLoop running on '),
    write(FileName),nl,
    initialise_deduction(FileName,InitialisedClauses),
    introspective_subsumption(InitialisedClauses, NonSubsumedClauses),
    % for debugging
    %sort(NonSubsumedClauses,Sorted),
    %writeln("Sorted Clauses (Subsumption done): "), print_list(Sorted),
    % ^^ for debugging
    initialise_model_resolution(NonSubsumedClauses, FalseClauses),
    %writeln("WARNING: Did model resolution, but not using model resolution"), 
    writeln("False Clauses (TBU):"),
    print_list(FalseClauses),
    %write("NewInitialisedClauses: "), print_list(NewInitialisedClauses),
    StartTime is cputime,
    call_with_time_limit(
        TimeLimit,
        catch(atp_loop(FalseClauses,0,Loops,SZSResult,Refutation),SWIError,
(swi_error_to_SZS(SWIError,SZSError),SZSResult = SZSError,Refutation = none,Loops = unknown))
    ),
    EndTime is cputime,
    CPUTime is EndTime - StartTime,
    write('% SZS status '),
    write(SZSResult),
    write(' for '),
    write(FileName),
    write(' : CPU = '),
    write(CPUTime),
    write('; Loops = '),
    write(Loops),nl,
    ( SZSResult == 'Unsatisfiable'
   -> ( write('% SZS output start Refutation for '),
        write(FileName),nl,
        writeln("Format is cnf/cnf_old([ID, OG_name, parentID1, parentID2], terms,weight)"),
        %write(Refutation),nl,
        print_clauses_from_ids(Refutation),
        write('% SZS output end Refutation for '),
        write(FileName),nl
      ) ; 
        true 
    ),
    write('%--------------------------------------------------------'),nl,
    !.
%--------------------------------------------------------------------------------------------------
print_list([]):-
    !.
print_list([Head | Tail]):-
    writeln(Head),
    print_list(Tail).
%--------------------------------------------------------------------------------------------------
print_clauses_from_ids([]):-
    !.
print_clauses_from_ids([ID | Tail]):-
    get_clause_from_id(ID, Clause),
    writeln(Clause),
    print_clauses_from_ids(Tail). 
%--------------------------------------------------------------------------------------------------
swi_error_to_SZS(time_limit_exceeded,'Timeout').

swi_error_to_SZS(error(resource_error(_),_),'ResourceOut').
%--------------------------------------------------------------------------------------------------
initialise_deduction(FileName,ProblemClauses):-
    retractall(cnf(_,_,_)),
    retractall(cnf_old(_,_,_)),
    read_cnfs_from_file(FileName,ReadClauses),
    % RENAME CLAUSES to format: [id, original_name, left_parent, right_parent]. First reset global id to 1 if needed
    nb_setval(next_id, 1),
    rename_clauses(ReadClauses, RenamedClauses),
    %write(RenamedClauses),
    weigh_clauses(RenamedClauses, WeighedClauses),
    sort(3, @=<, WeighedClauses, ProblemClauses),
write('Problem Clauses (sorted by weight):'), write(ProblemClauses),nl.
%--------------------------------------------------------------------------------------------------
initialise_model_resolution(NonSubsumedClauses, FalseClauses):-
    /* % get # of FALSE clauses using positive interpretation
    num_false_clauses_positive_interpretation(NonSubsumedClauses, 0, PositiveCount),
    % get # of FALSE clauses using negative interpretation
    num_false_clauses_negative_interpretation(NonSubsumedClauses, 0, NegativeCount),
    % Whichever interpretation is better, add all TRUE clauses in that interpretation to the CBU
    % The remaining clauses are the FalseClauses (i.e. new TBU)
    
    ((PositiveCount > NegativeCount) -> 
        (model_resolve_positive(NonSubsumedClauses, [], FalseClauses)) 
        ; (model_resolve_negative(NonSubsumedClauses, [], FalseClauses))
    ). */
    model_resolve_negative(NonSubsumedClauses, [], FalseClauses).
%--------------------------------------------------------------------------------------------------
model_resolve_positive([], CurrentFalseClauses, CurrentFalseClauses):-
    !.

model_resolve_positive([Clause | RestOfClauses], CurrentFalseClauses, AllFalseClauses):-
    true_in_positive_interpretation(Clause, Result),
    (
        (Result == "TRUE") ->
        (   add_to_can_be_used(Clause),
            model_resolve_positive(RestOfClauses, CurrentFalseClauses, AllFalseClauses)
        )
        ; (
            append([Clause], CurrentFalseClauses, NewCurrentFalseClauses),
            model_resolve_positive(RestOfClauses, NewCurrentFalseClauses, AllFalseClauses)
        )
    ).
%--------------------------------------------------------------------------------------------------
model_resolve_negative([], CurrentFalseClauses, CurrentFalseClauses):-
    !.

model_resolve_negative([Clause | RestOfClauses], CurrentFalseClauses, AllFalseClauses):-
    true_in_negative_interpretation(Clause, Result),
    
    (
        (Result == "TRUE") ->
        (   add_to_can_be_used(Clause),
            model_resolve_negative(RestOfClauses, CurrentFalseClauses, AllFalseClauses)
        )
        ; (
            append([Clause], CurrentFalseClauses, NewCurrentFalseClauses),
            model_resolve_negative(RestOfClauses, NewCurrentFalseClauses, AllFalseClauses)
        )
    ).
%--------------------------------------------------------------------------------------------------
num_false_clauses_positive_interpretation([], CurrentCount, CurrentCount):-
    !.
num_false_clauses_positive_interpretation([Clause | RestOfClauses], CurrentCount, Count):-
    true_in_positive_interpretation(Clause, Result),
    (
        (Result == "TRUE") -> 
        (num_false_clauses_positive_interpretation(RestOfClauses, CurrentCount, Count)) 
        ; (
            NewCurrentCount is CurrentCount + 1,
            num_false_clauses_positive_interpretation(RestOfClauses, NewCurrentCount, Count)
        )
    ).
%--------------------------------------------------------------------------------------------------
num_false_clauses_negative_interpretation([], CurrentCount, CurrentCount):-
    !.
num_false_clauses_negative_interpretation([Clause | RestOfClauses], CurrentCount, Count):-
    true_in_negative_interpretation(Clause, Result),
    (
        (Result == "TRUE") -> 
        (num_false_clauses_negative_interpretation(RestOfClauses, CurrentCount, Count)) 
        ; (
            NewCurrentCount is CurrentCount + 1,
            num_false_clauses_negative_interpretation(RestOfClauses, NewCurrentCount, Count)
        )
    ).
%--------------------------------------------------------------------------------------------------
true_in_positive_interpretation(cnf(_Name, Literals, _Weight), Result):-
    true_in_positive_interpretation(Literals, Result).

true_in_positive_interpretation([], "FALSE"):-
    !.
true_in_positive_interpretation([Literal | _RestOfLiterals], "TRUE"):-
    var(Literal), 
    !.
true_in_positive_interpretation([Literal | _RestOfLiterals], "TRUE"):-
    Literal =.. [Symbol|_Arguments],
    (Symbol \= '~'), 
    !.
true_in_positive_interpretation([_Literal | RestOfLiterals], Result):-
    true_in_positive_interpretation(RestOfLiterals, Result).
%--------------------------------------------------------------------------------------------------
true_in_negative_interpretation(cnf(_Name, Literals, _Weight), Result):-
    true_in_negative_interpretation(Literals, Result).
    
true_in_negative_interpretation([], "FALSE"):-
    !.
true_in_negative_interpretation([Literal | _RestOfLiterals], "TRUE"):-
    \+ var(Literal),   
    Literal =.. [Symbol|_Arguments],
    (Symbol == '~'), 
    !.
true_in_negative_interpretation([_Literal | RestOfLiterals], Result):-
    true_in_negative_interpretation(RestOfLiterals, Result).
%--------------------------------------------------------------------------------------------------
rename_clauses([],[]).
rename_clauses([cnf(Name, Literals, Weight)|TailClauses], [cnf(NewName, Literals, Weight)|RenamedTailClauses]):-
    nb_getval(next_id, ID),
    rename(Name, ID, NewName),
    increment_id(),
    rename_clauses(TailClauses, RenamedTailClauses).
rename(Name, ID, [ID, Name, none, none]).
%--------------------------------------------------------------------------------------------------
name_resolvant_clause([ID1, _, _, _], [ID2, _, _, _], [ResolvantID, "resolvant", ID1, ID2]):-
    nb_getval(next_id, ResolvantID),
    increment_id().
%--------------------------------------------------------------------------------------------------
name_factored_clause([ParentID, _, _, _], [FactoredID, "factor", ParentID, none]):-
    nb_getval(next_id, FactoredID),
    increment_id().
%--------------------------------------------------------------------------------------------------
name_paramodulated_clause([ID1, _, _, _], [ID2, _, _, _], [ParamodulatedID, "paramodulated", ID1, ID2]):-
    nb_getval(next_id, ParamodulatedID),
    increment_id().
%--------------------------------------------------------------------------------------------------
weigh_clauses([], []).

weigh_clauses([cnf(Name, Literals,_)|Tail],[cnf(Name,Literals,Weight)|WeightedTail]):-
    term_flatten(Literals, FlatList),
    kbo_length(FlatList, Weight),
    weigh_clauses(Tail, WeightedTail).
%--------------------------------------------------------------------------------------------------
term_flatten(Var, [Var]):-
    var(Var),   %- if Var is a variable
    !.

term_flatten([], []):-
    !.

term_flatten([Head|Tail], Flattened):-
    !,
    term_flatten(Head, FlatHead), 
    term_flatten(Tail, FlatTail),
    append(FlatHead, FlatTail, Flattened).

term_flatten(~A, Flattened):-
    !,
    term_flatten(A, Flattened).

term_flatten(Atom, [Symbol | FlatArguments]):-
    Atom =.. [Symbol|Arguments],
    term_flatten(Arguments, FlatArguments).
%--------------------------------------------------------------------------------------------------
%getRefutation(ToBeAdded, Added, Refutation, NewRefutation)

get_refutation([], _, Refutation, Refutation):-
    !.
get_refutation([[ID, _, PID1, PID2]|Tail], Added, Refutation, [ID|NewRefutation]):-
    %get_clause_from_id(ID, Clause),
    ((number(PID1), \+ member(PID1, Added)) -> (   
        get_clause_from_id(PID1, PID1Clause),
        get_name_from_clause(PID1Clause, PID1Name),
        append([PID1Name], Tail, UpdatedTail1)
    );(UpdatedTail1 = Tail)
    ),
    ((number(PID2), \+ member(PID2, Added)) -> (  
        get_clause_from_id(PID2, PID2Clause),
        get_name_from_clause(PID2Clause, PID2Name),
        append([PID2Name], UpdatedTail1, UpdatedTail2)
    );(UpdatedTail2 = UpdatedTail1)
    ),
    get_refutation(UpdatedTail2, [ID | Added], Refutation, NewRefutation).
    
% CNF
get_clause_from_id(ID, cnf([ID, A, B, C], D, E)):-
    cnf([ID, A, B, C], D, E),
    !.

% CNF_OLD
get_clause_from_id(ID, cnf_old([ID, A, B, C], D, E)):-
    cnf_old([ID, A, B, C], D, E).

% CNF
get_name_from_clause(cnf(Name, _, _), Name).

% CNF_OLD
get_name_from_clause(cnf_old(Name, _, _), Name).
%--------------------------------------------------------------------------------------------------
%----Test if a proof has been found
atp_loop(ToBeUsed,Loops,Loops,'Unsatisfiable',Refutation):-
    %writeln("In UNS loop"),
    member(cnf(FalseClauseName,[],_),ToBeUsed),
    writeln("UNSATISFIABLE"),
    !,
    add_to_can_be_used(cnf(FalseClauseName, [], weight)),
    %writeln("Added false clause to CBU"),
    % false clause name is empty!
    get_refutation([FalseClauseName], [], [], UnsRefutation),
    writeln("Got refutation"),
    sort(UnsRefutation, Refutation).
    %print_list(SortedRefutation),
    %print_clauses_from_ids(SortedRefutation).


    %maplist(n_pricep, UnsRefutation, UnsIDToClause).
    %keysort(UnsIDToClause, SortedIDToClause),
    %maplist(pair_value, SortedIDToClause, Refutation),
    

%----Test if no proof can be found
atp_loop([],Loops,Loops,'Satisfiable',none):-
    !.

%----Take first to_be_used clause and do inferences 
atp_loop([ChosenClause|RestOfToBeUsed],LoopsSoFar,FinalLoops,SZSResult,Refutation):-
    %write("ChosenClause: "), writeln(ChosenClause), 
%----Move the to_be_used clause to can_be_used
    add_to_can_be_used(ChosenClause),
%----Do all possible inferences
    findall(NewClause,do_inference(ChosenClause,NewClause),NewClauses),
    %writeln("Inferred clauses:"), print_list(NewClauses),
% do tautology deletion, introspective subsumption
    tautology_deletion(NewClauses, NoTautologyNewClauses),
    introspective_subsumption(NoTautologyNewClauses, IntrospectivelySubsumedNewClauses),
% do forward subsumption on the inferred clauses
    forward_subsumption(IntrospectivelySubsumedNewClauses, RestOfToBeUsed, ForwardSubsumedNewClauses),
% do backward subsumption on the inferred clauses
    %writeln("Doing backward subsumption"),
    backward_subsumption(ForwardSubsumedNewClauses, RestOfToBeUsed, BackwardSubsumedToBeUsed),
    %writeln("Done with backward subsumption"),
% weigh clauses 
    weigh_clauses(ForwardSubsumedNewClauses, WeighedNewClauses),
    %writeln("Done weighing clauses"),
%----Create new to_be_used list and loop. Breadth first search
    %append(RestOfToBeUsed, WeighedNewClauses, NewToBeUsed),
    append(BackwardSubsumedToBeUsed,WeighedNewClauses,NewToBeUsed),
    %writeln("Done appending to be used"),
%write('----New ToBeUsed is'), write(NewToBeUsed),nl,
    sort(3, @=<, NewToBeUsed, WeighedNewToBeUsed),
    %writeln("Done sorting"),
%    write("sorted!"),nl,
%----Go round the loop. Note this should be tail recursion optimized. If it's not then buy a 
%----better Prolog or place a cut here.
    OneMoreLoop is LoopsSoFar + 1,
    %writeln("Calling recursion"),
    atp_loop(WeighedNewToBeUsed,OneMoreLoop,FinalLoops,SZSResult,Refutation).
%--------------------------------------------------------------------------------------------------
%----Store can_be_used clause in the database
add_to_can_be_used(Clause):-
    assertz(Clause).
%--------------------------------------------------------------------------------------------------
%==================================================================================================
%----Inference rules and support
%==================================================================================================
%--------------------------------------------------------------------------------------------------

%----Binary resolution inference
do_inference(cnf(ChosenName,ChosenClauseLiterals,_),cnf(ResolvantName,ResolvantLiterals,_)):-
%----Select literal from first parent clause
    select(SelectedLiteral,ChosenClauseLiterals,RestOfChosenClauseLiterals),

% if ChosenClauseLiterals are FALSE, then only select the largest literal
    true_in_negative_interpretation(ChosenClauseLiterals, Result),
    (
        (Result == "FALSE") -> 
        (nothing_bigger(SelectedLiteral, RestOfChosenClauseLiterals))
        ; true
    ),
%----Make opposite sign literal required for other parent
    opposite_sign_literal(SelectedLiteral,NegatedSelectedLiteral),
    %write("NegatedSelectedLiteral: "), writeln(NegatedSelectedLiteral),
%----Look for other parent in database
    cnf(CBUName,CBUClauseLiterals,_),

% Only do inference on a clause if exactly one parent is FALSE
% QUESTION: Can two FALSE clauses resolve on each other, or is it EXACTLY one false and one true clause?
    exactly_one_clause_is_false(ChosenClauseLiterals, CBUClauseLiterals),

    %write("Selected CBU Clause Literals:"), writeln(CBUClauseLiterals),
%----Select literal of opposite sign that unifies, from the second parent
    select(NegatedSelectedLiteral,CBUClauseLiterals,RestOfCBUClauseLiterals),

/* % if CBUClauseLiterals are FALSE, then only valid if NegatedSelectedLiteral is the largest literal
    true_in_negative_interpretation(CBUClauseLiterals, Result),
    (
        (Result == "FALSE") -> 
        (nothing_bigger(NegatedSelectedLiteral, RestOfCBUClauseLiterals))
        ; true
    ), */


    %writeln("NegatedSelectedLiteral successfull"),
    %writeln("Warning: not using KBO"),
    %nothing_bigger(NegatedSelectedLiteral, RestOfCBUClauseLiterals),
    %writeln("NothingBigger successfull"),
%----Get name of resolvant
    name_resolvant_clause(ChosenName, CBUName, ResolvantName),
%write("ResolvantName"),write(ResolvantName),nl,
%----Collect the leftover literals
    append(RestOfChosenClauseLiterals,RestOfCBUClauseLiterals,ResolvantLiterals).

%----If you add binary factoring, you need to enable theta-subsumption below

% Factoring, allowing checking of the entire list (causes duplicate factored clauses and wastes time)
/* do_inference(cnf(ChosenName,ChosenClauseLiterals,_),cnf(f(ChosenName),FactoredLiterals,weight)):-
    % if there exists a copy somewhere later in the list, then remove
    select(FactoredLiteral, ChosenClauseLiterals, FactoredLiterals), 
    member(FactoredLiteral, FactoredLiterals).
    %write("\t\tChosen clause literals:"), write(ChosenClauseLiterals), nl,
    %write("\t\tFactored to be:"), write(FactoredLiterals),nl. */


% Factoring, only checking later in the list 
do_inference(cnf(ChosenName,ChosenClauseLiterals,_),cnf(FactoredName,FactoredLiterals,weight)):-
    % get FactoredLiteral and its index 
    nth0(FactoredLiteralIndex, ChosenClauseLiterals, FactoredLiteral, FactoredLiterals),
        
    % subsest is the list starting from the element following FactoredLiteral
    remove_n(FactoredLiteralIndex+1, ChosenClauseLiterals, subsest),

    % KBO need to check entire list for nothing bigger, normal only need to check later in the list
    nothing_bigger(FactoredLiteral, FactoredLiterals),

    % check if there is a copy somewhere in the subsest. If so, factor (i.e. return true)
    member(FactoredLiteral, subsest),

    % get factored clause name
    name_factored_clause(ChosenName, FactoredName).


% Paramodulation, chosen clause is equality literal
do_inference(cnf(ChosenName,ChosenClauseLiterals,_),cnf(ParamodulatedName,ParamodulatedLiterals,_)):-
    select(SelectedLiteral,ChosenClauseLiterals,_RestOfChosenClauseLiterals),
    positive_equality_terms(SelectedLiteral, LeftLiteral, RightLiteral),
    (
        bigger(LeftLiteral, RightLiteral) -> (ChosenLiteral = LeftLiteral, EqualLiteral = RightLiteral)
        ; (ChosenLiteral = RightLiteral, EqualLiteral = LeftLiteral)
    ),
    cnf(CBUName,CBUClauseLiterals,_),
    select(CBULiteral,CBUClauseLiterals,RestOfCBUClauseLiterals),
    \+ (positive_equality_term(CBULiteral)),
    % now need to check that ChosenLiteral is in CBULiteral
         % e.g. check that p(a) is in l(A, y(B, p(a)))  
    occurs_in_term(ChosenLiteral, CBULiteral),
    % then, replace CBULiteral[ChosenLiteral] => CBULiteral[EqualLiteral]
    replace_term(ChosenLiteral, EqualLiteral, CBULiteral, NewCBULiteral),
    name_paramodulated_clause(ChosenName, CBUName, ParamodulatedName),
    append([NewCBULiteral], RestOfCBUClauseLiterals, ParamodulatedLiterals).
%--------------------------------------------------------------------------------------------------

% Base case: SubTerm is exactly the same as Term.
occurs_in_term(SubTerm, Term) :-
    SubTerm == Term, !.

% If Term is atomic and base case fails, SubTerm cannot occur in it.
occurs_in_term(_, Term) :-
    (atomic(Term);var(Term)), !, fail.

% If Term is a compound term, check its arguments recursively.
occurs_in_term(SubTerm, Term) :-
    Term =.. [_ | Args], 
    member(Arg, Args),     
    occurs_in_term(SubTerm, Arg), !.
%--------------------------------------------------------------------------------------------------


% Base case: if the term is exactly X, replace it with Y.
replace_term(X, Y, X, Y) :- !.

% If the term is not X and it's an atomic value, leave it as is.
replace_term(_, _, Term, Term) :- atomic(Term), !.

% If the term is a compound term, recursively process its arguments.
replace_term(X, Y, Term, NewTerm) :-
    Term =.. [Functor | Args], % Break the term into its functor and arguments.
    maplist(replace_term(X, Y), Args, NewArgs), % Process each argument.
    NewTerm =.. [Functor | NewArgs]. % Reconstruct the term with replaced arguments.


%--------------------------------------------------------------------------------------------------
positive_equality_term(Term):-
    positive_equality_terms(Term, _, _).

positive_equality_terms(EqualityLiteral, LeftLiteral, RightLiteral):-
    EqualityLiteral =.. ['=', LeftLiteral, RightLiteral],
    !.

positive_equality_terms(EqualityLiteral, LeftLiteral, RightLiteral):-
    EqualityLiteral =.. ['~' | Literal],
    positive_equality_terms(Literal, LeftLiteral, RightLiteral).
%--------------------------------------------------------------------------------------------------
exactly_one_clause_is_false(Literals1, Literals2):-
    true_in_positive_interpretation(Literals1, Result),
    (Result == "TRUE"),
    true_in_negative_interpretation(Literals2, Result),
    (Result == "TRUE"), 
    !.
exactly_one_clause_is_false(Literals1, Literals2):-
    true_in_negative_interpretation(Literals1, Result),
    (Result == "TRUE"),
    true_in_positive_interpretation(Literals2, Result),
    (Result == "TRUE").
%--------------------------------------------------------------------------------------------------
nothing_bigger(ThanThis, InThese):-
    \+ (member(TheBiggerOne, InThese),
        bigger(TheBiggerOne, ThanThis)).

%--------------------------------------------------------------------------------------------------
bigger(BigLiteral, SmallLiteral):-
    % beware, literals can be positive or negative 
    % if 2 things are identical, 
    % p(a) =.. [Symbol|_]
    % @>= or @<=
    no_negation(BigLiteral, BigLiteralClean),
    no_negation(SmallLiteral, SmallLiteralClean),
    % TODO: Add KBO compare instead of compare
    kbo_bigger(BigLiteralClean, SmallLiteralClean).
    %compare(<, BigLiteralClean, SmallLiteralClean).
%--------------------------------------------------------------------------------------------------
no_negation(~A, A):-!.
no_negation(A, A).
%--------------------------------------------------------------------------------------------------
kbo_bigger(BigLiteral, SmallLiteral):-
    kbo_bigger_variable_check(BigLiteral, SmallLiteral),
    kbo_weight(BigLiteral, BigLiteralWeight),
    kbo_weight(SmallLiteral, SmallLiteralWeight),
    (
        (BigLiteralWeight > SmallLiteralWeight)
        ; (BigLiteralWeight == SmallLiteralWeight, compare(<, BigLiteral, SmallLiteral))   % using < bc we want a to be gt b
    ).
%--------------------------------------------------------------------------------------------------
kbo_bigger_variable_check(BigLiteral, SmallLiteral):-
    term_flatten(BigLiteral, FlatBigLiteral),
    term_flatten(SmallLiteral, FlatSmallLiteral),
    only_vars(FlatBigLiteral, BigLiteralVars),
    only_vars(FlatSmallLiteral, SmallLiteralVars),
    % for each member in FlatSmallLiteral, if var, ensure in FlatBigLiteral
    small_all_in_big(SmallLiteralVars, BigLiteralVars).
%--------------------------------------------------------------------------------------------------
kbo_weight(Literal, Weight):-
    term_flatten(Literal, FlatLiteral),
    kbo_length(FlatLiteral, Weight).
%--------------------------------------------------------------------------------------------------
kbo_length(List, Length):- kbo_length(List, 0, Length).
kbo_length([], Length, Length):-
    !.
kbo_length([Head | Tail], CurrentLength, Length):-
    (var(Head) -> (CL is CurrentLength + 1)
    ; (CL is CurrentLength + 2)
    ),
    kbo_length(Tail, CL, Length).
%--------------------------------------------------------------------------------------------------
only_vars([], []):-
    !.

only_vars([Head|Tail], [Head|Vars]) :-
    var(Head), % Check if H is a variable
    !,
    only_vars(Tail, Vars).

only_vars([_|Tail], Vars) :-
    only_vars(Tail, Vars).
%--------------------------------------------------------------------------------------------------
small_all_in_big([],_):-
    !.
small_all_in_big([Head|Tail],BigList):- 
    select(Item, BigList, RestOfBigList), Item == Head,
    !,
    small_all_in_big(Tail,RestOfBigList).
%--------------------------------------------------------------------------------------------------
remove_n(0, List, List):-
    !.

remove_n(N, [_OgHead|OgTail], subsest):-
    N1 is N - 1,
    remove_n(N1, OgTail, subsest).
%--------------------------------------------------------------------------------------------------
%-----Make a literal of opposite sign
opposite_sign_literal(~ Atom,Atom):-
    !.

opposite_sign_literal(Atom,~ Atom).
%--------------------------------------------------------------------------------------------------
% must be EXACTLY opposite literals
% use ==, not = 
% == is identical, = is unifiably identical

% 3 versions of tautology_deletion
    % 1st: empty list
    % 2nd: head clause is a tautology
    % 3rd: head clause is not a tautology
tautology_deletion([],[]).
tautology_deletion([HeadClause|TailClauses], TailClauses):-
    is_tautology(HeadClause),
    tautology_deletion(TailClauses, TailClauses),
    !.
tautology_deletion([HeadClause|TailClauses], [HeadClause|TailClauses]):-
    tautology_deletion(TailClauses, TailClauses).

is_tautology(cnf(_,Literals,_)):-
    %write("Literals:"), write(Literals), nl,
    select(Literal, Literals, RestOfLiterals),
    %write("selected literal: "), write(Literal), nl,
    %write("Rest of literals: "), write(RestOfLiterals),nl,
    opposite_sign_literal(Literal, NegatedLiteral),
    %write("Opposite sign literal: "), write(NegatedLiteral), nl,
    select(OtherLiteral, RestOfLiterals,_),
    %write("Other literal: "), write(OtherLiteral), nl,
    OtherLiteral == NegatedLiteral.


/* tautology_deletion([HeadClause|TailClauses], [NoTautologyHeadClause|NoTautologyTailClauses]):-
    % for each clause, check if there exists a tautology
    tautology_deletion_on_clause(HeadClause, NoTautologyHeadClause),
    tautology_deletion(TailClauses, NoTautologyTailClauses),
    !.

tautology_deletion([], []).
    
tautology_deletion_on_clause(cnf(_,Literals,_), cnf(_,[],0)):-
    % nearly same as factoring (but for inverse), make sure to check == a
    select(Literal, Literals, RestOfLiterals),
    opposite_sign_literal(Literal, NegatedLiteral),
    select(OtherLiteral, RestOfLiterals,_),
    OtherLiteral == NegatedLiteral,!. 

% no deletion for a given clause
tautology_deletion_on_clause(cnf(Name,Literals,Weight), cnf(Name, Literals, Weight)).*/


%==================================================================================================
%----Subsumption code
%==================================================================================================
%--------------------------------------------------------------------------------------------------
%----Do subsumption among a list of clauses
introspective_subsumption([],[]).

%----First clause is subsumed by later ones
introspective_subsumption([FirstClause|RestOfClauses],UnsubsumedClauses):-
    list_subsumption(RestOfClauses,[FirstClause],[]),
    !,
    introspective_subsumption(RestOfClauses,UnsubsumedClauses).

%----Keep first clause, doing backward subsumption on the others
introspective_subsumption([FirstClause|RestOfClauses],[FirstClause|RestOfUnsubsumedClauses]):-
    list_subsumption([FirstClause],RestOfClauses,UnsubsumedRestOfClauses),
    introspective_subsumption(UnsubsumedRestOfClauses,RestOfUnsubsumedClauses).
%--------------------------------------------------------------------------------------------------
forward_subsumption(NewClauses, ToBeUsed, ForwardSubsumedNewClauses):-
    forward_subsumption_TBU(NewClauses, ToBeUsed, ForwardSubsumedTBUNewClauses),
    forward_subsumption_CBU(ForwardSubsumedTBUNewClauses, ForwardSubsumedNewClauses).
    
forward_subsumption_TBU(NewClauses, ToBeUsed, ForwardSubsumedNewClauses):-
    list_subsumption(ToBeUsed, NewClauses, ForwardSubsumedNewClauses).    

forward_subsumption_CBU(ForwardSubsumedTBUNewClauses, ForwardSubsumedNewClauses):-
    database_forward_subsumption(ForwardSubsumedTBUNewClauses, ForwardSubsumedNewClauses).
%--------------------------------------------------------------------------------------------------
backward_subsumption(NewClauses, ToBeUsed, BackwardSubsumedToBeUsed):-
    backward_subsumption_TBU(NewClauses, ToBeUsed, BackwardSubsumedToBeUsed),
    backward_subsumption_CBU(NewClauses). 
    
backward_subsumption_TBU(NewClauses, ToBeUsed, BackwardSubsumedToBeUsed):-
    list_subsumption(NewClauses, ToBeUsed, BackwardSubsumedToBeUsed).

backward_subsumption_CBU(NewClauses):-
    database_backward_subsumption(NewClauses).
%--------------------------------------------------------------------------------------------------


%----Delete members of the 2nd list which are subsumed by members of the first list
% 1st is subsuming, 2nd gets subsumed, 3rd parameter is the cleaned
list_subsumption(_,[],[]).

%----Clause is subsumed, so throw it away. Bit of sneaky optimisation here, moving the subuming 
%----clause to the front so it is used first next time.
list_subsumption(SubsumingClauses,[SubsumedClause|RestOfPotentiallySubsumedClauses],
UnsubsumedClauses):-
    select(SubsumingClause,SubsumingClauses,OtherSubsumingClauses),
    cnf_subsumed(SubsumedClause,SubsumingClause),
    !,
    list_subsumption([SubsumingClause|OtherSubsumingClauses],RestOfPotentiallySubsumedClauses,
UnsubsumedClauses).

%----Not subsumed, so keep it
list_subsumption(SubsumingClauses,[UnsubsumedClause|RestOfPotentiallySubsumedClauses],
[UnsubsumedClause|RestOfUnsubsumedClauses]):-
    list_subsumption(SubsumingClauses,RestOfPotentiallySubsumedClauses,RestOfUnsubsumedClauses).
%--------------------------------------------------------------------------------------------------
%----Check if the clause is subsumed by a member database
% send dirt, get clean
database_forward_subsumption([],[]).

%----Clause is subsumed by a database clause
database_forward_subsumption([SubsumedClause|RestOfPotentiallySubsumedClauses],UnsubsumedClauses):-
    cnf(Name,SubsumingLiterals,_),
    cnf_subsumed(SubsumedClause,cnf(Name,SubsumingLiterals,_)),
    !,
    database_forward_subsumption(RestOfPotentiallySubsumedClauses,UnsubsumedClauses).

database_forward_subsumption([UnsubsumedClause|RestOfPotentiallySubsumedClauses],
[UnsubsumedClause|RestOfUnsubsumedClauses]):-
    database_forward_subsumption(RestOfPotentiallySubsumedClauses,RestOfUnsubsumedClauses).
%--------------------------------------------------------------------------------------------------
%----Delete subsumed clauses from the database
% send clauses, CBU is cleaned
database_backward_subsumption(SubsumingClauses):-
%----Select a subsuming clause from the new clauses and a subsumed clause from the database.
    member(SubsumingClause,SubsumingClauses),
    cnf(Name,SubsumedLiterals,Weight),
%----If not subsumed then backtrack for the next one
    cnf_subsumed(cnf(Name,SubsumedLiterals,Weight),SubsumingClause),
%----If subsumed then retract and backtrack for the next one
    % keep track of retracted clauses for the proof
    assertz(cnf_old(Name, SubsumedLiterals, Weight)),
    retract(cnf(Name,SubsumedLiterals,Weight)),
    fail.

%----When no more can be removed, just succeed
database_backward_subsumption(_).
%--------------------------------------------------------------------------------------------------
%----Others are two clauses.
cnf_subsumed(cnf(_,SubsumedLiterals,_),cnf(_,SubsumingLiterals,_)):-
%----Enforce theta rule for length
%    length(SubsumedLiterals,SubsumedLength),
%    length(SubsumingLiterals,SubsumingLength),
%    SubsumedLength >= SubsumingLength,
%----Put in a verify to avoid instantiation
    \+ \+ (
        numbervars(SubsumedLiterals,0,_),
        all_atp_literals(SubsumingLiterals,SubsumedLiterals)).
%--------------------------------------------------------------------------------------------------
%----Check that all the literals in the subsuming list are literals in the subsumed list
all_atp_literals([],_).

all_atp_literals([FirstLiteral|RestOfSubsumingLiterals],SubsumedLiterals):-
    member(FirstLiteral,SubsumedLiterals),
    all_atp_literals(RestOfSubsumingLiterals,SubsumedLiterals).

%----Uncomment these if you have built in equality reasoning
%all_atp_literals([(LHS = RHS)|RestOfSubsumingLiterals],SubsumedLiterals):-
%    member((RHS = LHS),SubsumedLiterals),
%    all_atp_literals(RestOfSubsumingLiterals,SubsumedLiterals).
%
%all_atp_literals([~(LHS = RHS)|RestOfSubsumingLiterals],SubsumedLiterals):-
%    member(~(RHS = LHS),SubsumedLiterals),
%    all_atp_literals(RestOfSubsumingLiterals,SubsumedLiterals).
%--------------------------------------------------------------------------------------------------
%==================================================================================================
%----This module holds the clauses for reading input sets in TPTP format.
%==================================================================================================
%--------------------------------------------------------------------------------------------------
%----Read input clauses from a file, doing includes too
read_cnfs_from_file(FileName,InputClauses):-
    tptp_path_name(FileName,PathName),
    (PathName \== user -> (
        current_input(CurrentInput),
        open(PathName,read,InputStream),
        set_input(InputStream))
    ;   true),
%----Read in the clauses, doing includes
    read_cnfs(InputClauses),
%----Cut, so that later errors do not try to read more input clauses
    !,
%----Restore output direction
    (PathName \== user -> (
        close(InputStream),
        set_input(CurrentInput))
    ;   true).
%--------------------------------------------------------------------------------------------------
%----Read in clauses from current input device, until eof
read_cnfs(InputClauses):-
    read(PrologTerm),
    \+ (PrologTerm == end_of_file),
    !,
%----Check if an include, and return all clauses resulting
    filter_for_clauses(PrologTerm,InputClauseList),
    read_cnfs(RestOfClauses),
    append(InputClauseList,RestOfClauses,InputClauses).

read_cnfs([]).
%--------------------------------------------------------------------------------------------------
%----Determine what to do with the term read.
filter_for_clauses(cnf(Name,_Status,Literals),[cnf(Name,ListOfLiterals,weight)]):-
    !,
    convert_clause_to_list(Literals,ListOfRawLiterals),
    convert_equality(ListOfRawLiterals,ListOfLiterals).
    
%----Include directive cause recursive call to the top level to read the included file.
filter_for_clauses(include(FileName),InputClauses):-
    !,
    read_cnfs_from_file(FileName,InputClauses).
%--------------------------------------------------------------------------------------------------
convert_clause_to_list((LHS | RHS),Literals):-
    !,
    convert_clause_to_list(LHS,LHSLiterals),
    convert_clause_to_list(RHS,RHSLiterals),
    append(LHSLiterals,RHSLiterals,Literals).

convert_clause_to_list(Literal,[Literal]).
%--------------------------------------------------------------------------------------------------
%----Convert equality
convert_equality([],[]).

convert_equality([FirstLiteral|RestOfLiterals],[FirstConvertedLiteral|RestOfConvertedLiterals]):-
    !,
    convert_equality(FirstLiteral,FirstConvertedLiteral),
    convert_equality(RestOfLiterals,RestOfConvertedLiterals).

%----Special hack for !=, with ! as a postfix operator
convert_equality(LHS = RHS,~ (RealLHS = RHS)):-
    nonvar(LHS),
    LHS = !(RealLHS),
    !.

convert_equality(~ Atom,~ ConvertedAtom):-
    !,
    convert_equality(Atom,ConvertedAtom).

convert_equality(Atom,Atom).
%--------------------------------------------------------------------------------------------------
%----Make a completed path name from the TPTP directory and the file name. If the pathname is user, 
%----then do nothing.
tptp_path_name(user,user):-
    !.

%----If the file exists locally, then add nothing
tptp_path_name(FileName,FileName):-
%Eclipse    exists(FileName),
    exists_file(FileName),
    !.

%----If leading Axioms, then prepend TPTP
tptp_path_name(AxiomIncludeName,PathName):-
    atom_chars(AxiomIncludeName,['A','x','i','o','m','s','/'|_]),
    !,
    tptp_directory(Directory),
    atomic_list_concat([Directory,'/',AxiomIncludeName],PathName).

%----If no leading /, then put the TPTP directory + Problems + domain on front
tptp_path_name(FileName,PathName):-
    atom_chars(FileName,[C1,C2,C3|RestFileNameChars]),
    atom_chars(Domain,[C1,C2,C3]),
    (   append(_,['.','p'],RestFileNameChars)
    ->  FullFileName = FileName
    ;   atom_concat(FileName,'.p',FullFileName) ),
    tptp_directory(Directory),
    atomic_list_concat([Directory,'/Problems/',Domain,'/',FullFileName],PathName).
%--------------------------------------------------------------------------------------------------
increment_id():-
    nb_getval(next_id, V),
    Z is V + 1,
    nb_setval(next_id, Z).

n_pricep(Clause, ID-Clause):-
   get_name_from_clause(Clause, [ID | _]).

pair_value(_-V,V).