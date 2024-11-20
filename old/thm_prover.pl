%==================================================================================================
%----General ANL Loop style theorem prover. This is the overall control code, non-specific to a 
%----particular calculus
%==================================================================================================
%Eclipse :-use_module(library(iso)).
%Eclipse :-use_module(library(numbervars)).
%Eclipse :-set_flag(occur_check,on).
:-use_module(library(time)).    %%swi
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
    write("InitialisedClauses:"), write(InitialisedClauses),nl,
    StartTime is cputime,
    call_with_time_limit(
        TimeLimit,
        catch(atp_loop(InitialisedClauses,0,Loops,SZSResult,Refutation),SWIError,
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
        write(Refutation),nl,
        write('% SZS output end Refutation for '),
        write(FileName),nl
      ) ; 
        true 
    ),
    write('%--------------------------------------------------------'),nl,
    !.
%--------------------------------------------------------------------------------------------------
swi_error_to_SZS(time_limit_exceeded,'Timeout').

swi_error_to_SZS(error(resource_error(_),_),'ResourceOut').
%--------------------------------------------------------------------------------------------------
initialise_deduction(FileName,ProblemClauses):-
write('IN INITIALISE DEDUCTION'),nl,
    retractall(cnf(_,_,_)),
write('\tRetract all successful'),nl,
    read_cnfs_from_file(FileName, ReadClauses), 
write('\tread_cnfs_from_file successful'),nl,
    weigh_clauses(ReadClauses, WeighedClauses),
write('\tweigh_clauses_successful'),nl,
    sort(3, @=<, WeighedClauses, ProblemClauses),
write('\tsort clauses successful'),nl.
%--------------------------------------------------------------------------------------------------
weigh_clauses([], []):-
write('IN WEIGH CLAUSES BASE CASE'),nl.


weigh_clauses([cnf(Name, Literals,_)|Tail],[cnf(Name,Literals,Weight)|WeightedTail]):-
write('IN WEIGH CLAUSES'),nl,
    term_flatten(Literals, FlatList),
write('\tterm_flatten successful'),nl,
write('\tFlatList'), write(FlatList),nl,
    length(FlatList, Weight),
write('\tlength successful'),nl,
write('\tTail:'), write(Tail), nl,
    weigh_clauses(Tail, WeightedTail),
write('\tWeighted Tail:'), write(WeightedTail), nl,
write('\trecursive weigh_clauses successful'),nl.

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

%----Test if a proof has been found
atp_loop(ToBeUsed,Loops,Loops,'Unsatisfiable',Proof):-
    member(cnf(Proof,[],_),ToBeUsed),
    !.

%----Test if no proof can be found
atp_loop([],Loops,Loops,'Satisfiable',none):-
    !.

%----Take first to_be_used clause and do inferences 
atp_loop([ChosenClause|RestOfToBeUsed],LoopsSoFar,FinalLoops,SZSResult,Refutation):-
write('----ToBeUsed is'),write([ChosenClause|RestOfToBeUsed]),nl,
%----Move the to_be_used clause to can_be_used
    add_to_can_be_used(ChosenClause),
write('added to can be used'),nl,
%----Do all possible inferences
    findall(NewClause,do_inference(ChosenClause,NewClause),NewClauses),
write('found clauses:'),write(NewClauses),nl,
    weigh_clauses(NewClauses, WeighedNewClauses),
write('----The new clauses are'),write(WeighedNewClauses),nl,
%----Create new to_be_used list and loop. Breadth first search
    append(RestOfToBeUsed,WeighedNewClauses,NewToBeUsed),
    sort(3, @=<, NewToBeUsed, WeighedNewToBeUsed),
%----Go round the loop. Note this should be tail recursion optimized. If it's not then buy a 
%----better Prolog or place a cut here.
    OneMoreLoop is LoopsSoFar + 1,
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
do_inference(cnf(ChosenName,ChosenClauseLiterals,_),cnf(r(ChosenName, CBUName),ResolvantLiterals,weight)):-
write('IN DO_INFERENCE'),nl,
%----Select literal from first parent clause
    select(SelectedLiteral,ChosenClauseLiterals,RestOfChosenClauseLiterals),
write('\tselected literal:'), write(SelectedLiteral),nl,
%----Make opposite sign literal required for other parent
    opposite_sign_literal(SelectedLiteral,NegatedSelectedLiteral),
write('\topposite sign literal:'), write(NegatedSelectedLiteral),nl,
%----Look for other parent in database
    cnf(_,CBUClauseLiterals,_),
write('\tfound parent'),nl,
write('\tCBUName: '), write(CBUName),nl,
write('\tCBUCluaseLiterals'), write(CBUClauseLiterals), nl,
%----Select literal of opposite sign that unifies, from the second parent
    select(NegatedSelectedLiteral,CBUClauseLiterals,RestOfCBUClauseLiterals),
write('\tRestOfCBUClauseLiterals'), write(RestOfCBUClauseLiterals),nl,
%----Collect the leftover literals
    append(RestOfChosenClauseLiterals,RestOfCBUClauseLiterals,ResolvantLiterals).

%----If you add binary factoring, you need to enable theta-subsumption below
%do_inference(cnf(ChosenName,ChosenClauseLiterals,_),cnf(f(ChosenName),FactoredLiterals,weight)):-
    %select(FactoredLiteral, ChosenClauseLiterals, FactoredLiterals), 
    %-- TODO: Only check elements that are later in the list, not before FactoredLiterals 
    %-- likely can use by comparing nth0(Index, List, Elem)
    %member(FactoredLiteral, FactoredLiterals).

%--------------------------------------------------------------------------------------------------
%-----Make a literal of opposite sign
opposite_sign_literal(~ Atom,Atom):-
    !.

opposite_sign_literal(Atom,~ Atom).
%--------------------------------------------------------------------------------------------------
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
%----Delete members of the 2nd list which are subsumed by members of the first list
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
database_backward_subsumption(SubsumingClauses):-
%----Select a subsuming clause from the new clauses and a subsumed clause from the database.
    member(SubsumingClause,SubsumingClauses),
    cnf(Name,SubsumedLiterals,Weight),
%----If not subsumed then backtrack for the next one
    cnf_subsumed(cnf(Name,SubsumedLiterals,Weight),SubsumingClause),
%----If subsumed then retract and backtrack for the next one
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