:- module(pattern, [
        pattern/3,
        example/3,
        get_patterns/1,
        get_examples/1,
        compile_pattern/1,
        compile_patterns/0,
        run/3,
        solutions/4,
        numbered_solutions/4
    ]). 

:- use_module('skip_pattern_syntax.pl').
:- use_module('skip_pattern_compiler.pl').
:- use_module('so_auto_cp.pl').

:- dynamic pattern/3.
:- dynamic example/3.
:- multifile pattern/3.
:- multifile example/3.

get_patterns(Patterns)
    :- findall(
          pattern(Id, Pattern, Vars), 
          pattern(Id, Pattern, Vars), 
          Patterns
       ).

get_examples(Examples)
    :- findall(example(Id, Example, Vars), example(Id, Example, Vars), Examples).

compile_patterns
    :- (pattern(Id, _, _), compile_pattern(Id), false) ; true.

compile_pattern(I)
:-   pattern(I, Pattern0, _), 
     make_pattern_unique_o(Pattern0, Pattern),
     assert_regular(I, Pattern),
     format('Pattern ~w compiled ~n', [I]).

%nums_to_(Min, Min, Max) :- Min < Max.
%nums_to_(N, Min, Max) 
%    :- Min < Max, nums_to_(N0, Max), N is N0 + 1, (N < Max ; (N>=Max, !)).
%nums_to_(N, Max) :- nums_to_(N, 1, Max).

nums_to_(1, Max) :- 1 =< Max.
nums_to_(N, Max) 
    :- 1 < Max, nums_to_(N0, Max), N is N0 + 1, (N < Max ; (N>=Max, !)).

%
%nums_to_(N, N).

run(ExId, MaxLen, L-MTrees)
    :- example(ExId, ex(Pid1, In1-Out1-In2, Pid2), _),
        nums_to_(Len1, MaxLen),
        write(user_error, 'Len1='), writeln(user_error, Len1),
        match_list(Pid1, _, L0, MTrees0, [input(In1), output(Out1),max_depth(Len1)]),
        nums_to_(Len2, MaxLen),
        write(user_error, 'Len2='), writeln(user_error, Len2),
        match_list(Pid2, L0, L, MTrees, 
            [input(In2), inmtrees(MTrees0), max_depth(Len2)]),
        writeln(user_error, 'success'). 

run(ExId, MaxLen, L-MTrees)
    :- example(ExId, ex(Pid1, Out-In, Pid2), _),
       nums_to_(Len1, MaxLen),
       match_list(Pid1, _, L0, MTrees0, [output(Out),max_depth(Len1)]),
       nums_to_(Len2, MaxLen),
       match_list(Pid2, L0, L, MTrees, 
           [input(In), inmtrees(MTrees0), max_depth(Len2)]). 

run(ExId, MaxLen, L-MTrees)
    :- example(ExId, ex(Pid, In), _),
       nums_to_(Len, MaxLen),
       match_list(Pid, _, L, MTrees, [max_depth(Len), input(In), output(_)]). 

run(ExId, MaxLen, L-MTrees)
:- example(ExId, ex(Pid), _),
   nums_to_(Len, MaxLen),
   match_list(Pid, _, L, MTrees, [max_depth(Len), output(_)]).

solutions(ExId, MaxLen, NSols, Sols)
    :- findnsols(NSols, sol(L, MTrees, Goals), (
            run(ExId, MaxLen, L0-MTrees0),
            copy_term(L0-MTrees0, L-MTrees, Goals)
        ), Sols).

number_solutions(_, [], []).
number_solutions(
    N0, 
    [sol(L, MTrees, Goals) | Sols0],
    [sol(N0, SidAtom, L, MTrees, Goals) | Sols]
) :- N is N0 + 1, 
     atom_concat('s_', N0, SidAtom),
     number_solutions(N, Sols0, Sols).

numbered_solutions(ExId, MaxLen, NSols, Sols)
    :- solutions(ExId, MaxLen, NSols, Sols0),
       number_solutions(1, Sols0, Sols).
