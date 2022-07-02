:- use_module('skip_pattern_compiler.pl').
:- use_module('so_auto_cp.pl').
:- use_module('pattern.pl').
:- use_module('read_patterns.pl').
:- use_module('auto_noskip.pl').
:- use_module('auto_noskip_conc.pl').
:- use_module(library(statistics)).
:- use_module(library(csv)).
:- use_module(library(clpfd)).


run_(Id1-Id2, Matcher, L-MTrees, Lambda-MaxLen)
    :-  call(Matcher, Id1, _, L1, MTrees0,
            [output(out(D, M)), max_depth(MaxLen), input(inp(lambda(Lambda)))]),
        call(Matcher, Id2, L1, L, MTrees,
            [input(inp(D, M, lambda(Lambda))), 
             inmtrees(MTrees0), max_depth(MaxLen)]), !.

fixed_test(Ids, Type, Matcher, Lambda-MaxLen, _, Row) 
      :- call_time(run_(Ids, Matcher, _, Lambda-MaxLen), S),
         Row = row(Matcher, Type, MaxLen, Lambda, S.wall, S.cpu, S.inferences),
         print(Row), nl.

fixed_tests(Ids, Type, Matcher, t(N, Pair), Rows)
    :- length(L, N),
       maplist(fixed_test(Ids, Type, Matcher, Pair), L, Rows).

matcher_tests(Ids,  Type, m(Matcher, Tests), Rows)
    :- maplist(fixed_tests(Ids, Type, Matcher), Tests, Rows0),
       append(Rows0, Rows).

matchers_tests(Ids, Type, MTests, Rows)
    :- maplist(matcher_tests(Ids, Type), MTests, Rows0),
       append(Rows0, Rows).

make_test_(N, Lambda, Max, t(N, Lambda-Max)).
make_tests_(N, Lambda-Maxs, Tests)
    :- maplist(make_test_(N, Lambda), Maxs, Tests).
make_tests(N, Pairs, Tests)
    :- maplist(make_tests_(N), Pairs, Testss),
       append(Testss, Tests).
  
files('example_data.pl', 'aux_types_data.pl', 'raw_mesurements.csv').
ids(100-101).
mtests(
    [
        m('match_list', MatchList),
        m('match_list_ns', MatchListNS),
        m('match_list_nsc', MatchListNSCBasic)
    ],
    [
        m('match_list', MatchList),
        m('match_list_ns', MatchListNS),
        m('match_list_nsc', MatchListNSCExt)
    ]
) :- make_tests(5, [
        1-[3, 5, 10, 20, 30, 40, 50],
        2-[5, 10, 20, 30, 40, 50],
        5-[12, 20, 30, 40, 50],
        10-[22, 30, 40, 50],
        15-[32, 40, 50],
        20-[42, 50, 60],
        25-[52, 60],
        30-[62]
     ], MatchList),
     make_tests(5, [
        1-[3, 5, 10, 12, 14, 16, 18],
        2-[5, 10, 12, 14, 16, 18],
        3-[10, 12, 14, 16, 18],
        4-[10, 12, 14, 16, 18],
        5-[12, 14, 16, 18],
        6-[14, 16, 18],
        7-[16, 18],
        8-[18]
     ], MatchListNS),
     make_tests(5, [
        1-[3, 4, 5, 6],
        2-[5, 6, 7],
        3-[7, 8],
        4-[9]
     ], MatchListNSCBasic),
     make_tests(5, [
        1-[3,4,5],
        2-[5,6],
        3-[7]
     ], MatchListNSCExt).

all_tests 
    :- files(Input, Aux, Out),
       ids(Ids),
       mtests(Tests, AuxTests),
       assert_file(Input),
       compile_patterns,
       print('Starting basic tests'), nl,
       matchers_tests(Ids, basic, Tests, Rows1),
       print('Reading auxilliary type definitions'), nl,
       assert_file(Aux),
       print('Starting auxilliary tests'), nl,
       matchers_tests(Ids, aux, AuxTests, Rows2),
       append(Rows1, Rows2, Rows0),
       Rows = [
            row('matcher', 'ntypes', 'max_len', 
                'lambda', 'wall', 'cpu', 'inferences')|Rows0],
       print('Saving csv file'), nl,
       csv_write_file(Out, Rows),
       print('Halting the interpreter ...'), nl,
       halt.

:- all_tests.
       
