:- module(auto_noskip, [match_list_ns/5]).

:- use_module(library(clpfd)).
%:- use_module('skip_pattern_compiler.pl').
:- use_module('event_types.pl').
:- use_module('skippable.pl').
:- use_module('so_auto_cp.pl').
:- use_module('time_constr.pl').
:- use_module(library(option)).

/*
     This module describes automaton recognizing patterns on lists with output.
     The automaton is defined by the following predicates:
     initial(Id, I, Input) : initial state I for automaton Id
     final(F, Output) : final state F
     trans(S0, A, Node, S1) : automaton can do transition after consuming A from state
     S0 to S1
     eps(S0, S1) : automaton can do ε - transition
     skip(S, A) : automaton can skip A when in a state S.
 */

state(T), [T] --> [T].
state(T0, T1), [T1] --> [T0].
state_consume(S0, S1, Event)
    --> state(
            a(S0, _, T0, C0, MaxLen), 
            a(S1, [], T, C1, MaxLen)
        ), 
        {
            C1 = C0 + 1,
            C0 < MaxLen,
            T0 #< T,
            event_time(Event, T)
        }.

eps_(S0, [], S1, [S1, S0])
   :- eps(S0, S1),
      dif(S0, S1). 

eps_(S0, [S0|Acc], S1, [S1, S0|Acc])
   :- eps(S0, S1),
      maplist(dif(S1), [S0|Acc]).

match_list_ns(Id, L0, L, MTrees, Options)
   :- option(input(Input), Options, in),
      option(output(Output), Options, out),
      option(inmtrees(MTreesIn), Options, []),
      option(max_depth(MaxLen), Options, 20),
      initial(Id, Input, I),
      phrase(
         matcher_ns(L0, L, MTreesIn-MTreesOut, MTree), 
         [a(I, [], 0, 0, MaxLen)], 
         [a(S, _, T, _, _)]
      ),
      attr_dom(time, T),
      final(S, Output),
      append(MTreesOut, [MTree], MTrees). 

make_skips(L0, L, _) --> {var(L0), !, copy_term(L0, L)}.
make_skips([], [], []) --> !.
make_skips([A|L0], [A|L], [skip|MTree])
   --> {visited_(A)}, !, 
        state_consume(S, S, A),
        make_skips(L0, L, MTree).

move_ins_outs(A, TList-RList, IList-OutList)
   :- visited(A, Move),
      maplist(move_inp_tail_rec_out(Move), IList, TList, RList, OutList).

move_inp_tail_rec_out(id, [I|Tail], Tail, Rec, [I|Rec]).
move_inp_tail_rec_out(end, [skip|Tail], Tail, Rec, [skip | Rec]).

visited_(A) :- nonvar(A), !.
visited_(A) :- var(A), get_attr(A, any_event, _), !.
visited_(A) :- var(A), get_attr(A, skippable, _).

visited(A, id) :- visited_(A), !.
visited(_, end).

matcher_ns(L0, L, MTreesIn-MTreesIn, MTree) 
--> state(a(S, _, _, _, _)),
      {final(S, _)},
      make_skips(L0, L, MTree).

matcher_ns([A|L0], [A|L], MTrees, [Node | MTree])
   --> state_consume(S0, S1, A),
       {
         trans(S0, A, Node, S1),
         move_ins_outs(A, MTrees0, MTrees)
       },
       matcher_ns(L0, L, MTrees0, MTree).

matcher_ns(L0, L, MTrees, MTree)
   --> state(
         a(S0, Acc0, T, C, MaxLen), 
         a(S1, Acc1, T, C, MaxLen)
       ),
       {
          eps_(S0, Acc0, S1, Acc1)
       },
       matcher_ns(L0, L, MTrees, MTree).

matcher_ns([A|L0], [A|L], MTrees, [skip|MTree])
   --> state_consume(S, S, A),
       {
          skip(S, A),
          move_ins_outs(A, MTrees0, MTrees)
       },
       matcher_ns(L0, L,  MTrees0, MTree).

% :- assert(event_types:event_type(s(_), s)).   
