:- module(so_auto_cp, [
      match_list/5, 
      initial/3, 
      final/2, 
      trans/4, 
      eps/2, 
      skip/2,
      squash/2,
      pos_tree_new_/3
]).

:- use_module(library(clpfd)).
%:- use_module('skip_pattern_compiler.pl').
:- use_module('event_types.pl').
:- use_module('skippable.pl').
%:- use_module('time_constr.pl').
:- use_module(library(option)).

:- dynamic initial/3, final/2, trans/4, eps/2, skip/2.


move_ins_outs(Move, TList-RList, IList-OutList)
    :- maplist(move_inp_tail_rec_out(Move), IList, TList, RList, OutList).

move_inp_tail_rec_out(id, [I|Tail], Tail, Rec, [I|Rec]).
move_inp_tail_rec_out(end, [skip|Tail], Tail, Rec, [skip, skip | Rec]).
move_inp_tail_rec_out(mid, [I|Tail], [skip|Tail], Rec, [skip, I | Rec]).
 

/*
    Some runtime helpers for computing aggregate functions min and max
 */

ext_min(nothing, X, m(X)).
ext_min(m(X), Y, m(Z)) :- Z #= min(X, Y).

ext_max(nothing, X, m(X)).
ext_max(m(X), Y, m(Z)) :- Z #= max(X, Y).

fin_minmax(m(X), X).
update_avg(a(Sum0, Count0), E, a(Sum, Count))
   :- Sum #= Sum0 + E, Count #= Count0 + 1.
fin_avg(a(Sum, Count), Avg) :- Avg #= Sum // Count.

/*
     This module describes automaton recognizing patterns on lists with output.
     The automaton is defined by the following predicates:
     initial(Id, I, Input) : initial state I for automaton Id
     final(F, Output) : final state F
     trans(S0, A, Node, S1) : automaton can do transition after consuming A from state
     S0 to S1
     eps(S0, P, S1) : automaton can do ε - transition. P is skip except when the 
                      transition in question implements start(X): then it is a position 
                      of start(X).
     skip(S, A) : automaton can skip A when in a state S.
 */

state(T), [T] --> [T].
state(T0, T1), [T1] --> [T0].
state_consume(S0, S1, A)
    --> state(
            a(S0, _, T0, C0, MaxLen), 
            a(S1, [], T, C1, MaxLen)
        ), 
        {
            C0 < MaxLen,
            C1 is C0 + 1,
            T0 #< T,
            S1 =..[_, _, T|_]
            %event_time(A, T)
        }.

eps_([], S0 , P, S1, [S1, S0])
   :- eps(S0, P, S1),
      dif(S0, S1). 

eps_([S0|Acc], S0, P, S1, [S1, S0|Acc])
   :- eps(S0, P, S1),
      maplist(dif(S1), [S0|Acc]).

match_list(Id, L0, L, MTrees, Options)
   :- option(input(Input), Options, in),
      option(output(Output), Options, out),
      option(inmtrees(MTreesIn), Options, []),
      option(max_depth(MaxLen), Options, 20),
      initial(Id, Input, I),
      phrase(
         matcher(L0, L, MTreesIn-MTreesOut, MTree0), 
         [a(I, [], 0, 0, MaxLen)], 
         [a(S, _, T, _, _)]
      ),
      attr_dom(time, T),
      final(S, Output),
      squash(MTree0, MTree),
      append(MTreesOut, [MTree], MTrees). 

squash(X, X) :- var(X), !.
squash([], []).
squash([skip|Ps0], [skip|Ps]) :- !, squash(Ps0, Ps).
squash([start(_)|Ps0], Ps) :- !, squash(Ps0, Ps).
squash([pos(L)|Ps0], [P|Ps]) :- squash_(Ps0, pos(L), P, Ps).
squash_(X, P, P, X) :- var(X), !.
squash_([], P, P,  []) :- !.
squash_([skip|Ps0], P, P, Ps) :- !, squash([skip|Ps0], Ps).
squash_([pos(L)|Ps0], P, P, Ps) :- !, squash([pos(L)|Ps0], Ps).
squash_([start(L0)|Ps0], pos(L), P, Ps)
   :- !, squash_([start(L0)|Ps0], pos(L,[]), P, Ps).
squash_([start(L0)|Ps0], pos(L,Ls), P, Ps)
   :- squash_(Ps0, pos(L, [pos(L0)|Ls]), P, Ps).

pos_tree_new_(skip, MTree, MTree) :- !.
pos_tree_new_(pos(L), MTree, [start(L)|MTree]).

is_event_(A) :- nonvar(A), !.
is_event_(A) :- get_attr(A, any_event, _).

make_skips_(State, L0, L, MTree)
   :- phrase(make_skips(L0, L, MTree), State, _).

make_skips(L0, L, _) --> {var(L0), !, copy_term(L0, L)}.
make_skips([], [], []) --> !.
make_skips([A|L0], [A|L], [skip|MTree])
   --> {is_event_(A)}, !, 
       state_consume(S, S, A),
       make_skips(L0, L, MTree).
make_skips([A|L0], [A|L], [skip|MTree])
   --> make_skips(L0, L, MTree).

matcher(L0, L, MTreesIn-MTreesIn, MTree) 
   --> state(a(S, _, _, _, _)),
      {final(S, _)},
      make_skips(L0, L, MTree).


matcher(L0, L, MTrees, MTree)
   --> advance(L0, L1, L2, L, MTrees0, MTrees, MTree0, MTree),
       matcher(L1, L2, MTrees0, MTree0).

matcher(L0, L, MTrees, MTree)
   --> state(
         a(S0, Acc0, T, C, MaxLen), 
         a(S1, Acc1, T, C, MaxLen)
       ),
       {
         eps_(Acc0, S0, P, S1, Acc1)
       },
       matcher(L0, L, MTrees, MTree0),
       {
         pos_tree_new_(P, MTree0, MTree)
       }.

advance(L0, L1, L2, L, MTrees0, MTrees, MTree0, MTree)
   --> {var(L0), !, L0 = [A | L1]},
       state_consume(S0, S1, A),
       {
         trans(S0, A, Node, S1),
         skip(S0, X),
         move_ins_outs(end, MTrees0, MTrees),
         L = [X, A | L2],
         MTree = [skip, Node | MTree0]
       }.

advance([A | L0], L1, L2, L, MTrees0, MTrees, MTree0, MTree)
   --> take_item(A, L0, L1, L2, L, MTrees0, MTrees, MTree0, MTree).

take_item(A, L1, L1, L2, L, MTrees0, MTrees, MTree0, MTree)
   --> {is_event_(A), !},
       take_event(A, L1, L2, L, MTrees0, MTrees, MTree0, MTree).

take_item(A, L0, L1, L2, L, MTrees0, MTrees, MTree0, MTree)
   --> take_non_event(A, L0, L1, L2, L, MTrees0, MTrees, MTree0, MTree).

take_event(A, _, L2, [A | L2], MTrees0, MTrees, MTree0, [Node | MTree0])
   --> state_consume(S0, S1, A),
      {  
         trans(S0, A, Node, S1),
         move_ins_outs(id, MTrees0, MTrees)
      }.

take_event(A, _, L2, [A | L2], MTrees0, MTrees, MTree0, [skip | MTree0])
--> state_consume(S, S, A),
   {  
      skip(S, A),
      move_ins_outs(id, MTrees0, MTrees)
   }.

take_non_event(A, L0, L1, L2, L, MTrees0, MTrees, MTree0, [skip, Node | MTree0])
   --> state_consume(S0, S1, Z),
       {
         copy_term(A, X),
         copy_term(A, Y),
         trans(S0, A, Node, S1),
         A = Z,
         skip(S0, X),
         move_ins_outs(mid, MTrees0, MTrees),
         L1 = [Y | L0],
         L = [X, A | L2]
       }.

take_non_event(A, L1, L1, L2, [A | L2], MTrees0, MTrees, MTree0, [skip | MTree0])
   --> state(a(S, _, _, _, _)),
       {
         skip(S, A),
         move_ins_outs(id, MTrees0, MTrees)
       }.
  
