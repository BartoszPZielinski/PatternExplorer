:- module(auto_noskip, [match_list_ns/4]).

:- use_module(library(clpfd)).
:- use_module('../event_types.pl').
:- use_module('../skippable.pl').
:- use_module('../so_auto_cp.pl').

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


eps_(S0-[], S1-[S1, S0])
   :- eps(S0,  S1),
      dif(S0, S1). 

eps_(S0-[S0|Acc], S1-[S1, S0|Acc])
   :- eps(S0, S1),
      maplist(dif(S1), [S0|Acc]).

match_list_ns(Id, L, MTree, Input)
   :- initial(Id, Input, I),
      matcher_ns(L, MTree, I-[], _).

matcher_ns(_, [], S-Acc, S-Acc) :- final(S, _). 

matcher_ns([A|L0], [Node | MTree0], S0-_, X)
   :- trans(S0, A, Node, S1),
      matcher_ns(L0, MTree0, S1-[], X).

matcher_ns(L, MTree, X0, X)
   :- eps_(X0, X1),
      matcher_ns(L, MTree, X1, X).

matcher_ns([A|L], [skip|MTree], S-Acc, X)
   :- skip(S, A),
      matcher_ns(L, MTree, S-Acc, X).   
