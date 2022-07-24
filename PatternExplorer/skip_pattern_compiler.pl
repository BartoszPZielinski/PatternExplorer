:- module(skip_pattern_compiler, [
     assert_regular/2
]).

:- use_module(library(clpfd)).
:- use_module(library(ordsets)).
:- use_module(library(varnumbers)).
:- use_module(library(pairs)).
:- use_module('skip_pattern_syntax.pl').
:- use_module('compiler_state.pl').
:- use_module('compiler_helpers.pl').
:- use_module('skippable.pl').
:- use_module('event_types.pl').


/*
    Automatons are represented (during compilation) by dicts of the form
    auto{
         transitions: [trans(V, Type, pos([L]), S0, S1):-G, ...],
         epses: [eps(S0, StartPos, S1), ...],
         skips: [skip(S, V1, event_specs), ...],
         initial: S,
         final: [S, ...]
    }
    where event_specs is a list of pairs type-condition.
    An event E is skippable in state S0 iff its type either is not on the list skips or it is 
    and then the condition is satisfied. The variable V1 is used
    to refer to the event under consideration in all the conditions.
   StartPos in eps is the position of the form pos(L) of start(X) subterm if the given eps corresponds 
   to saving the value of a last matched event in a variable. It is skip 
   otherwise.
*/

compile_query_pure(Id, Pattern, M0, Vs, Automaton)
    :- %numbervars(Pattern, 0, M0),
       init_state(M0, Id, Vs, InitialState),
       %format('Initial state ~w~n', [InitialState]),
       phrase(comp_aut(Pattern, Automaton), InitialState, [_]).

appends_bin_(Auto1, Auto2, Ts, Es, Skips)
   :- append_poss(p(1), Auto1.transitions, T1),
      append_poss(p(2), Auto2.transitions, T2),
      append_poss(p(1), Auto1.epses, Es01),
      append_poss(p(2), Auto2.epses, Es02),
      append(T1, T2, Ts),
      append(Es01, Es02, Es),
      append(Auto1.skips, Auto2.skips, Skips).

comp_aut(
   start(V), auto{
        transitions: [],
        epses: [(eps(S0, pos([]), S1) :- V = LastMatched)],
        initial: S0,
        skips: [],
        final: [S1]
   }) 
   --> last_matched(LastMatched),
       replace_vars(Vs0, Vs),
       {ord_add_element(Vs0, V, Vs)},
       fresh_states([S0, S1], [Vs0, Vs]). 

comp_aut(
   any(V), auto{
        transitions: [(trans(V, any, pos([]), S0, S2) :- true)],
        epses: [],
        initial: S0,
        skips: [skip(S0, V1, [])],
        final: [S1]
   }) 
   --> fresh_var(V1),
       replace_vars(Vs0, Vs),
       {ord_add_element(Vs0, V, Vs)},
       fresh_states([S0, S1], [Vs0, Vs]),
       {matched_state_push(V, S1, S2)}.

comp_aut(
   event(Type, V), auto{
        transitions: [(trans(V, Type, pos([]), S0, S2) :- true)],
        epses: [],
        initial: S0,
        skips: [skip(S0, V1, [])],
        final: [S1]
   }) 
   --> fresh_var(V1),
       replace_vars(Vs0, Vs),
       {ord_add_element(Vs0, V, Vs)},
       fresh_states([S0, S1], [Vs0, Vs]),
       {matched_state_push(V, S1, S2)}.

comp_aut(P1 then P2, auto{
   transitions: Ts,
   epses: Es,
   initial: I,
   skips: Skips,
   final: F
})
--> 
    comp_aut(P1, Auto1),
    comp_aut(P2, Auto2),
    {
      I = Auto1.initial,
      F = Auto2.final,
      appends_bin_(Auto1, Auto2, Ts, Es0, Skips),
      sources_target_acc_epses(Auto1.final, Auto2.initial, Es0, Es)
    }.

comp_aut(P1 or P2, auto{
   transitions: Ts,
   epses: [(eps(S0, skip, I1) :- true), (eps(S0, skip, I2) :- true)|Es],
   skips: Skips,
   initial: S0,
   final: Fs
})
   --> current_vars(Vs0),
       comp_aut(P1, Auto1),
       replace_vars(Vs1, Vs0),
       comp_aut(P2, Auto2),
       replace_vars(Vs2, Vs),
       {
          I1 = Auto1.initial,
          I2 = Auto2.initial,
          ord_intersection(Vs1, Vs2, Vs),
          appends_bin_(Auto1, Auto2, Ts, Es, Skips),
          append(Auto1.final, Auto2.final, Fs)
       },
       fresh_state(S0, Vs0).

comp_aut(P1 and P2, auto{
   transitions: Trans,
   epses: [(eps(NewInit, skip, I) :- true), (eps(F, skip, NewFinal) :- true)|Es],
   skips: Skips,
   initial: NewInit,
   final: [NewFinal]
})
   --> current_vars(Vs0),
       comp_aut(P1, Auto10),
       replace_vars(Vs1, Vs0),
       comp_aut(P2, Auto20),
       replace_vars(Vs2, Vs),
       {
          ord_union(Vs1, Vs2, Vs)
       },
       fresh_states([NewInit, NewFinal], [Vs0, Vs]),
       localize_auto(Auto10, Auto1, I1, F1, Vs1),
       localize_auto(Auto20, Auto2, I2, F2, Vs2),
       merge_states(F1, F2, F),
       merge_states(Auto1.initial, Auto2.initial, I),
       {
          skip_states(Auto1.skips, I1, States1),
          skip_states(Auto2.skips, I2, States2)
       },
       collect_lists(Auto1.transitions, Auto2.transitions, 
                     merge_trans_, [], Pairs),
       {extract_trans_states_(Pairs, []-States2, Trans0-States3)},
       collect_lists(Auto1.epses, States3, merge_eps_(left), [], Es1),
       collect_lists(Auto2.epses, States1, merge_eps_(right), Es1, Es2),
       {reverse(Es2, Es)},
       collect_lists(Auto1.skips, Auto2.skips, merge_skips_(F1, F2), [], Skips),
       collect_lists(Auto1.transitions, Auto2.skips, 
                     merge_trans_skip_(left), Trans0, Trans1),
       collect_lists(Auto2.transitions, Auto1.skips, 
                     merge_trans_skip_(right), Trans1, Trans). 

comp_aut(iter(P), auto{
   transitions: Trans,
   epses: [(eps(IterInit, skip, I0) :- true)|Es],
   skips: Skips,
   initial: IterInit,
   final: [IterFinal]
})
   --> current_vars(Vs),
       comp_aut(P, Auto0),
       fresh_states([IterInit, IterFinal], [Vs, Vs]),
       fresh_vars([CounterVar0, CounterVar]),
       replace_vars(_,Vs),
       {
         Skips = Auto0.skips,
         maplist(append_iter(CounterVar), Auto0.transitions, Trans),
         maplist(append_iter(CounterVar), Auto0.epses, Es0),
         count_state_push(0, Auto0.initial, I0),
         count_state_push(CounterVar, Auto0.initial, I1),
         maplist(count_state_push(CounterVar0), Auto0.final, Fin),
         sources_target_cond_acc_epses(Fin, I1, 
            CounterVar #= CounterVar0 + 1, Es0, Es1),
         sources_target_acc_epses(Fin, IterFinal, Es1, Es)
       }.

comp_aut(iter(P, Event, V), Auto)
--> 
    current_vars(Vs0),
    comp_aut(P, Auto0),
    {ord_add_element(Vs0, V, Vs)},
    fresh_states([IterInit, IterFinal], [Vs0, Vs]),
    fresh_vars([CounterVar0, CounterVar]),
    event_fresh(Event, EventFresh0),
    event_fresh(Event, EventFresh),
    event_fresh(Event, EventFresh2),  %1
    term_trans_goals(Event, EventT, GoalList0),
    {
       EventT =.. [Type|ExprList],
       maplist(init_expr, ExprList, InitList),
       InitEvent =.. [Type|InitList],
       frame_state_push(InitEvent, Auto0.initial, I0),
       count_state_push(0, I0, I),
       maplist(frame_state_push(EventFresh0), Auto0.final, FinalN0),
       maplist(count_state_push(CounterVar0), FinalN0, FinalN),
       frame_state_push(EventFresh, Auto0.initial, NextIter0),
       count_state_push(CounterVar, NextIter0, NextIter),
       EventFresh0 =.. [_|Xs0],
       EventFresh =.. [_|Xs],
       EventFresh2 =.. [_|Xs2], %2
       maplist(update_goal, ExprList, Xs0, Xs, UpdGoalList),
       maplist(finalize_goal, ExprList, Xs, Xs2, FinGoalList), %3
       append(GoalList0, UpdGoalList, GoalList),
       append(GoalList, FinGoalList, GoalList2), %4
       glist_goals([(CounterVar #= CounterVar0 + 1)|GoalList], Goals),
       glist_goals([V=EventFresh2|GoalList2], GoalsFinal), 
       maplist(append_iter(CounterVar), Auto0.epses, Epses0),
       maplist(append_iter(CounterVar), Auto0.transitions, Trans),
       sources_target_cond_acc_epses(FinalN, NextIter, Goals, 
         [(eps(IterInit, skip, I) :- true)|Epses0], 
         Epses1),
       sources_target_cond_acc_epses(FinalN, IterFinal, 
         GoalsFinal, Epses1, Epses),
       Auto = Auto0.put([epses=Epses, initial=IterInit, final=[IterFinal], 
          transitions=Trans])
    },
    replace_vars(_, Vs).      


comp_aut(filter(P, Cond), Auto)
   --> 
       comp_aut(P, Auto0),
       current_vars(Vs),
       fresh_state(S, Vs),
       cond_trans(Cond, C),
       {
         sources_target_cond_acc_epses(Auto0.final, S, C, Auto0.epses, Es),
         Auto = Auto0.put([epses=Es, final=[S]])
       }.


comp_aut(noskip(P, event(Type, V), Cond), Auto1)
   -->
       comp_aut(P, Auto),
       cond_trans(#\ Cond, C),
       {
          maplist(mod_skip(Type, V, C), Auto.skips, Skips),
          Auto1 = Auto.put([skips=Skips])
       }. 

/*
   Asserting compiled automaton.
*/

assert_trans((trans(V, Type, P, S0, S1) :- G))
   :- assertz((so_auto_cp:trans(S0, V, P, S1) :- event_types:event_type(V, Type), G)).

assert_trans((eps(S0, P, S1) :- G))
   :- assertz(so_auto_cp:eps(S0,P, S1):-G).

assert_final(Out, S)
   :- assertz(so_auto_cp:final(S, Out)).

assert_skip(skip(S, V, L))
   :- assertz(
         so_auto_cp:skip(S, X)
            :- skippable(X, V, L)
      ).

assert_regular(Id, Select0)
    :-  numbervars(Select0, 0, M0),
        Select0 = select(In0, Out0, Pattern),
        In0 =.. [_|Vs],
        length(Vs, NVs),
        %writeln('Compiling query pure'),
        compile_query_pure(Id, Pattern, M0, Vs, Auto0),
        %writeln('Compiled query pure'),
        varnumbers(select(In0, Out0, Auto0), Select),
        %writeln(Select),
        Select = select(_, Out, Auto),
        maplist(assert_trans, Auto.transitions),
        maplist(assert_trans, Auto.epses),
        maplist(assert_skip, Auto.skips),
        Auto.initial =.. [Sid|_],
        assertz((
           so_auto_cp:initial(Id, Input, Init) 
               :- Input =.. [_|Args],
                  length(Args, N),
                  N #= NVs,
                  Init =.. [Sid, [], [], start(0)|Args]
        )),
        maplist(assert_final(Out), Auto.final),
        !.
