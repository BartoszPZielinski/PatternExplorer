:- module(skip_pattern_compiler, [
     assert_regular/2
]).

:- use_module(library(clpfd)).
:- use_module(library(ordsets)).
:- use_module(library(varnumbers)).
:- use_module(library(pairs)).
:- use_module(library(assoc)).
:- use_module('skip_pattern_syntax.pl').
:- use_module('compiler_state.pl').
:- use_module('compiler_helpers.pl').
:- use_module('skippable.pl').
:- use_module('event_types.pl').


/*
    Automatons are represented (during compilation) by dicts of the form
    auto{
         transitions: [trans(V, Type, pos([L]), Subst, S0, S1):-G, ...],
         epses: [eps(S0, StartPos, Subst, S1), ...],
         skips: [skip(S, V1, event_specs), ...],
         initial: S,
         final: [S, ...]
    }
    Above Subst is a current substitution of variables in S1, and
    event_specs is a list of pairs type-condition.
    An event E is skippable in state S0 iff its type either is not on the list skips or it is 
    and then the condition is satisfied. The variable V1 is used
    to refer to the event under consideration in all the conditions.
   StartPos in eps is the position of the form pos(L) of start(X) subterm if the given eps corresponds 
   to saving the value of a last matched event in a variable. It is skip 
   otherwise.
*/

compile_query_pure(Id, Pattern, M0, Vs, Automaton)
    :- init_state(M0, Id, Vs, InitialState),
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
        epses: [(eps(S0, pos([]), Subst, S1) :- true)],
        initial: S0,
        skips: [],
        final: [S1]
   }) 
   --> last_matched(LastMatched),
       replace_vars(Vs0, Vs),
       {
         ord_add_element(Vs0, V, Vs),
         list_to_assoc([V-LastMatched], Subst)
       },
       fresh_states([S0, S1], [Vs0, Vs]). 

comp_aut(
   any(V), auto{
        transitions: [(trans(V, any, pos([]), Subst, S0, S1) :- true)],
        epses: [],
        initial: S0,
        skips: [skip(S0, V1, [])],
        final: [S1]
   }) 
   --> fresh_var(V1),
       replace_vars(Vs0, Vs),
       last_matched(LastMatched),
       {ord_add_element(Vs0, V, Vs)},
       fresh_states([S0, S1], [Vs0, Vs]),
       {list_to_assoc([LastMatched-V], Subst)}.

comp_aut(
   event(Type, V), auto{
        transitions: [(trans(V, Type, pos([]), Subst, S0, S1) :- true)],
        epses: [],
        initial: S0,
        skips: [skip(S0, V1, [])],
        final: [S1]
   }) 
   --> fresh_var(V1),
       replace_vars(Vs0, Vs),
       last_matched(LastMatched),
       {ord_add_element(Vs0, V, Vs)},
       fresh_states([S0, S1], [Vs0, Vs]),
       {list_to_assoc([LastMatched-V], Subst)}.

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
   epses: [(eps(S0, skip, Empty, I1) :- true), (eps(S0, skip, Empty, I2) :- true)|Es],
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
          append(Auto1.final, Auto2.final, Fs),
          list_to_assoc([], Empty)
       },
       fresh_state(S0, Vs0). 
        

comp_aut(P1 and P2, auto{
   transitions: Trans,
   epses: Es,
   skips: Skips,
   initial: I,
   final: [F]
})
   --> current_vars(Vs0),
       comp_aut(P1, Auto10),
       replace_vars(Vs1, Vs0),
       comp_aut(P2, Auto20),
       replace_vars(Vs2, Vs),
       localize_auto(Auto10, Auto1, F1, Vs1),
       localize_auto(Auto20, Auto2, F2, Vs2),
       {
         ord_union(Vs1, Vs2, Vs),
         merge_states(F1, F2, F),
         merge_states(Auto1.initial, Auto2.initial, I),
         skip_states(Auto1.skips, Auto1.initial, States1),
         skip_states(Auto2.skips, Auto2.initial, States2),
         collect_lists(Auto1.transitions, Auto2.transitions, 
                        merge_trans_, [], Pairs),
         extract_trans_states_(Pairs, []-States2, Trans0-States3),
         collect_lists(Auto1.epses, States3, merge_eps_(left), [], Es1),
         collect_lists(Auto2.epses, States1, merge_eps_(right), Es1, Es2),
         reverse(Es2, Es),
         collect_lists(Auto1.skips, Auto2.skips, merge_skips_(F1, F2), [], Skips),
         collect_lists(Auto1.transitions, Auto2.skips, 
                        merge_trans_skip_(left), Trans0, Trans1),
         collect_lists(Auto2.transitions, Auto1.skips, 
                        merge_trans_skip_(right), Trans1, Trans)
       }. 

comp_aut(iter(P), auto{
   transitions: Trans,
   epses: [(eps(IterInit, skip, Subst, I0) :- true)|Es],
   skips: Skips,
   initial: IterInit,
   final: [IterFinal]
}) --> current_vars(Vs),
       comp_aut(P, Auto0),
       fresh_states([IterInit, IterFinal], [Vs, Vs]),
       fresh_vars([CounterVar, CounterVar1]),
       replace_vars(_,Vs),
       {
         add_vars_to_auto([CounterVar], Auto0, Auto),
         I0 = Auto.initial,
         Skips = Auto.skips,
         maplist(append_iter(CounterVar), Auto.transitions, Trans),
         maplist(append_iter(CounterVar), Auto.epses, Es0),
         list_to_assoc([CounterVar-0], Subst),
         list_to_assoc([CounterVar-CounterVar1], Subst1),
         sources_target_cond_acc_epses(Auto.final, Auto.initial, Subst1,
            CounterVar1 #= CounterVar + 1, Es0, Es1),
         sources_target_acc_epses(Auto.final, IterFinal, Es1, Es)
       }.

comp_aut(iter(P, Event, V), Auto)
--> 
    current_vars(Vs0),
    comp_aut(P, Auto0),
    {ord_add_element(Vs0, V, Vs)},
    fresh_states([IterInit, IterFinal], [Vs0, Vs]),
    fresh_vars([CVar, Aggr, CVar1]),
    event_fresh(Event, EFresh0),
    event_fresh(Event, EFresh),
    term_trans_goals(Event, EventT, GList0),
    {
       list_to_ord_set([CVar, Aggr], NewVars),
       add_vars_to_auto(NewVars, Auto0, Auto1),
       iter_init_sub([CVar,Aggr], EventT, SubInit),
       iter_update_sub_goals([CVar, Aggr, CVar1], 
                             EventT-GList0, EFresh0-EFresh, SubUpd-UGoals),
       iter_finalize_sub_goals([Aggr, V], EventT-GList0, EFresh0-EFresh,
                               SubFin-FGoals),
       maplist(append_iter(CVar), Auto1.epses, Epses0),
       maplist(append_iter(CVar), Auto1.transitions, Trans),
       sources_target_cond_acc_epses(Auto1.final, Auto1.initial, SubUpd, UGoals, 
         [(eps(IterInit, skip, SubInit, Auto1.initial) :- true)|Epses0], 
         Epses1),
       sources_target_cond_acc_epses(Auto1.final, IterFinal, SubFin, FGoals,
         Epses1, Epses),
       Auto = Auto1.put([epses=Epses, initial=IterInit, final=[IterFinal], 
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
         list_to_assoc([], Empty),
         sources_target_cond_acc_epses(Auto0.final, S, Empty, C, Auto0.epses, Es),
         Auto = Auto0.put([epses=Es, final=[S]])
       }.

comp_aut(noskip(P, event(Type, V), Cond), Auto1)
   --> comp_aut(P, Auto),
       cond_trans(#\ Cond, C),
       {
          maplist(mod_skip(Type, V, C), Auto.skips, Skips),
          Auto1 = Auto.put([skips=Skips])
       }. 

comp_aut(noskip(P, N), Auto1)
   --> comp_aut(P, Auto),
       {pat_nskip_(N, NS)},
       modify_skips_rec_(NS, Auto.skips, Skips),
       {Auto1 = Auto.put([skips=Skips])}.

modify_skips_rec_([], Skips, Skips) --> [].
modify_skips_rec_([nskip(V, Type, Cond)|NS], Skips0, Skips)
   --> cond_trans(#\ Cond, C),
       {maplist(mod_skip(Type, V, C), Skips0, Skips1)},
       modify_skips_rec_(NS, Skips1, Skips).

pat_nskip_(P1 or P2, NS)
   :- pat_nskip_(P1, NS1),
      pat_nskip_(P2, NS2),
      append(NS1, NS2, NS).
pat_nskip_(filter(P, C), NS)
   :- pat_nskip_(P, NS0),
      maplist(add_ns_cond_(C), NS0, NS).
pat_nskip_(event(Type, X), [nskip(X, Type, 1 #= 1)]).

add_ns_cond_(C1, nskip(X, Type, C2), nskip(X, Type, C1 #/\ C2)).

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
        compile_query_pure(Id, Pattern, M0, Vs, Auto0),
        %format('Query ~w compiled~n', [Id]),
        subst_auto(Auto0, Auto1),
        varnumbers(select(In0, Out0, Auto1), Select),
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
                  Init =.. [Sid, start(0)|Args]
        )),
        maplist(assert_final(Out), Auto.final),
        !.
