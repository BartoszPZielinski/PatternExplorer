:- module(skip_pattern_compiler, [
     assert_regular/2
]).

:- use_module(library(clpfd)).
:- use_module(library(ordsets)).
:- use_module(library(varnumbers)).
:- use_module(library(pairs)).
:- use_module(library(assoc)).
:- use_module(library(yall)).
:- use_module('skip_pattern_syntax.pl').
:- use_module('compiler_state.pl').
:- use_module('compiler_helpers.pl').
:- use_module('skippable.pl').
:- use_module('event_types.pl').

/*
    Automatons are represented (during compilation) by dicts of the form
    auto{
         trans: [trans(V, Type, pos([L]), Subst, S0, S1):-G, ...],
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


par_compose_(P1-P2, Auto1-Auto2, Op, [Vs0, Vs1, Vs2, Vs])
   --> current_vars(Vs0),
       comp_aut(P1, Auto1),
       replace_vars(Vs1, Vs0),
       comp_aut(P2, Auto2),
       replace_vars(Vs2, Vs),
       {call(Op, Vs1, Vs2, Vs)}. 

comp_aut(start(V), Auto) 
   --> last_matched(LastMatched),
       add_var(Vs0, V, Vs),
       fresh_states([S0, S1], [Vs0, Vs]),
       {
            list_to_assoc([V-LastMatched], Subst),
            epsrev(pos([]), true, Subst, S1, S0, E),
            empty_auto(S0, [S1], Auto0),
            Auto = Auto0.put([epses=[E]])
        }.

comp_aut(any(V), Auto) --> comp_aut(event(any, V), Auto).

comp_aut(event(Type, V), Auto) 
   --> fresh_vars([V1, Time]),
       add_var(Vs0, V, Vs),
       specials(LastMatched, LastTime),
       fresh_states([S0, S1], [Vs0, Vs]),
       {
            list_to_assoc([LastMatched-V, LastTime-Time], Subst),
            T = (trans(V, Type, pos([]), Subst, S0, S1) 
                     :- event_time(V, Time)),
            empty_auto(S0, [S1], Auto0),
            Auto = Auto0.put([trans=[T], skips=[skip(S0, V1, [])]])
       }.

comp_aut(P1 then P2, Auto)
   --> comp_aut(P1, Auto1),
       comp_aut(P2, Auto2),
       {
            appends_bin_(Auto1, Auto2, Auto1.initial, Auto2.final, Auto0),
            maplist(epsrev(Auto2.initial), Auto1.final, Es1),
            append(Auto0.epses, Es1, Es),
            Auto = Auto0.put([epses=Es])
       }.

comp_aut(P1 or P2, Auto)
   --> par_compose_(P1-P2, Auto1-Auto2, ord_intersection, [Vs0|_]),
       fresh_state(S0, Vs0),
       {
          append(Auto1.final, Auto2.final, Fs),
          appends_bin_(Auto1, Auto2, S0, Fs, Auto0),
          maplist({S0}/[I, Eps]>>(epsrev(I, S0, Eps)), 
                  [Auto1.initial, Auto2.initial], Epses0),
          append(Epses0, Auto0.epses, Epses),
          Auto = Auto0.put([epses=Epses])
       }. 

comp_aut(P1 and P2, Auto) 
   --> par_compose_(P1-P2, Auto10-Auto20, ord_union, [_, Vs1, Vs2, _]),
       localize_auto(Auto10, Vs1, F1, Auto1),
       localize_auto(Auto20, Vs2, F2, Auto2),
       {
         merge_states(Auto1.initial, Auto2.initial, Initial),
         merge_states(F1, F2, Final),
         eps_states(Auto1, States1),
         eps_states2(Auto2, Auto1.trans, States20),
         (
               (ord_memberchk(Auto1.initial, States1) 
                ; ord_memberchk(Auto2.initial, States20))
               -> States2 = States20 
               ; ord_union(States20, [Auto2.initial], States2)
         ),
         combine_lists(merge_eps_(left), Auto1.epses, States2, Es1),
         combine_lists(merge_eps_(right), Auto2.epses, States1, Es2),
         append(Es1, Es2, Es),
         combine_lists(merge_skips_(F1, F2), Auto1.skips, Auto2.skips, Skips),
         combine_lists(merge_trans_, Auto1.trans, Auto2.trans, Trans1),
         combine_lists(merge_trans_skip_(left), Auto1.trans, Auto2.skips, Trans2),
         combine_lists(merge_trans_skip_(right),Auto2.trans, Auto1.skips, Trans3),
         append([Trans1, Trans2, Trans3], Trans),
         empty_auto(Initial, [Final], Auto0),
         Auto = Auto0.put([trans=Trans, epses=Es, skips=Skips])
       }. 

comp_aut(iter(P), Auto) 
   --> current_vars(Vs),
       comp_aut(P, Auto0),
       fresh_states([IterInit, IterFinal], [Vs, Vs]),
       fresh_vars([CVar, CVar1]),
       replace_vars(_,Vs),
       {
         iteratize_auto([CVar], Auto0, Auto1),
         counter_epses(Auto1, IterInit-IterFinal, CVar-CVar1, [Ei, Eu, Ef]),
         append([Ef, Eu, [Ei], Auto1.epses], Es),
         Auto = Auto1.put([initial=IterInit, final=[IterFinal], epses=Es])
       }.

comp_aut(iter(P, Event, V), Auto)
--> current_vars(Vs0),
    comp_aut(P, Auto0),
    {ord_add_element(Vs0, V, Vs)},
    fresh_states([IterInit, IterFinal], [Vs0, Vs]),
    fresh_vars([CVar, Aggr, CVar1]),
    event_fresh(Event, EFresh0),
    event_fresh(Event, EFresh),
    term_trans_goals(Event, EventT, GList0),
    {
       iteratize_auto([CVar, Aggr], Auto0, Auto1),
       counter_epses(Auto1, IterInit-IterFinal, CVar-CVar1, [Ei0, Eu0, Ef0]),
       mod_init_eps(Aggr, EventT, Ei0, Ei),
       maplist(mod_upd_eps(Aggr, EventT-GList0, EFresh0-EFresh), Eu0, Eu),
       maplist(mod_fin_eps(Aggr-V, EventT-GList0, EFresh0-EFresh), Ef0, Ef),
       append([Ef, Eu, [Ei], Auto1.epses], Epses),
       Auto = Auto1.put([epses=Epses, initial=IterInit, final=[IterFinal]])
    },
    replace_vars(_, Vs).  

comp_aut(aggr(P, List, V), Auto)
   --> current_vars(Vs0),
       comp_aut(P, Auto0),
       {ord_add_element(Vs0, V, Vs)},
       fresh_states([IterInit, IterFinal], [Vs0, Vs]),
       fresh_vars([CVar, TVar, Aggr, CVar1]),
       get_event_spec(CVar-TVar, List, Event, EAggr),
       event_fresh(EAggr, EFresh0),
       event_fresh(EAggr, EFresh),
       term_trans_goals(EAggr, EventT, GList0),
       specials(_, LastTime),
       {
          iteratize_auto([CVar, Aggr, TVar], Auto0, Auto1),
          counter_epses(Auto1, IterInit-IterFinal, CVar-CVar1, [Ei0, Eu0, Ef0]),
          maplist(mod_time_trans(LastTime, TVar), Auto1.trans, Trans),
          mod_init_eps(Aggr, EventT, Ei0, Ei),
          maplist(mod_upd_eps(Aggr, EventT-GList0, EFresh0-EFresh), Eu0, Eu),
          maplist(mod_fin_eps(Aggr-V, EventT-GList0, EFresh0-EFresh), Ef0, Ef),
          append([Ef, Eu, [Ei], Auto1.epses], Epses),
          Auto = Auto1.put([epses=Epses, initial=IterInit, trans=Trans,
                            final=[IterFinal], aggrs=[Event|Auto1.aggrs]])
       },
       replace_vars(_, Vs).      
       

comp_aut(filter(P, Cond), Auto)
   --> comp_aut(P, Auto0),
       current_vars(Vs),
       fresh_state(S, Vs),
       cond_trans(Cond, C),
       {
         list_to_assoc([], Empty),
         maplist(epsrev(C, Empty, S), Auto0.final, Es0),
         append(Es0, Auto0.epses, Es),
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

assert_regular(Id, Select0)
    :-  numbervars(Select0, 0, M0),
        Select0 = select(In0, Out0, Pattern),
        In0 =.. [_|Vs],
        length(Vs, NVs),
        compile_query_pure(Id, Pattern, M0, Vs, Auto0),
        subst_auto(Auto0, Auto1),
        varnumbers(select(In0, Out0, Auto1), Select),
        Select = select(_, Out, Auto),
        maplist(assert_trans, Auto.trans),
        maplist(assert_trans, Auto.epses),
        maplist(
            [skip(S, V, L)]>>assertz(so_auto_cp:skip(S, X) :- skippable(X, V, L)),
            Auto.skips
        ),
        def_event_types(Auto.aggrs),
        Auto.initial =.. [Sid|_],
        assertz((
           so_auto_cp:initial(Id, Input, Init) 
               :- Input =.. [_|Args],
                  length(Args, N),
                  N #= NVs,
                  Init =.. [Sid, start(0), 0|Args]
        )),
        maplist({Out}/[S]>>assertz(so_auto_cp:final(S, Out)), Auto.final),
        !.
