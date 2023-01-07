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
         epses: [eps(S0,  Subst, S1), ...],
         skips: [skip(S, V1, event_specs), ...],
         initial: S,
         final: [S, ...]
    }
    Above Subst is a current substitution of variables in S1, and
    event_specs is a list of pairs type-condition.
    An event E is skippable in state S0 iff its type either is not on the list skips or it is 
    and then the condition is satisfied. The variable V1 is used
    to refer to the event under consideration in all the conditions.
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

comp_aut(event(Type, V), Auto) 
   --> fresh_var(V1),
       add_var(Vs0, V, Vs),
       fresh_states([S0, S1], [Vs0, Vs]),
       {
            empty_assoc(Subst),
            T = (trans(V, Type, pos([]), Subst, S0, S1) :- true),
            mk_auto(S0, [S1], [r(trans, [T]), r(skips, [skip(S0, V1, [])])], Auto)
       }.

comp_aut(fevent(Type, V, CT0, C0), Auto) 
   --> fresh_var(V1),
       add_var(Vs0, V, Vs),
       fresh_states([S0, S1], [Vs0, Vs]),
       {renumber_var(V, V1, CT0, CT1)},
       cond_trans(CT1, CT),
       cond_trans(C0, C),
       {
            empty_assoc(Subst),
            T = (trans(V, Type, pos([]), Subst, S0, S1) :- C),
            mk_auto(S0, [S1], [r(trans, [T]), r(skips, [skip(S0, V1, [any-CT])])], Auto)
       }.

comp_aut(P1 then P2, Auto)
   --> comp_aut(P1, Auto1),
       comp_aut(P2, Auto2),
       {
            appends_bin_(Auto1, Auto2, Auto1.initial, Auto2.final, Auto0),
            maplist(epsrev(Auto2.initial), Auto1.final, Es),
            mod_auto([a(epses, Es)], Auto0, Auto)
       }.

comp_aut(P1 or P2, Auto)
   --> par_compose_(P1-P2, A1-A2, ord_intersection, [Vs0|_]),
       fresh_state(S0, Vs0),
       {
          appends_bin_(A1, A2, S0, [], A0),
          maplist({S0}/[I, Eps]>>(epsrev(I, S0, Eps)), 
                  [A1.initial, A2.initial], Es),
          mod_auto([ra(final, [A1.final, A2.final]), a(epses, Es)], A0, Auto)
       }. 

comp_aut(P1 and P2, Auto) 
   --> par_compose_(P1-P2, Auto10-Auto20, ord_union, [_, Vs1, Vs2, _]),
       localize_auto(Auto10, Vs1, F1, Auto1),
       localize_auto(Auto20, Vs2, F2, Auto2),
       {
         merge_states(Auto1.initial, Auto2.initial, Initial),
         merge_states(F1, F2, Final),
         maplist([skip(S, _, _), S]>>true, Auto1.skips, States1),
         maplist([skip(S, _, _), S]>>true, Auto2.skips, States20),
         combine_lists(
            [(trans(_, Type, _, _, _, _) :- _), 
             (trans(_, Type, _, _, _, S) :- _), S]>>true,
            Auto1.trans, Auto2.trans, States21),
         (
               (member(Auto1.initial, States1);member(Auto2.initial, States20))
               -> append(States20, States21, States2) 
               ; append([[Auto2.initial], States20, States21], States2)
         ),
         combine_lists(merge_eps_(left), Auto1.epses, States2, Es1),
         combine_lists(merge_eps_(right), Auto2.epses, States1, Es2),
         combine_lists(merge_skips_(F1, F2), Auto1.skips, Auto2.skips, Skips),
         combine_lists(merge_trans_, Auto1.trans, Auto2.trans, Trans1),
         combine_lists(merge_trans_skip_(left), Auto1.trans, Auto2.skips, Trans2),
         combine_lists(merge_trans_skip_(right),Auto2.trans, Auto1.skips, Trans3),
         mk_auto(Initial, [Final], [
            ra(epses, [Es1, Es2]), 
            ra(trans, [Trans1, Trans2, Trans3]), 
            r(skips, Skips)
         ], Auto)
       }. 

comp_aut(iter(P), Auto) --> comp_aut(iter(P,[]), Auto).

comp_aut(iter(P, List0), Auto)
      --> current_vars(Vs0),
          comp_aut(P, Auto0),
          get_count_var(List0, CVar, List),
          {
               maplist([X = _, X]>>true, List, Xs0),
               list_to_ord_set(Xs0, Xs),
               ord_union(Vs0, Xs, Vs)
          },
          replace_vars(_, Vs),
          fresh_states([IterInit, IterFinal], [Vs0, Vs]),
          args_fresh_vars(Xs0, Xs1),
          terms_trans_goals_(List, ListT, GList0),
          {
               add_vars_to_auto(Xs0, Auto0, Auto1),
               maplist(append_iter(CVar), Auto1.trans, Trans0),
               mod_time_trans(List0, Trans0, Trans),
               maplist(init_expr, ListT, Pairs),
               epsrev(Pairs, Auto1.initial, IterInit, Ei),
               iter_eps(update_goal, Auto1.final-Auto1.initial, 
                        ListT-GList0, Xs1, Eu),
               iter_eps(finalize_goal, Auto1.final-IterFinal, 
                        ListT-GList0, Xs1, Ef),
               mod_auto([
                  aa(epses, [Ef, Eu, [Ei]]),
                  r(initial, IterInit), r(trans, Trans), r(final, [IterFinal])
               ], Auto1, Auto)
          }. 


comp_aut(fiter(P, List0, CT0), Auto)
         --> current_vars(Vs0),
             comp_aut(P, Auto0),
             get_count_var(List0, CVar, List),
             {
                  maplist([X = _, X]>>true, List, Xs0),
                  list_to_ord_set(Xs0, Xs),
                  ord_union(Vs0, Xs, Vs)
             },
             replace_vars(_, Vs),
             fresh_states([IterInit, IterFinal], [Vs0, Vs]),
             args_fresh_vars(Xs0, Xs1),
             terms_trans_goals_(List, ListT, GList0),
             term_trans_goals(CT0, CT, CTList),
             {
                  add_vars_to_auto(Xs0, Auto0, Auto1),
                  maplist(append_iter(CVar), Auto1.trans, Trans0),
                  mod_time_trans(List0, Trans0, Trans),
                  maplist(init_expr, ListT, Pairs),
                  epsrev(Pairs, Auto1.initial, IterInit, Ei),
                  append(CTList, GList0, GList1),
                  iter_eps(update_goal, Auto1.final-Auto1.initial, 
                           ListT-[CT|GList1], Xs1, Eu),
                  iter_eps(finalize_goal, Auto1.final-IterFinal, 
                           ListT-GList0, Xs1, Ef),
                  mod_auto([
                     aa(epses, [Ef, Eu, [Ei]]),
                     r(initial, IterInit), r(trans, Trans), r(final, [IterFinal])
                  ], Auto1, Auto)
             }. 
   

comp_aut(filter(P, Cond), Auto)
   --> comp_aut(P, Auto0),
       current_vars(Vs),
       fresh_state(S, Vs),
       cond_trans(Cond, C),
       {
         maplist(epsrev(C, [], S), Auto0.final, Es),
         mod_auto([a(epses, Es), r(final, [S])], Auto0, Auto)
       }.

comp_aut(noskip(P, N), Auto1)
   --> comp_aut(P, Auto),
       {pat_nskip_(N, NS)},
       modify_skips_rec_(NS, Auto.skips, Skips),
       {mod_auto([r(skips, Skips)], Auto, Auto1)}.

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

add_ns_cond_(C1, nskip(X, Type, 1 #= 1), nskip(X, Type, C1)) :- ! .
add_ns_cond_(C1, nskip(X, Type, C2), nskip(X, Type, C1 #/\ C2)) 
   :- dif(C2, 1 #= 1), !.

/*
   Asserting compiled automaton.
*/

assert_trans((trans(V, Type, P, S0, S1) :- G))
   :- assertz((so_auto_cp:trans(S0, V, P, S1) :- event_types:event_type(V, Type), G)).

assert_trans((eps(S0, S1) :- G))
   :- assertz(so_auto_cp:eps(S0, S1):-G).

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
        Auto.initial =.. [Sid|_],
        assertz((
           so_auto_cp:initial(Id, Input, Init) 
               :- Input =.. [_|Args],
                  length(Args, N),
                  N #= NVs,
                  Init =.. [Sid|Args]
        )),
        maplist({Out}/[S]>>assertz(so_auto_cp:final(S, Out)), Auto.final),
        !.
