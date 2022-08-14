:- module(compiler_helpers, [
        epsrev/6,
        epsrev/5,
        epsrev/4,
        epsrev/3,
        init_expr/2,
        update_goal/4,
        finalize_goal/4,
        mod_skip/5,
        append_iter/3,
        merge_states/3,
        eps_states/2,
        eps_states2/3,
        combine_lists/4,
        merge_eps_/4,
        merge_skips_/5,
        merge_trans_skip_/4,
        merge_trans_/3,
        add_vars_to_auto/3,
        subst_auto/2,
        iteratize_auto/3,
        mod_init_eps/4,
        mod_upd_eps/5,
        mod_fin_eps/5,
        counter_epses/4,
        empty_auto/3,
        appends_bin_/5,
        localize_auto//4,
        get_event_spec//4,
        mod_time_trans/4
    ]).

:- use_module(library(clpfd)).
:- use_module(library(assoc)).
:- use_module(library(yall)).
:- use_module(library(apply)).
:- use_module('compiler_state.pl').

empty_auto(Initial, Final, auto{
   trans: [],
   epses: [],
   initial: Initial,
   skips: [],
   final: Final,
   aggrs: []
}).

%%%%% Some compilation helpers

appends_bin_(Auto1, Auto2, Initial, Final, Auto)
:- maplist(append_pos(p(1)), Auto1.trans, T1),
   maplist(append_pos(p(2)), Auto2.trans, T2),
   maplist(append_pos(p(1)), Auto1.epses, Es01),
   maplist(append_pos(p(2)), Auto2.epses, Es02),
   append(T1, T2, Ts),
   append(Es01, Es02, Es),
   append(Auto1.skips, Auto2.skips, Skips),
   empty_auto(Initial, Final, Auto0),
   Auto = Auto0.put([trans=Ts, epses=Es, skips=Skips]).

%%%%% Adding variables

add_vars_to_state(Vars0, S0, S1)
   :- S0 =.. [SId, LastMatched | Vars1],
      ord_union(Vars0, Vars1, Vars),
      S1 =.. [SId, LastMatched | Vars].

add_vars_to_el(Vars, 
   (trans(V, Type, Pos, Subst, S00, S10) :- G),
   (trans(V, Type, Pos, Subst, S0, S1) :- G)
) :- maplist(add_vars_to_state(Vars), [S00, S10], [S0, S1]).

add_vars_to_el(Vars, 
   (eps(S00, Pos, Subst,  S10) :- G),
   (eps(S0, Pos, Subst, S1) :- G)
) :- maplist(add_vars_to_state(Vars), [S00, S10], [S0, S1]).

add_vars_to_el(Vars,
   skip(S0, V, Spec),
   skip(S, V, Spec)
) :- add_vars_to_state(Vars, S0, S).

add_vars_to_auto(Vars0, Auto0, Auto) 
   :- list_to_ord_set(Vars0, Vars),
      maplist(add_vars_to_el(Vars), Auto0.trans, Ts),
      maplist(add_vars_to_el(Vars), Auto0.epses, Es),
      maplist(add_vars_to_el(Vars), Auto0.skips, Skips),
      maplist(add_vars_to_state(Vars), Auto0.final, Fs),
      add_vars_to_state(Vars, Auto0.initial, I),
      empty_auto(I, Fs, Auto1),
      Auto = Auto1.put([trans=Ts, epses=Es, skips=Skips]).
      
%%%% Position helpers

head_tail_pos_(_, skip, skip).
head_tail_pos_(H, pos(L), pos([H|L])).

dir_tail_pos_(Dir, Pos0, Pos) 
   :- (Dir=left -> H = p(1) ; H = p(2)),
      head_tail_pos_(H, Pos0, Pos).

append_pos(H, (trans(V, Type, P0, Sub, S0, S1) :- C), 
             (trans(V, Type, P, Sub, S0, S1) :- C))
   :- head_tail_pos_(H, P0, P).

append_pos(H, (eps(S0, P0, Sub, S1) :- C), (eps(S0, P, Sub, S1) :- C))
   :- head_tail_pos_(H, P0, P).

append_iter(
   CounterVar,
   (trans(V, Type, pos(L), Sub, S0, S1) :- G),
   (trans(V, Type, pos([i(CounterVar)|L]), Sub, S0, S1) :- G)
).

append_iter(CounterVar, 
   (eps(S0, P0, Sub, S1) :- G),
   (eps(S0, P, Sub, S1) :- G)
) :- head_tail_pos_(i(CounterVar), P0, P).

/*
    Adding epses
 */

epsrev(P, C, Sub, S1, S0, (eps(S0, P, Sub, S1) :- C)).
epsrev(C, Sub, S1, S0, Eps) :- epsrev(skip, C, Sub, S1, S0, Eps).
epsrev(Sub, S1, S0, Eps) :- epsrev(skip, true, Sub, S1, S0, Eps).
epsrev(S1, S0, Eps)
   :- list_to_assoc([], Empty), 
      epsrev(skip, true, Empty, S1, S0, Eps).

/*
    Iteration helpers
 */

get_event_spec(CVar-TVar, List, Event, Aggr)
-->  {maplist([Attr = Fun, Attr, Fun] >> true, List, Attrs, Funs)}, 
     fresh_event(Event, [time, count | Attrs]),
     {Event =.. [Eid|_],
      Aggr =.. [Eid, time(TVar), count0(CVar)|Funs]}.

mod_time_trans(
   LastTime, TVar,
   (trans(V, Type, P, Sub0, S0, S1) :- C),
   (trans(V, Type, P, Sub, S0, S1) :- C)
) :- get_assoc(LastTime, Sub0, LT),
     put_assoc(TVar, Sub0, LT, Sub).

iteratize_auto(NewVars, Auto0, Auto)
   :- add_vars_to_auto(NewVars, Auto0, Auto1),
      NewVars = [CounterVar|_],
      maplist(append_iter(CounterVar), Auto1.epses, Epses),
      maplist(append_iter(CounterVar), Auto1.trans, Trans),
      Auto = Auto1.put([epses=Epses, trans = Trans]).

counter_epses(Auto, IterInit-IterFinal, CVar-CVar1, [Ei, Eu, Ef])
   :- list_to_assoc([CVar-1], Sub),
      list_to_assoc([CVar-CVar1], Sub1),
      epsrev(Sub, Auto.initial, IterInit, Ei),
      maplist(epsrev(CVar1 #= CVar + 1, Sub1, Auto.initial), Auto.final, Eu),
      maplist(epsrev(IterFinal), Auto.final, Ef).

mod_eps_(OSub-NSub, C,
   (eps(S0, P, OSub, S1) :- C0),
   (eps(S0, P, NSub, S1) :- C0, C) 
).

mod_init_eps(Aggr, EventT, Eps0, Eps)
   :- EventT =.. [Type|ExprList],
      maplist(init_expr, ExprList, InitList),
      InitEvent =.. [Type|InitList],
      mod_eps_(OSub-NSub, true, Eps0, Eps),
      put_assoc(Aggr, OSub, InitEvent, NSub).

mod_upd_eps(Aggr, EventT-GList0, EventFresh0-EventFresh, Eps0, Eps)
   :- EventT =.. [_|ExprList],
      EventFresh0 =.. [_|Xs0],
      EventFresh =.. [_|Xs],
      maplist(update_goal, ExprList, Xs0, Xs, UpdGList0),
      append(GList0, UpdGList0, UpdGList1),
      glist_goals([(Aggr=EventFresh0)|UpdGList1], Goals),
      mod_eps_(OSub-NSub, Goals, Eps0, Eps),
      put_assoc(Aggr, OSub, EventFresh, NSub).

mod_fin_eps(Aggr-V, EventT-GList0, EventFresh0-EventFresh, Eps0, Eps)
   :- EventT =.. [_|ExprList],
      EventFresh0 =.. [_|Xs0],
      EventFresh =.. [_|Xs],
      maplist(finalize_goal, ExprList, Xs0, Xs, FinGList0),
      append(GList0, FinGList0, FinGList1),
      glist_goals([Aggr=EventFresh0|FinGList1], Goals),
      mod_eps_(OSub-NSub, Goals, Eps0, Eps),
      put_assoc(V, OSub, EventFresh, NSub).

init_expr(sum(_), 0).
init_expr(min(_), nothing).
init_expr(max(_), nothing).
init_expr(count(*), 1).
init_expr(avg(_), a(0,0)).
init_expr(count0(_), _).
init_expr(time(_), 0).

update_goal(sum(E), X0, X, X #= X0 + E).
update_goal(min(E), X0, X, so_auto_cp:ext_min(X0, E, X)).
update_goal(max(E), X0, X, so_auto_cp:ext_max(X0, E, X)).
update_goal(count(*), X0, X, X #= X0 + 1).
update_goal(avg(E), X0, X, so_auto_cp:update_avg(X0, E, X)).
update_goal(count0(_), _, _, true).
update_goal(time(_), _, _, true).

finalize_goal(min(_), X0, X, X #= X0).
finalize_goal(min(_), X0, X, so_auto_cp:fin_minmax(X0, X)).
finalize_goal(max(_), X0, X, so_auto_cp:fin_minmax(X0, X)).
finalize_goal(min(_), X0, X, so_auto_cp:fin_minmax(X0, X)).
finalize_goal(count(*), X0, X, X #= X0).
finalize_goal(avg(_), X0, X, so_auto_cp:fin_avg(X0, X)).
finalize_goal(count0(CounterVar), _, X, X #= CounterVar).
finalize_goal(time(TVar), _, X, X #= TVar).

/*
    Noskip helpers
 */

mod_skip(Type, V0, C0, skip(S, V, L0), skip(S,  V, L))
   :- renumber_var(V0, V, C0, C),
      mod_or_add_skip_rules(Type, C, L0, L).

mod_or_add_skip_rules(Type, C, [], [Type-C]).
mod_or_add_skip_rules(Type, C, [Type-C0 | L0], [Type-(C, C0) |L0]).
mod_or_add_skip_rules(Type, C, [Type0-C0 | L0], [Type0-C0 | L])
:- dif(Type, Type0),
   mod_or_add_skip_rules(Type, C, L0, L).

/*
    And helpers
 */

localize_auto(Auto0, Vs, F, Auto)
   --> fresh_state(F, Vs),
       fresh_var(V),
       {
            maplist(epsrev(F), Auto0.final, Es0),
            append(Auto0.epses, Es0, Es),
            Skips = [skip(F, V, [])|Auto0.skips],
            Auto = Auto0.put([skips=Skips, epses=Es, final=[F]])
       }.

merge_states(S1, S2, S)
   :- S1 =.. [Sid1, LastMatched|Vars1],
      S2 =.. [Sid2, LastMatched|Vars2],
      term_to_atom(a(Sid1, Sid2), Sid),
      ord_union(Vars1, Vars2, Vars),
      S =.. [Sid, LastMatched | Vars].

eps_states(Auto, States)
   :- maplist([skip(S, _, _), S]>>true, Auto.skips, States).

eps_states2(Auto, Ts, States)
   :- eps_states(Auto, States0),
      combine_lists(
         [(trans(_, Type, _, _, _, _) :- _), 
          (trans(_, Type, _, _, _, S) :- _), S]>>true,
         Ts, Auto.trans, States1),
      list_to_ord_set(States1, States2),
      ord_union(States0, States2, States).

make_pairs_(Ls1, Ls2, Pairs)
   :- maplist(
         {Ls1}/[X2, Sublist]>>(
            maplist({X2}/[X1, X1-X2]>>true, Ls1, Sublist)
         ), Ls2, Sublists
      ), append(Sublists, Pairs).

combine_lists(F, Ls1, Ls2, Out)
   :- make_pairs_(Ls1, Ls2, Pairs),
      convlist({F}/[X1-X2, Y]>>call(F, X1, X2, Y), Pairs, Out).

merge_eps_(Dir, (eps(S0, P0, Sub, S1) :- G), S, (eps(Sm0, P, Sub, Sm1) :- G))
   :- maplist(merge_states(Dir), [S0, S1], [S, S], [Sm0, Sm1]),
      dir_tail_pos_(Dir, P0, P). 

merge_states(left, S1, S2, S) :- merge_states(S1, S2, S).
merge_states(right, S1, S2, S) :- merge_states(S2, S1, S).

merge_skips_(F1, F2, skip(S1, V1, L1), skip(S2, V2, L2), skip(S, V2, L))
   :- (dif(F1, S1) ; dif(F2, S2)),
      merge_states(S1, S2, S),
      renumber_var(V1, V2, L1, L11),
      foldl([Pair, Spec0, Spec]>>merge_spec(Spec0, Pair, Spec), L11, L2, L). 

merge_spec([], Pair, [Pair]).
merge_spec([Type-Cond0|Spec0], Type-Cond, [Type-(Cond0, Cond)|Spec0]) 
:- !.
merge_spec([Type0-Cond0|Spec0], Type-Cond, [Type0-Cond0|Spec])
:- dif(Type0, Type),
   merge_spec(Spec0, Type-Cond, Spec).

merge_trans_skip_(
   Dir,
   (trans(V, Type, Pos0, Sub, S0, S1):-G), 
   skip(S2, V1, L), 
   (trans(V, Type, Pos, Sub, Sm0, Sm1):-C, G)
) :-  maplist(merge_states(Dir), [S0, S1], [S2, S2], [Sm0, Sm1]),
      type_spec_cond(Type, L, C0),
      renumber_var(V1, V, C0, C),
      dir_tail_pos_(Dir, Pos0, Pos).

type_spec_cond(_, [],  true).
type_spec_cond(Type, [Type-C|_], C) :- !.
type_spec_cond(Type, [Type1-_|L], C)
   :- dif(Type, Type1),
      type_spec_cond(Type, L, C).

merge_trans_(
         (trans(V1, Type, pos(L1), Sub1, S10, S11) :- G1),
         (trans(V2, Type, pos(L2), Sub2, S20, S21) :- G2),
         (trans(V1, Type, pos([c(L1, L2)]), Sub, S0, S1) :- G1, G2)
) :- maplist(merge_states, [S10, S11], [S20, S21], [S0, S1]),
     assoc_to_list(Sub1, Pairs),
     foldl([K-V, A0, A]>>put_assoc(K, A0, V, A), Pairs, Sub2, Sub0),
     put_assoc(V2, Sub0, V1, Sub). 

%%% Final transformation of an automaton: applying substitutions in 
%%% transitions and epses.

sub_var_(Sub, Var, Value) :- 
   get_assoc(Var, Sub, Value) -> true ; Value = Var.

subst_state_(Sub, S0, S)
   :- S0 =.. [Sid|Vars0],
      maplist(sub_var_(Sub), Vars0, Values),
      S =.. [Sid|Values].

subst_(
   (trans(V, Type, P, Sub, S0, S1) :- G1),
   (trans(V, Type, P, S0, S2) :- G1)
) :- subst_state_(Sub, S1, S2).

subst_(
   (eps(S0, P, Sub, S1) :- G1),
   (eps(S0, P, S2) :- G1)
) :- subst_state_(Sub, S1, S2).

subst_auto(Auto0, Auto)
   :- maplist(subst_, Auto0.trans, Trans),
      maplist(subst_, Auto0.epses, Epses),
      Auto = Auto0.put([trans=Trans, epses=Epses]).
