:- module(compiler_helpers, [
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
        empty_auto/3,
        appends_bin_/5,
        localize_auto//4,
        mod_time_trans/3,
        get_count_var//3,
        iter_eps/5,
        mod_auto/3,
        mk_auto/4
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
   final: Final
}).

mod_auto(Trans, Auto0, Auto)
   :- foldl(mod_auto_, Trans, Auto0, Auto).

mk_auto(Initial, Final, Trans, Auto)
   :- empty_auto(Initial, Final, Auto0),
      mod_auto(Trans, Auto0, Auto).

mod_auto_(r(Attr, Val), Auto0, Auto)
   :- Auto=Auto0.put([Attr=Val]).

mod_auto_(ra(Attr, L), Auto0, Auto)
   :- append(L, Val),
      Auto=Auto0.put([Attr=Val]).

mod_auto_(a(Attr, Val), Auto0, Auto)
   :- append(Val, Auto0.Attr, L),
      Auto=Auto0.put([Attr=L]).

mod_auto_(aa(Attr, L0), Auto0, Auto)
   :- append([Auto0.Attr|L0], L),
      Auto=Auto0.put([Attr=L]).

%%%%% Some compilation helpers

appends_bin_(Auto1, Auto2, Initial, Final, Auto)
:- maplist(append_pos(p(1)), Auto1.trans, T1),
   maplist(append_pos(p(2)), Auto2.trans, T2),
   mk_auto(Initial, Final, [
      ra(trans, [T1, T2]), 
      ra(epses, [Auto1.epses, Auto2.epses]), 
      ra(skips, [Auto1.skips, Auto2.skips])
   ], Auto).

%%%%% Adding variables

add_vars_to_state(Vars0, S0, S1)
   :- S0 =.. [SId | Vars1],
      ord_union(Vars0, Vars1, Vars),
      S1 =.. [SId | Vars].

add_vars_to_el(Vars, 
   (trans(V, Type, Pos, Subst, S00, S10) :- G),
   (trans(V, Type, Pos, Subst, S0, S1) :- G)
) :- maplist(add_vars_to_state(Vars), [S00, S10], [S0, S1]).

add_vars_to_el(Vars, 
   (eps(S00, Subst,  S10) :- G),
   (eps(S0, Subst, S1) :- G)
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

append_pos(H, (trans(V, Type, pos(L), Sub, S0, S1) :- C), 
             (trans(V, Type, pos([H|L]), Sub, S0, S1) :- C)).

append_iter(
   CounterVar,
   (trans(V, Type, pos(L), Sub, S0, S1) :- G),
   (trans(V, Type, pos([i(CounterVar)|L]), Sub, S0, S1) :- G)
).

/*
    Adding epses
 */

epsrev(C, Pairs, S1, S0, (eps(S0, Sub, S1) :- C))
   :- list_to_assoc(Pairs, Sub).
epsrev(Pairs, S1, S0, Eps) :- epsrev(true, Pairs, S1, S0, Eps).
epsrev(S1, S0, Eps) :- epsrev(true, [], S1, S0, Eps).

/*
    Iteration helpers
 */

get_count_var([], CVar, [CVar=count]) --> fresh_var(CVar).
get_count_var([A = count|L], A, [A = count|L]) --> [].
get_count_var([A = F|Ls0], CVar, [A = F|Ls]) 
   --> {dif(F, count)}, get_count_var(Ls0, CVar, Ls).

mod_time_trans([], Trans, Trans).
mod_time_trans([TVar = time|_], Trans0, Trans) 
   :- maplist(mod_time_trans_(TVar), Trans0, Trans).
mod_time_trans([_=F|Ls], Trans0, Trans)
   :- dif(F, time), mod_time_trans(Ls, Trans0, Trans).

mod_time_trans_(
   LastMatched,
   (trans(V, Type, P, Sub0, S0, S1) :- C),
   (trans(V, Type, P, Sub1, S0, S1) :- C)
) :- put_assoc(LastMatched, Sub0, V, Sub1).

iter_eps(F, Ss-T, ListT-GList0, Xs1, Es)
:- maplist(F, ListT, Xs1, Pairs, GList1),
   append(GList0, GList1, GList),
   glist_goals(GList, Goals),
   maplist(epsrev(Goals, Pairs, T), Ss, Es).

init_expr(X=sum(_), X-0).
init_expr(X=min(_), X-nothing).
init_expr(X=max(_), X-nothing).
init_expr(X=count, X-1).
init_expr(X=avg(_), X-a(0,0)).
init_expr(X=time(_), X-0).

update_goal(X0=sum(E), X, X0-X, X #= X0 + E).
update_goal(X0=min(E), X, X0-X, so_auto_cp:ext_min(X0, E, X)).
update_goal(X0=max(E), X, X0-X, so_auto_cp:ext_max(X0, E, X)).
update_goal(X0=count, X, X0-X, X #= X0 + 1).
update_goal(X0=avg(E), X, X0-X, so_auto_cp:update_avg(X0, E, X)).
update_goal(X0=time(_), _, X0-X0, true).

finalize_goal(X0=sum(_), _, X0-X0, true).
finalize_goal(X0=min(_), X, X0-X, so_auto_cp:fin_minmax(X0, X)).
finalize_goal(X0=max(_), X, X0-X, so_auto_cp:fin_minmax(X0, X)).
finalize_goal(X0=count, _, X0-X0, true).
finalize_goal(X0=avg(_), X, X0-X, so_auto_cp:fin_avg(X0, X)).
finalize_goal(X0=time, X, X0-X, event_types:event_time(X0, X)).

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
            maplist(epsrev(F), Auto0.final, Es),
            mod_auto([a(epses, Es), a(skips, [skip(F, V, [])]), r(final, [F])], 
                     Auto0, Auto)
       }.

merge_states(S1, S2, S)
   :- S1 =.. [Sid1 | Vars1],
      S2 =.. [Sid2 | Vars2],
      term_to_atom(a(Sid1, Sid2), Sid),
      ord_union(Vars1, Vars2, Vars),
      S =.. [Sid | Vars].

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

merge_eps_(Dir, (eps(S0, Sub, S1) :- G), S, (eps(Sm0, Sub, Sm1) :- G))
   :- maplist(merge_states(Dir), [S0, S1], [S, S], [Sm0, Sm1]). 

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
   (trans(V, Type, pos(L), Sub, S0, S1):-G), 
   skip(S2, V1, L), 
   (trans(V, Type, pos([H|L]), Sub, Sm0, Sm1):-C, G)
) :-  maplist(merge_states(Dir), [S0, S1], [S2, S2], [Sm0, Sm1]),
      type_spec_cond(Type, L, C0),
      renumber_var(V1, V, C0, C),
      (Dir=left -> H = p(1) ; H = p(2)). 

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
   (eps(S0, Sub, S1) :- G1),
   (eps(S0, S2) :- G1)
) :- subst_state_(Sub, S1, S2).

subst_auto(Auto0, Auto)
   :- maplist(subst_, Auto0.trans, Trans),
      maplist(subst_, Auto0.epses, Epses),
      mod_auto([r(trans, Trans), r(epses, Epses)], Auto0, Auto).
