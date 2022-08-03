:- module(compiler_helpers, [
        append_pos/3,
        append_poss/3,
        term_trans_goals//3,
        glist_goals/2,
        cond_trans//2,
        sources_target_acc_epses/4,
        sources_target_cond_acc_epses/6,
        init_expr/2,
        update_goal/4,
        finalize_goal/4,
        mod_skip/5,
        append_iter/3,
        localize_auto//4,
        merge_states/3,
        skip_states/3,
        collect_lists/5,
        merge_eps_/5,
        merge_skips_/6,
        merge_trans_skip_/5,
        merge_trans_/4,
        extract_trans_states_/3,
        add_vars_to_auto/3,
        iter_init_sub/3,
        iter_update_sub_goals/4,
        iter_finalize_sub_goals/4,
        subst_auto/2
    ]).

:- use_module(library(clpfd)).
:- use_module(library(assoc)).
:- use_module('compiler_state.pl').

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

add_vars_to_auto(Vars, Auto0, auto{
        transitions: Ts,
        epses: Es,
        initial: I,
        skips: Skips,
        final: Fs
}) :- maplist(add_vars_to_el(Vars), Auto0.transitions, Ts),
      maplist(add_vars_to_el(Vars), Auto0.epses, Es),
      maplist(add_vars_to_el(Vars), Auto0.skips, Skips),
      maplist(add_vars_to_state(Vars), Auto0.final, Fs),
      add_vars_to_state(Vars, Auto0.initial, I).
      
%%%% Position helpers

append_poss(H, Ts0, Ts) :- maplist(append_pos(H), Ts0, Ts).

head_tail_pos_(_, skip, skip).
head_tail_pos_(H, pos(L), pos([H|L])).

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
   Translate conditions. Extract references ref(var, field, value)
*/

term_trans_goals(
   ref(Var, time),
   V,
   [event_time(Var, V)]
) --> fresh_var(V), !.


term_trans_goals(
    ref(Var, Field),
    V,
    [ref(Var, Field, V)]
 ) --> {dif(Field, time)}, fresh_var(V), !.

term_trans_goals(Cond, Trans, Goals)
   --> {
          Cond =.. [F|L], 
          dif(F, ref)
       },
       terms_trans_goals_(L, L1, Goals),
       {Trans =.. [F|L1]}.

terms_trans_goals_([],[],[]) --> [].
terms_trans_goals_([C|L],[T|L1], Gs)
--> term_trans_goals(C, T, G),
    terms_trans_goals_(L, L1, Gs0),
    {append(G, Gs0, Gs)}.

glist_goals([], true).
glist_goals([G], G).
glist_goals([G1, G2|Gs], (G1, Goals))
 :- glist_goals([G2|Gs], Goals).

cond_trans(Cond, Goals)
 --> term_trans_goals(Cond, T, Gs),
     {
       append(Gs, [T], Gs1),
       glist_goals(Gs1, Goals)
     }.

/*
   Renumbering variables
 */

renumber_var('$VAR'(N0), '$VAR'(N), '$VAR'(N0), '$VAR'(N)).
renumber_var('$VAR'(N0), _, '$VAR'(N), '$VAR'(N))
     :- N0 #\= N.
renumber_var('$VAR'(N0), '$VAR'(N), C0, C)
      :- C0 =.. [F|Args0],
         dif(F, '$VAR'),
         maplist(renumber_var('$VAR'(N0), '$VAR'(N)), Args0, Args),
         C =.. [F|Args].

/*
    Adding epses
 */

sources_target_acc_epses([], _, L, L).
sources_target_acc_epses([S|Ss], T, Acc, L)
    :- list_to_assoc([], Subst),
       sources_target_acc_epses(Ss, T, [(eps(S, skip, Subst, T) :- true)|Acc], L).

sources_target_cond_acc_epses([], _, _, _, L, L).
sources_target_cond_acc_epses([S|Ss], T,Sub, C, Acc, L)
    :- sources_target_cond_acc_epses(Ss, T, Sub, C, [(eps(S, skip, Sub, T) :- C)|Acc], L).

/*
    Iteration helpers
 */

iter_init_sub([CounterVar,Aggregate], EventT, SubInit)
   :- EventT =.. [Type|ExprList],
      maplist(init_expr, ExprList, InitList),
      InitEvent =.. [Type|InitList],
      list_to_assoc([CounterVar-0, Aggregate-InitEvent], SubInit).

iter_update_sub_goals(
   [CounterVar, Aggregate, CounterVar1], 
   EventT-GoalList0,
   EventFresh0-EventFresh,
   SubUpdate-Goals
) :- EventT =.. [_|ExprList],
     EventFresh0 =.. [_|Xs0],
     EventFresh =.. [_|Xs],
     maplist(update_goal, ExprList, Xs0, Xs, UpdGoalList0),
     append(GoalList0, UpdGoalList0, UpdGoalList1),
     glist_goals([
         (Aggregate=EventFresh0), 
         (CounterVar1 #= CounterVar + 1)
      |UpdGoalList1], Goals),
     list_to_assoc([CounterVar-CounterVar1, Aggregate-EventFresh], SubUpdate).

iter_finalize_sub_goals(
   [Aggregate, V],  
   EventT-GoalList0,
   EventFresh0-EventFresh,
   SubFin-Goals
) :- EventT =.. [_|ExprList],
     EventFresh0 =.. [_|Xs0],
     EventFresh =.. [_|Xs],
     maplist(finalize_goal, ExprList, Xs0, Xs, FinGoalList0),
     append(GoalList0, FinGoalList0, FinGoalList1),
     glist_goals([Aggregate=EventFresh0|FinGoalList1], Goals),
     list_to_assoc([V-EventFresh], SubFin).

init_expr(sum(_), 0).
init_expr(min(_), nothing).
init_expr(max(_), nothing).
init_expr(count(*), 1).
init_expr(avg(_), a(0,0)).

update_goal(sum(E), X0, X, X #= X0 + E).
update_goal(min(E), X0, X, so_auto_cp:ext_min(X0, E, X)).
update_goal(max(E), X0, X, so_auto_cp:ext_max(X0, E, X)).
update_goal(count(*), X0, X, X #= X0 + 1).
update_goal(avg(E), X0, X, so_auto_cp:update_avg(X0, E, X)).

finalize_goal(min(_), X0, X, X #= X0).
finalize_goal(min(_), X0, X, so_auto_cp:fin_minmax(X0, X)).
finalize_goal(max(_), X0, X, so_auto_cp:fin_minmax(X0, X)).
finalize_goal(min(_), X0, X, so_auto_cp:fin_minmax(X0, X)).
finalize_goal(count(*), X0, X, X #= X0).
finalize_goal(avg(_), X0, X, so_auto_cp:fin_avg(X0, X)).

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

merge_states(S1, S2, S)
   :- S1 =.. [Sid1, LastMatched|Vars1],
      S2 =.. [Sid2, LastMatched|Vars2],
      term_to_atom(a(Sid1, Sid2), Sid),
      ord_union(Vars1, Vars2, Vars),
      S =.. [Sid, LastMatched | Vars].

skipped_state(skip(State, _, _), State).

state_in(S0, [S1|_])
   :- S0 =.. [F|_],
      S1 =.. [F|_].
state_in(S0, [S1|L])
   :- S0 =.. [F1|_],
      S1 =.. [F2|_],
      dif(F1, F2),
      state_in(S0, L).

add_ifn_(S, States0, States)
   :- state_in(S, States0) 
         -> States=States0 
         ; States = [S|States0].

skip_states(Skips, I, States)
   :- maplist(skipped_state, Skips, States0),
      add_ifn_(I, States0, States).

localize_auto(Auto0, Auto, F, Vs)
   --> fresh_state(F, Vs),
       fresh_vars([V]),
       {
         sources_target_acc_epses(Auto0.final, F, Auto0.epses, Epses),
         Skips = [skip(F, V, [])|Auto0.skips],
         Auto = Auto0.put([final=[F], epses=Epses, skips=Skips])
       }. 

collect_lists([], _, _, Out, Out).
collect_lists([L0|Ls0], Ls1, F, Buf0, Out)
   :-  collect_list(Ls1, L0, F, Buf0, Buf1),
       collect_lists(Ls0, Ls1, F, Buf1, Out).
collect_list([], _, _, Out, Out).
collect_list([L1|Ls1], L0, F, Buf0, Out)
   :-  call(F, L0, L1, Buf0, Buf1),
       collect_list(Ls1, L0, F, Buf1, Out).

merge_eps_(Dir, (eps(S0, P0, Sub, S1) :- G), S, Buf, 
           [(eps(Sm0, P, Sub, Sm1) :- G)|Buf])
 :- merge_states(Dir, S0, S, Sm0),
    merge_states(Dir, S1, S, Sm1),
    dir_p_(Dir, H),
    head_tail_pos_(H, P0, P). 

merge_states(left, S1, S2, S) :- merge_states(S1, S2, S).
merge_states(right, S1, S2, S) :- merge_states(S2, S1, S).

merge_skips_(F1, F2, skip(S1, V1, L1), skip(S2, V2, L2),  Buf, Buf1)
 :- (S1=F1, S2=F2) -> (Buf1 = Buf) ; (
         merge_states(S1, S2, S),
         renumber_var(V1, V2, L1, L11),
         merge_specs(L11, L2, L),
         Buf1 = [skip(S, V2, L)|Buf]
      ). 

merge_specs([], Spec, Spec).
merge_specs([Pair|Spec0], Spec1, Spec)
:- merge_spec(Spec1, Pair, Spec2),
   merge_specs(Spec0, Spec2, Spec).

merge_spec([], Pair, [Pair]).
merge_spec([Type-Cond0|Spec0], Type-Cond, [Type-(Cond0, Cond)|Spec0]) 
:- !.
merge_spec([Type0-Cond0|Spec0], Type-Cond, [Type0-Cond0|Spec])
:- dif(Type0, Type),
   merge_spec(Spec0, Type-Cond, Spec).

dir_p_(left, p(1)).
dir_p_(right, p(2)).

merge_trans_skip_(
   Dir,
   (trans(V, Type, Pos0, Sub, S0, S1):-G), 
   skip(S2, V1, L), 
   Buf,
   [(trans(V, Type, Pos, Sub, Sm0, Sm1):-C, G)|Buf]
) :-  merge_states(Dir, S0, S2, Sm0),
      merge_states(Dir, S1, S2, Sm1),
      type_spec_cond(Type, L, C0),
      renumber_var(V1, V, C0, C),
      dir_p_(Dir, H),
      head_tail_pos_(H, Pos0, Pos).

type_spec_cond(_, [],  true).
type_spec_cond(Type, [Type-C|_], C) :- !.
type_spec_cond(Type, [Type1-_|L], C)
   :- dif(Type, Type1),
      type_spec_cond(Type, L, C).

combine_pos_(pos(L1), pos(L2), pos([c(L1, L2)])).

merge_trans_(
   (trans(V1, Type1, P1, Sub1, S10, S11) :- G1),
   (trans(V2, Type2, P2, Sub2, S20, S21) :- G2),
   Buf, Buf1
) :- (Type1 = Type2) -> (
         merge_states(S10, S20, S0),
         merge_states(S11, S21, S1),
         merge_assocs(Sub1, Sub2, Sub0),
         put_assoc(V2, Sub0, V1, Sub),
         combine_pos_(P1, P2, P),
         Buf1 = [(trans(V1, Type1, P, Sub, S0, S1) :- G1, G2)-S21|Buf]
     ) ; (Buf1 = Buf). 

merge_assocs_([], Assoc, Assoc).
merge_assocs_([Key-Value|Pairs], Assoc0, Assoc)
   :- put_assoc(Key, Assoc0, Value, Assoc1),
      merge_assocs_(Pairs, Assoc1, Assoc).
merge_assocs(Assoc0, Assoc1, Assoc)
   :- assoc_to_list(Assoc0, Pairs),
      merge_assocs_(Pairs, Assoc1, Assoc).

extract_trans_states_([],Result, Result).
extract_trans_states_([T-S|Pairs], Ts0-Ss0, Result)
   :- add_ifn_(S, Ss0, Ss),
      extract_trans_states_(Pairs, [T|Ts0]-Ss, Result).

%%% Final transformation of an automaton: applying substitutions in 
%%% transitions and epses.

sub_var_(Sub, Var, Value) :- 
   get_assoc(Var, Sub, Value) 
      -> true ; Value = Var.

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
   :- maplist(subst_, Auto0.transitions, Trans),
      maplist(subst_, Auto0.epses, Epses),
      Auto = Auto0.put([transitions=Trans, epses=Epses]).
