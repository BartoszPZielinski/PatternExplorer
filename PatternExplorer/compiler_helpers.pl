:- module(compiler_helpers, [
        append_pos/3,
        append_poss/3,
        frame_state_push/3,
        matched_state_push/3,
        term_trans_goals//3,
        glist_goals/2,
        cond_trans//2,
        sources_target_acc_epses/4,
        sources_target_cond_acc_epses/5,
        init_expr/2,
        update_goal/4,
        finalize_goal/4,
        mod_skip/5,
        count_state_push/3,
        append_iter/3,
        append_iters//2
    ]).

:- use_module(library(clpfd)).
:- use_module('compiler_state.pl').

append_pos(H, (trans(V, Type, pos(L0), S0, S1) :- C), 
             (trans(V, Type, pos(L), S0, S1) :- C))
   :- append(H, L0, L).

append_poss(H, Ts0, Ts) :- maplist(append_pos(H), Ts0, Ts).

append_iter(
   CounterVar,
   (trans(V, Type, pos(L), S0, S1) :- G),
   (trans(V, Type, pos([i(CounterVar)|L]), S0, S1) 
            :- so_auto_cp:iter_counter(S0, CounterVar), G)
).

append_iters(T0, T)
   --> fresh_var(CounterVar),
       {maplist(append_iter(CounterVar), T0, T)}.

frame_state_push(Frame, S0, S)
:- S0 =.. [Sid, IterVar | Vs],
   S  =.. [Sid, [Frame | IterVar] | Vs].

matched_state_push(Event, S0, S)
:- S0 =.. [Sid, IterVar, IterCount, _ | Vs],
   S  =.. [Sid, IterVar, IterCount, Event | Vs].

count_state_push(Count, S0, S)
:- S0 =.. [Sid, IterVar, IterCount| Vs],
   S  =.. [Sid, IterVar, [Count | IterCount] | Vs].

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
    :- sources_target_acc_epses(Ss, T, [(eps(S, T) :- true)|Acc], L).

sources_target_cond_acc_epses([], _, _, L, L).
sources_target_cond_acc_epses([S|Ss], T, C, Acc, L)
    :- sources_target_cond_acc_epses(Ss, T, C, [(eps(S, T) :- C)|Acc], L).

/*
    Iteration helpers
 */

init_expr(sum(_), 0).
init_expr(min(_), nothing).
init_expr(max(_), nothing).
init_expr(count(*), 0).
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

%init_expr(max(_), nothing).
%update_goal(max(E), X0, X, ext_max(X0, E, X)).


/*
    Unless helpers
 */

mod_skip(Type, V0, C0, skip(S, V, L0), skip(S,  V, L))
:- renumber_var(V0, V, C0, C),
   mod_or_add_skip_rules(Type, C, L0, L).

mod_or_add_skip_rules(Type, C, [], [Type-C]).
mod_or_add_skip_rules(Type, C, [Type-C0 | L0], [Type-(C, C0) |L0]).
mod_or_add_skip_rules(Type, C, [Type0-C0 | L0], [Type0-C0 | L])
:- dif(Type, Type0),
   mod_or_add_skip_rules(Type, C, L0, L).
