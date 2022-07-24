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
        append_iters//2,
        localize_auto//5,
        merge_states//3,
        skip_states/3,
        collect_lists//5,
        merge_eps_//5,
        merge_skips_//6,
        merge_trans_skip_//5,
        merge_trans_//4,
        extract_trans_states_/3
    ]).

:- use_module(library(clpfd)).
:- use_module('compiler_state.pl').

append_poss(H, Ts0, Ts) :- maplist(append_pos(H), Ts0, Ts).

head_tail_pos_(_, skip, skip).
head_tail_pos_(H, pos(L), pos([H|L])).

append_pos(H, (trans(V, Type, P0, S0, S1) :- C), 
             (trans(V, Type, P, S0, S1) :- C))
   :- head_tail_pos_(H, P0, P).

append_pos(H, (eps(S0, P0, S1) :- C), (eps(S0, P, S1) :- C))
   :- head_tail_pos_(H, P0, P).

pos_then_else_res_(skip, _, X, X).
pos_then_else_res_(pos(_), X, _, X).

append_iter(
   CounterVar,
   (trans(V, Type, pos(L), S0, S1) :- G),
   (trans(V, Type, pos([i(CounterVar)|L]), S0, S1) 
            :- so_auto_cp:iter_counter(S0, CounterVar), G)
).

append_iter(CounterVar, 
   (eps(S0, P0, S1) :- G),
   (eps(S0, P, S1) :- Cond)
) :- head_tail_pos_(i(CounterVar), P0, P), 
     pos_then_else_res_(
         P0, (so_auto_cp:iter_counter(S0, CounterVar), G), G, Cond
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
    :- sources_target_acc_epses(Ss, T, [(eps(S, skip, T) :- true)|Acc], L).

sources_target_cond_acc_epses([], _, _, L, L).
sources_target_cond_acc_epses([S|Ss], T, C, Acc, L)
    :- sources_target_cond_acc_epses(Ss, T, C, [(eps(S, skip, T) :- C)|Acc], L).

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
--> stack_vars(IterVar, IterCount, LastMatched),
    {
      S1 =.. [Sid1|_],
      S2 =.. [Sid2|_],
      term_to_atom(a(Sid1, Sid2), Sid),
      S =.. [Sid, IterVar, IterCount, LastMatched, S1, S2]
    }.
   
reinit_state(S0, S)
:- S0 =.. [Sid, _, _, LastMatched | Vs],
   S =.. [Sid, [], [], LastMatched |Vs].

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

localize_auto(Auto0, Auto, I, F, Vs)
   --> stack_vars(IterVar, IterCount, _),
       fresh_state(F, Vs),
       fresh_vars([NewIter, NewCount, V]),
       {
         sources_target_acc_epses(Auto0.final, F, Auto0.epses, Epses),
         Skips = [skip(F, V, [])|Auto0.skips],
         Auto1 = Auto0.put([final=[F],
                            epses=Epses,
                            skips=Skips]),
         renumber_var(IterVar, NewIter, Auto1, Auto2),
         renumber_var(IterCount, NewCount, Auto2, Auto3),
         I = Auto3.initial,
         reinit_state(I, NewInitial),
         Auto = Auto3.put([initial=NewInitial])
    }. 

collect_lists([], _, _, Out, Out) --> [].
collect_lists([L0|Ls0], Ls1, F, Buf0, Out)
   --> collect_list(Ls1, L0, F, Buf0, Buf1),
       collect_lists(Ls0, Ls1, F, Buf1, Out).
collect_list([], _, _, Out, Out) --> [].
collect_list([L1|Ls1], L0, F, Buf0, Out)
   --> call(F, L0, L1, Buf0, Buf1),
       collect_list(Ls1, L0, F, Buf1, Out).

%

merge_eps_(Dir, (eps(S0, P0, S1) :- G), S, Buf, [(eps(Sm0, P, Sm1) :- G)|Buf])
--> merge_states(Dir, S0, S, Sm0),
    merge_states(Dir, S1, S, Sm1),
    {
      dir_p_(Dir, H),
      head_tail_pos_(H, P0, P)
    }.

merge_states(left, S1, S2, S)
   --> merge_states(S1, S2, S).
merge_states(right, S1, S2, S)
   --> merge_states(S2, S1, S).

%
merge_skips_(F1, F2, skip(S1, V1, L1), skip(S2, V2, L2),  Buf, Buf1)
--> {S1=F1, S2=F2} -> {Buf1 = Buf} ; (
      merge_states(S1, S2, S),
      {
         renumber_var(V1, V2, L1, L11),
         merge_specs(L11, L2, L),
         Buf1 = [skip(S, V2, L)|Buf]
      }
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

%

dir_p_(left, p(1)).
dir_p_(right, p(2)).

merge_trans_skip_(
   Dir,
   (trans(V, Type, Pos0, S0, S1):-G), 
   skip(S2, V1, L), 
   Buf,
   [(trans(V, Type, Pos, Sm0, Sm2):-C, G)|Buf]
) --> merge_states(Dir, S0, S2, Sm0),
      merge_states(Dir, S1, S2, Sm1),
      {
         type_spec_cond(Type, L, C0),
         renumber_var(V1, V, C0, C),
         dir_p_(Dir, H),
         head_tail_pos_(H, Pos0, Pos),
         matched_state_push_rec(V, Sm1, Sm2)
      }.

type_spec_cond(_, [],  true).
type_spec_cond(Type, [Type-C|_], C) :- !.
type_spec_cond(Type, [Type1-_|L], C)
   :- dif(Type, Type1),
      type_spec_cond(Type, L, C).

combine_pos_(pos(L1), pos(L2), pos([c(L1, L2)])).

merge_trans_(
   (trans(V1, Type1, P1, S10, S11) :- G1),
   (trans(V2, Type2, P2, S20, S21) :- G2),
   Buf, Buf1
) --> {Type1 = Type2} -> (
         merge_states(S10, S20, S0),
         merge_states(S11, S21, S1),
         {
            matched_state_push_rec(V2, S1, S2),
            combine_pos_(P1, P2, P),
            Buf1 = [(trans(V2, Type2, P, S0, S2) :- V1=V2, G1, G2)-S21|Buf]
         }
     ) ; {Buf1 = Buf}. 

extract_trans_states_([],Result, Result).
extract_trans_states_([T-S|Pairs], Ts0-Ss0, Result)
   :- add_ifn_(S, Ss0, Ss),
      extract_trans_states_(Pairs, [T|Ts0]-Ss, Result).

matched_state_push_rec(Event, S0, S)
   :- S0 =.. [Sid, IterVar, IterCount, _ | Vs0],
      read_term_from_atom(Sid, T, []),  
      (T = s(_,_) -> Vs = Vs0 
           ; maplist(matched_state_push_rec(Event), Vs0, Vs)),
      S  =.. [Sid, IterVar, IterCount, Event | Vs].

