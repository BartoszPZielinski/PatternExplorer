:- module(compiler_state, [
        fresh_state//2,
        fresh_states//2,
        fresh_var//1,
        fresh_vars//1,
        current_vars//1,
        replace_vars//2,
        last_matched//1,
        init_state/4,
        add_var//3,
        term_trans_goals//3,
        terms_trans_goals_//3,
        glist_goals/2,
        cond_trans//2,
        renumber_var/4,
        args_fresh_vars//2
    ]).

:- use_module(library(clpfd)).
:- use_module(library(yall)).

/*
  States a(M, Vars, Id, LastMatched), where:
     M - number used to create variables and states
     Vars - set of current variables,
     Id - identifier of the currently compiled pattern
     LastMatched - variable storing last matched event
*/

state(S), [S] --> [S].
state(S0, S), [S] --> [S0].

fresh_state(S, Vs)
   --> state(a(M0, Vars, Id, LastMatched), 
             a(M, Vars, Id, LastMatched)),
       {
          M #= M0 + 1,
          term_to_atom(s(Id, M0), Sid),
          S =.. [Sid, LastMatched | Vs]
       }.

fresh_states(States, Vss, S0, S1) 
   :- foldl(fresh_state, States, Vss, S0, S1). 

fresh_var('$VAR'(M0))
   --> state(a(M0, Vars, Id, LastMatched), a(M, Vars, Id, LastMatched)),
       {M #= M0 + 1}.

fresh_vars(Vs, S0, S1) :- foldl(fresh_var, Vs, S0, S1).

args_fresh_vars(As, Vs, S0, S1)
   :- foldl([_, V, S0_, S1_]>>fresh_var(V, S0_, S1_), As, Vs, S0, S1).

current_vars(Vars)
      --> state(a(_, Vars, _, _)).

replace_vars(Vars0, Vars)
   --> state(a(M, Vars0, Id, LastMatched), 
             a(M, Vars, Id, LastMatched)).

add_var(Vars0, V, Vars)
   --> replace_vars(Vars0, Vars),
       {ord_add_element(Vars0, V, Vars)}.

last_matched(LastMatched)
   --> state(a(_, _, _, LastMatched)).

init_state(M0, Id, Vs0, [a(M, Vs, Id, LastMatched)])
    :-  M #= M0 +1,
        LastMatched = '$VAR'(M0),
        list_to_ord_set(Vs0, Vs). 
        
/*
   Translate conditions. Extract references ref(var, field, value)
*/

term_trans_goals(
   ref(Var, time), V, [event_time(Var, V)]
) --> fresh_var(V), !.

term_trans_goals(
    ref(Var, Field), V, [ref(Var, Field, V)]
 ) --> {dif(Field, time)}, fresh_var(V), !.

term_trans_goals(Cond, Trans, Goals)
   --> {Cond =.. [F|L], dif(F, ref)},
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

