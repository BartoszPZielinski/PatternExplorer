:- module(compiler_state, [
        fresh_state//2,
        fresh_states//2,
        fresh_var//1,
        fresh_vars//1,
        event_fresh//2,
        current_vars//1,
        replace_vars//2,
        iter_var//2,
        last_matched//1,
        init_state/4,
        stack_vars//3
    ]).

:- use_module(library(clpfd)).

/*
  States a(N, M, Vars, Id, IterVar, IterCount, LastMatched), where:
     N - number used to create states,
     M - number used to create variables,
     Vars - set of current variables,
     Id - identifier of the currently compiled pattern
     IterVar - variable storing iteration stack,
     IterCount - variable storing iteration count stack
     LastMatched - variable storing last matched event
*/

state(S), [S] --> [S].
state(S0, S), [S] --> [S0].

fresh_state(S, Vs)
   --> state(a(N0, M0, Vars, Id, IterVar, IterCount, LastMatched), 
             a(N, M0, Vars, Id, IterVar, IterCount, LastMatched)),
       {
          N #= N0 + 1,
          term_to_atom(s(Id, N0), Sid),
          S =.. [Sid, IterVar, IterCount, LastMatched | Vs]
       }.

fresh_states([], []) --> [].
fresh_states([S|States], [Vs|Vss])
   --> fresh_state(S, Vs),
       fresh_states(States, Vss).

fresh_var('$VAR'(M0))
   --> state(a(N0, M0, Vars, Id, IterVar, IterCount, LastMatched), 
             a(N0, M, Vars, Id, IterVar, IterCount, LastMatched)),
       {M #= M0 + 1}.

fresh_vars([]) --> [].
fresh_vars([V|Vs])
   --> fresh_var(V),
       fresh_vars(Vs).

args_fresh_vars([], []) --> [].
args_fresh_vars([_|As], [V|Vs])
   --> fresh_var(V),
       args_fresh_vars(As, Vs).

event_fresh(Event0, Event)
   --> {
      Event0 =.. [Type | Args]
   }, args_fresh_vars(Args, Vs),
   {
      Event =.. [Type | Vs]
   }.

current_vars(Vars)
      --> state(a(_,_, Vars, _, _, _, _)).

replace_vars(Vars0, Vars)
   --> state(a(N, M, Vars0, Id, IterVar, IterCount, LastMatched), 
             a(N,M, Vars, Id, IterVar, IterCount, LastMatched)).

iter_var(IterVar, IterCount)
    --> state(a(_, _, _, _, IterVar, IterCount, _)).

stack_vars(IterVar, IterCount, LastMatched)
    --> state(a(_, _, _, _, IterVar, IterCount, LastMatched)).

last_matched(LastMatched)
   --> state(a(_, _, _, _, _, _, LastMatched)).

init_state(M0, Id, Vs0, [a(0, M, Vs, Id, '$VAR'(M0), '$VAR'(M1), '$VAR'(M2))])
    :-  M1 #= M0 + 1,
        M2 #= M1 + 1,
        M #= M2 +1,
        list_to_ord_set(Vs0, Vs).
        

