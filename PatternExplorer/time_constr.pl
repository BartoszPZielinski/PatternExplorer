:- module(time_constr,[
    time_constr/2
]).

:- use_module('event_types.pl').
:- use_module(library(clpfd)).

time_constr(X, T)
    :- get_attr(X, time_constr, T1)
       -> T = T1
       ; (put_attr(Y, time_constr, T), X=Y).

attr_unify_hook(T0, Y)
    :- (   get_attr(Y, time_constr, T1)
        ->  T0 = T1
        ;   var(Y)
        ->  put_attr( Y, time_constr, T0 )
        ;   ref(Y, time, T0)
        ).

attribute_goals(X) 
    --> { get_attr(X, time_constr, T) },
        [time_constr(X, T)].



