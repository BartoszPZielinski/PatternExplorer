:- module(skippable,[
    skippable/3
]).

:- use_module('event_types.pl').
:- use_module(library(clpfd)).

skippable(Event, V, Pairs)
    :- var(Pairs), !, 
       get_attr(Event, skippable, skip(V, Pairs)).

skippable(Event, V,  Pairs)
    :- put_attr(Y, skippable, skip(V, Pairs)),
       Event = Y.

attr_unify_hook(skip(VX, PairsX), Y) :-
(   get_attr(Y, skippable, skip(VY, PairsY))
->  VX=VY,
    unify_pairs(PairsX, PairsY, Pairs),
    put_attr(Y, skippable, skip(VY, Pairs))
;   var(Y)
->  put_attr( Y, skippable, skip(VX, PairsX))
;   event_type(Y, Type), dif(Type, any),
    VX = Y,
    verify_pairs(PairsX, Type)
).

/*verify_pairs([], _) :- !.
verify_pairs([Type-Cond|_],  Type)
    :- !, call(Cond).
verify_pairs([Type0-_|Pairs], Type)
    :- dif(Type0, Type), !, 
       verify_pairs(Pairs, Type).*/

verify_pairs([], _) :- !.
verify_pairs([any-Cond|Pairs], Type)
    :- !, call(Cond), verify_pairs(Pairs, Type).
verify_pairs([Type-Cond|Pairs],  Type)
    :- !, call(Cond), verify_pairs(Pairs, Type).
verify_pairs([Type0-_|Pairs], Type)
    :- dif(Type0, Type), dif(Type0, any), !, 
       verify_pairs(Pairs, Type).

unify_pairs([], Pairs, Pairs).
unify_pairs([P|Pairs0], Pairs1, Pairs)
    :- unify_pair(Pairs1, P, Pairs2),
       unify_pairs(Pairs0, Pairs2, Pairs).

unify_pair([], _, []).
unify_pair([Type0-C0|Pairs0], Type-C, [Type0-C0|Pairs])
    :- dif(Type0, Type), !, 
       unify_pair(Pairs0, Type-C, Pairs).
unify_pair([Type-C0|Pairs], Type-C, [Type-(C0, C)|Pairs]).

%       Translate attributes from this module to residual goals

attribute_goals(X) 
    --> { get_attr(X, skippable, skip(V, Pairs)) },
        [skippable(X, V, Pairs)].
