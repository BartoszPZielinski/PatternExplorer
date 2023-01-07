:- module(mk_list, [mk_list/2, mk_list/3]).

mk_list(Pairs, List) :- mk_list_(Pairs, List, 0, 1).

mk_list(Pairs, D, List)
    :- mk_list(Pairs,List0),
       maplist(add_(D), List0, List).

mk_list_([],[], _, _) :- !.
mk_list_([C-Delta|Pairs], [V|List], V0, K0)
    :- K0 =< C, !, V is V0 + Delta, K is K0 + 1, 
       mk_list_([C-Delta|Pairs], List, V, K).
mk_list_([C-_|Pairs], List, V, K)
    :- K > C, !, mk_list_(Pairs, List, V, 1).

add_(X, Y, Z) :- Z is X + Y.

