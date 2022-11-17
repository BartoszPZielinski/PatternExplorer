:- module(skip_pattern_syntax,[
    op(800, xfy, or),
    op(700, xfy, then),
    op(750, xfy, and),
    pattern_binds/2,
    closed/2,
    closed_select/2,
    closed_select/3,
    is_unique_pattern/1,
    make_pattern_unique/2,
    aggr_vars/3
]).

:- use_module(library(ordsets)).
:- use_module(library(varnumbers)).
:- use_module(library(assoc)).
:- use_module(library(clpfd)).
:- use_module(library(yall)).
:- use_module('event_types.pl').

/*
    Syntax: pattern ::= any(X) | start(X) | event(typ, variable) | iter(pattern) |
    filter(pattern, condition)
    | noskip(pattern, event(type, variable), condition) |
    | noskip(pattern, noskip)|
    pattern₁ or pattern₂ | pattern₁ and pattern₂ | pattern₁ then pattern₂
*/

noskip_pattern_(P1 or P2)
    :- noskip_pattern_(P1),
       noskip_pattern_(P2).
noskip_pattern_(filter(P, _)) :- noskip_pattern_(P).
noskip_pattern_(event(_,_)).

aggr_vars(L, Xs, Es)
    :- maplist([X = E, X, E]>>true, L, Xs, Es),
       list_unique(Xs, _).

pattern_binds(event(_,X), [X]).
pattern_binds(start(X), [X]).
pattern_binds(any(X), [X]).
pattern_binds(iter(_), []).
pattern_binds(iter(_, L), Xs) :- aggr_vars(L, Xs, _).
pattern_binds(Q1 or Q2, V)
    :- pattern_binds(Q1, V1),
       pattern_binds(Q2, V2),
       ord_intersection(V1, V2, V).
pattern_binds(Q1 then Q2, V)
    :- pattern_binds(Q1, V1),
       pattern_binds(Q2, V2),
       ord_union(V1, V2, V).
pattern_binds(Q1 and Q2, V)
    :- pattern_binds(Q1, V1),
       pattern_binds(Q2, V2),
       ord_union(V1, V2, V).
pattern_binds(filter(Q, _), V)
     :- pattern_binds(Q, V).
pattern_binds(noskip(Q, _), V)
     :- pattern_binds(Q, V).

closed(Pattern, Types)
    :- empty_assoc(Empty),
       closed(Pattern, Empty, Types).

closed(event(T, X), Ts0, Ts) :- use_var(event(T, X), Ts0, Ts).
closed(start(X), Ts0, Ts) :- use_var(start(X), Ts0, Ts).
closed(any(X), Ts0, Ts) :- use_var(event(any,X), Ts0, Ts).
closed(iter(P), Ts0, Ts) :- closed(iter(P, []), Ts0, Ts).
closed(iter(P, List), Ts0, Ts)
    :- closed(P, Ts0, Ts1),
       aggr_vars(List, Vs, Es),
       foldl(closed_filter, Es, Ts1, _),
       use_var(iter(Vs), Ts0, Ts).
closed(filter(P, C), Ts0, Ts)
    :- closed(P, Ts0, Ts1),
       closed_filter(C, Ts1, Ts).
closed(noskip(P, N), Ts0, Ts)
    :- noskip_pattern_(N),
       closed(N, Ts0, _),
       closed(P, Ts0, Ts).
closed(P1 then P2, Ts0, Ts)
    :- closed(P1, Ts0, Ts1),
       closed(P2, Ts1, Ts).
closed(P1 and P2, Ts0, Ts) 
    :- closed(P1, Ts0, Ts1),
       closed(P2, Ts0, Ts2),
       assoc_to_list(Ts2, Pairs),
       foldl([K-V, X0, X]>>put_assoc(K, X0, V, X), Pairs, Ts1, Ts).
closed(P1 or P2, Ts0, Ts) 
    :- closed(P1, Ts0, Ts1),
       closed(P2, Ts0, Ts2),
       pattern_binds(P1, Vs1),
       pattern_binds(P2, Vs2),
       ord_intersection(Vs1, Vs2, Vs),
       foldl({Ts1, Ts2}/[V, Ts0, Ts]>>(
            get_assoc(V, Ts1, T1),
            get_assoc(V, Ts2, T2),
            branch_types(T1, T2, T),
            put_assoc(V, Ts0, T, Ts)
       ), Vs, Ts0, Ts).

closed_filter('$VAR'(N), Ts0, Ts) :- !, use_var('$VAR'(N), Ts0, Ts).
closed_filter(ref(X, Attr), Ts0, Ts) :- !, use_var(ref(X, Attr), Ts0, Ts).
closed_filter(C, Ts0, Ts)
    :- C =.. [F|Args], 
       dif(F, ref), dif(F, '$VAR'), !,
       foldl(closed_filter, Args, Ts0, Ts).

closed_select(S, OTypes)
    :- S = select(Input, _, _),
       Input =.. [_|VsIn],
       maplist([_, undefined]>>true, VsIn, ITypes),
       closed_select(S, ITypes, OTypes).

closed_select(S0, ITypes, OTypes)
    :- copy_term(S0, S),
       numbervars(S),
       S=select(Input, Output, Pattern),
       Input =.. [_|VsIn],
       list_unique(VsIn, _),
       maplist([V, Type, V-Type]>>true, VsIn, ITypes, Pairs),
       list_to_assoc(Pairs, A0),
       closed(Pattern, A0, A),
       Output =.. [_|VsOut],
       list_unique(VsOut, _),
       maplist({A}/[V, T]>>get_assoc(V, A, T), VsOut, OTypes).

is_fresh(X, Vs0, Vs) 
    :- ord_add_element(Vs0, X, Vs),
       \+ ord_memberchk(X, Vs0).

vars_cont_expr(Vs, '$VAR'(N)) :- ord_memberchk('$VAR'(N), Vs).
vars_cont_expr(Vs, E)
    :- E =.. [F|Args],
       dif(F, '$VAR'),
       maplist(vars_cont_expr(Vs), Args).

is_unique_pattern(Pattern) :- is_unique_pattern(Pattern, [], _).

is_unique_pattern(event(_, X), Vs0, Vs) :- is_fresh(X, Vs0, Vs).
is_unique_pattern(any(X), Vs0, Vs) :- is_fresh(X, Vs0, Vs).
is_unique_pattern(start(X), Vs0, Vs) :- is_fresh(X, Vs0, Vs).
is_unique_pattern(iter(P), Vs0, Vs) :- is_unique_pattern(P, Vs0, Vs).
is_unique_pattern(iter(P, L), Vs0, Vs)
    :- is_unique_pattern(P, Vs0, Vs1),
       aggr_vars(L, AVs, Es),
       foldl(is_fresh, AVs, Vs1, Vs),
       pattern_binds(P, PVs),
       ord_union(Vs0, PVs, Vs2),
       maplist(vars_cont_expr(Vs2), Es).
is_unique_pattern(filter(P, C), Vs0, Vs)
    :- is_unique_pattern(P, Vs0, Vs),
       pattern_binds(P, PVs),
       ord_union(PVs, Vs0, Vs1),
       vars_cont_expr(Vs1, C).
is_unique_pattern(noskip(P, N), Vs0, Vs)
    :- is_unique_pattern(P, Vs0, Vs1),
       noskip_pattern_(N),
       is_unique_pattern(N, Vs0, Vs2),
       ord_intersection(Vs1, Vs2, Vs0),
       ord_union(Vs1, Vs2, Vs).
is_unique_pattern(P1 then P2, Vs0, Vs)
    :- is_unique_pattern(P1, Vs0, Vs1),
       is_unique_pattern(P2, Vs1, Vs).
is_unique_pattern(P1 and P2, Vs0, Vs)
    :- is_unique_pattern(P1, Vs0, Vs1),
       is_unique_pattern(P2, Vs0, Vs2),
       ord_intersection(Vs1, Vs2, Vs0),
       ord_union(Vs1, Vs2, Vs).
is_unique_pattern(P1 or P2, Vs0, Vs)
    :- is_unique_pattern(P1, Vs0, Vs1),
       is_unique_pattern(P2, Vs0, Vs2),
       pattern_binds(P1 or P2, Binds),
       ord_union(Vs0, Binds, Common),
       ord_intersection(Vs1, Vs2, Common),
       ord_union(Vs1, Vs2, Vs).
is_unique_pattern(select(Input, Output, Pattern), _, Vs)
    :- Input =.. [_|VsIn],
       list_unique(VsIn, Vs0),
       is_unique_pattern(Pattern, Vs0, Vs),
       Output =.. [_|VsOut],
       list_unique(VsOut, Vs1),
       ord_subset(Vs1, Vs).

/*
    renaming (represented by assoc, requires numbered variables, assoc is from nats to nats)
*/

term_vars_renamed(Sub, '$VAR'(N), '$VAR'(M))
     :- get_assoc(N, Sub, M0) ->  M = M0 ; M = N.
term_vars_renamed(Sub, Term0, Term)
     :- Term0 =.. [F|Args0],
        dif(F, '$VAR'),
        maplist(term_vars_renamed(Sub), Args0, Args),
        Term =.. [F|Args].

/*
Composition A1 o A2|_Bind
*/

comb_bind(A1, A2, Bind, A)
    :- foldl({A2}/['$VAR'(X), B0, B]>>(
            get_assoc(X, A2, Y),
            put_assoc(X, B0, Y, B)
       ), Bind, A1, A).

/*
    Make unique pattern.
*/

make_pattern_unique(Pattern, Unique)
    :- numbervars(Pattern, 0, End),
       empty_assoc(A0),
       pattern_unique(Pattern, Unique0, End-A0, _),
       varnumbers(Unique0, Unique).

pattern_unique(event(T, X), event(T, Y), S0, S) :- ren_var_(X, Y, S0, S).
pattern_unique(any(X), any(Y), S0, S) :- ren_var_(X, Y, S0, S).
pattern_unique(start(X), start(Y), S0, S) :- ren_var_(X, Y, S0, S).
pattern_unique(iter(P0), iter(P), S0, S)
    :- pattern_unique(iter(P0, []), iter(P, []), S0, S).
pattern_unique(iter(P0, Ls0), iter(P, Ls), M0-A0, M-A)
    :- pattern_unique(P0, P, M0-A0, M1-A1),
       aggr_vars(Ls0, Vs0, Es0),
       foldl(ren_var_, Vs0, Vs, M1-A0, M-A),
       maplist({A1}/[F0, V, V=F]>>term_vars_renamed(A1, F0, F), Es0, Vs, Ls).
pattern_unique(filter(P0, C0), filter(P, C), S0, M-A)
    :- pattern_unique(P0, P, S0, M-A),
       term_vars_renamed(A, C0, C).
pattern_unique(noskip(P0, N0), noskip(P, N), M0-A0, M-A)
    :- noskip_pattern_(N0),
       pattern_unique(N0, N, M0-A0, M1-_),
       pattern_unique(P0, P, M1-A0, M-A).
pattern_unique(P1 then P2, U1 then U2, S0, S)
    :- pattern_unique(P1, U1, S0, S1),
       pattern_unique(P2, U2, S1, S).
pattern_unique(P1 and P2, U1 and U2, M0-A0, M-A)
    :- pattern_unique(P1, U1, M0-A0, M1-A1),
       pattern_unique(P2, U2, M1-A0, M-A2),
       pattern_binds(P2, Binds),
       comb_bind(A1, A2, Binds, A).
pattern_unique(P1 or P2, U1 or U2, M0-A0, M-A)
    :- pattern_unique(P1, U1, M0-A0, M1-A1),
       pattern_unique(P2, U2_, M1-A0, M-A2),
       pattern_binds(P1 or P2, Binds),
       comb_bind(A0, A1, Binds, A),
       maplist({A1, A2}/['$VAR'(X), X2-X1]>>(
            get_assoc(X, A1, X1),
            get_assoc(X, A2, X2)
        ), Binds, Pairs),
       list_to_assoc(Pairs, AT),
       term_vars_renamed(AT, U2_, U2). 
pattern_unique(select(Input0, Output0, P0), select(Input, Output, P), S0, M-A)
    :- Input0 =.. [IN|VsIn0],
       list_unique(VsIn0, _),
       foldl(ren_var_, VsIn0, VsIn, S0, S1),
       pattern_unique(P0, P, S1, M-A),
       Input =.. [IN|VsIn],
       term_vars_renamed(A, Output0, Output).

ren_var_('$VAR'(N), '$VAR'(M0), M0-A0, M-A)
    :- M #= M0 + 1,
       put_assoc(N, A0, M0, A).