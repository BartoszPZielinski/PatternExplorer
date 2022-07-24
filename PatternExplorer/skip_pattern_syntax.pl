:- module(skip_pattern_syntax,[
    op(800, xfy, or),
    op(700, xfy, then),
    op(750, xfy, and),
    pattern_binds/2,
    closed/2,
    is_unique_pattern/1,
    make_pattern_unique/2
]).

:- use_module(library(ordsets)).
:- use_module(library(varnumbers)).
:- use_module(library(assoc)).
:- use_module(library(clpfd)).

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
noskip_pattern_(filter(P, _))
    :- noskip_pattern_(P).
noskip_pattern_(event(_,_)).

pattern_binds(event(_,X), [X]).
pattern_binds(start(X), [X]).
pattern_binds(any(X), [X]).
pattern_binds(iter(_), []).
pattern_binds(iter(_, _, X), [X]).
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
pattern_binds(noskip(Q, _, _), V)
     :- pattern_binds(Q, V).
pattern_binds(noskip(Q, _), V)
     :- pattern_binds(Q, V).


closed(Pattern, Binding)
   :- phrase(closed_(Pattern), [s([])], [s(Binding)]).

dlist_ordset(Ls, B)
    :- list_to_ord_set(Ls, B),
       length(Ls, N),
       length(B, M),
       N #= M.

cur_col(B), [s(B)] --> [s(B)].
old_new_col(B0, B), [s(B)] --> [s(B0)].
el_old_new(X, B0, B), [s(B)] --> [s(B0)],  {ord_add_element(B0, X, B)}.

closed_(event(_, X))
     --> el_old_new(X, _, _).
closed_(start(X))
     --> el_old_new(X, _, _).
closed_(any(X))
     --> el_old_new(X, _, _).
closed_(iter(P))
    --> cur_col(B0),
        closed_(P),
        old_new_col(_, B0).
closed_(iter(P, Event, X))
    --> cur_col(B0),
        closed_(P),
        closed_filter_(Event),
        old_new_col(_, B0),
        el_old_new(X, _, _).
closed_(filter(P, C))
   --> closed_(P),
       closed_filter_(C).
closed_(noskip(P, event(_, X), C))
   --> cur_col(B0),
       closed_(P),
       old_new_col(B1, B0),
       el_old_new(X, B0, _),
       closed_filter_(C),
       old_new_col(_, B1).
closed_(noskip(P, N))
    --> cur_col(B0),
        {noskip_pattern_(N)},
        closed_(N),
        old_new_col(_, B0),
        closed_(P).
closed_(P1 then P2)
   --> closed_(P1),
       closed_(P2).
closed_(P1 and P2)
   --> cur_col(B0),
       closed_(P1),
       old_new_col(B1, B0),
       closed_(P2),
       cur_col(B2),
       {ord_union(B1, B2, B)},
       old_new_col(_, B).
closed_(P1 or P2)
   --> cur_col(B0),
       closed_(P1),
       old_new_col(B1, B0),
       closed_(P2),
       cur_col(B2),
       {ord_intersection(B1, B2, B3)},
       old_new_col(_, B3).
closed_(select(Input, Output, Pattern))
    --> {
        Input =.. [_|VsIn],
        dlist_ordset(VsIn, B0)
    }, old_new_col(_, B0),
    closed_(Pattern),
    cur_col(B),
    {
        Output =.. [_|VsOut],
        dlist_ordset(VsOut, B1),
        ord_subset(B1, B)
    }.

closed_filter_(ref(X, _))
    --> cur_col(B),
        {ord_memberchk(X, B)}.
closed_filter_(C)
    --> {C =.. [F|Args], dif(F, ref)},
        closed_filter_list_(Args).
closed_filter_list_([]) --> [].
closed_filter_list_([A|Args])
    --> closed_filter_(A),
        closed_filter_list_(Args).

is_unique_pattern(Pattern)
    :- phrase(is_unique_pattern_(Pattern), [s([])], _).

is_fresh(X)
    --> el_old_new(X, Vars0, _),
        {\+ ord_memberchk(X, Vars0)}.

is_unique_pattern_(event(_, X))
    --> is_fresh(X).
is_unique_pattern_(any(X))
    --> is_fresh(X).
is_unique_pattern_(start(X))
    --> is_fresh(X).
is_unique_pattern_(iter(P))
    --> is_unique_pattern_(P).
is_unique_pattern_(iter(P, _, X))
    --> is_unique_pattern_(P),
        is_fresh(X).
is_unique_pattern_(filter(P, _))
    --> is_unique_pattern_(P).
is_unique_pattern_(noskip(P, E, _))
    --> is_unique_pattern_(P),
        is_unique_pattern_(E).
is_unique_pattern_(noskip(P, N))
--> is_unique_pattern_(P),
    {noskip_pattern_(N)},
    is_unique_pattern_(N).
is_unique_pattern_(P1 then P2)
    --> is_unique_pattern_(P1),
        is_unique_pattern_(P2).
is_unique_pattern_(P1 and P2)
    --> is_unique_pattern_(P1),
        is_unique_pattern_(P2).
is_unique_pattern_(P1 or P2)
    --> cur_col(Vars0),
        is_unique_pattern_(P1),
        old_new_col(Vars1, Vars0),
        is_unique_pattern_(P2),
        cur_col(Vars2),
        {
           pattern_binds(P1 or P2, Binds),
           ord_intersection(Vars1, Vars2, Common),
           ord_union(Vars0, Binds, Super),
           ord_subset(Common, Super),
           ord_union(Vars1, Vars2, Vars)
        },
        old_new_col(_, Vars).
is_unique_pattern_(select(Input, Output, Pattern))
    --> {
        Input =.. [_|VsIn],
        dlist_ordset(VsIn, B0)
    }, old_new_col(_, B0),
    is_unique_pattern_(Pattern),
    cur_col(B),
    {
        Output =.. [_|VsOut],
        dlist_ordset(VsOut, B1),
        ord_subset(B1, B)
    }.


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
    Make unique pattern.
    State: first unused var number,
     renaming from old vars (only visible binding vars) to new vars.
    The state u(N, Trans)
*/

fresh(N0), [u(N, Trans)]
     --> [u(N0, Trans)],
         {N #= N0 + 1}.
rename_old_to_new(V0, V), [u(N, A)]
      --> [u(N, A0)],
          {put_assoc(V0, A0, V, A)}.
renaming(A), [u(N, A)]
      --> [u(N, A)].
set_renaming(A0, A), [u(N, A)]
      --> [u(N, A0)].

combine(A0, A1, A2, A, AT)
    :- assoc_to_keys(A1, B1),
       assoc_to_keys(A2, B2),
       ord_intersection(B1, B2, B),
       empty_assoc(BindAssoc),
       empty_assoc(TransAssoc),
       combine_(A0, A1, A2, B, BindAssoc, A, TransAssoc, AT).

combine_(_, _, _, [], A, A, AT, AT).
combine_(A0, A1, A2, [B|Bs], BindAssoc0, A, TransAssoc0, AT)
    :- get_assoc(B, A1, V1),
       get_assoc(B, A2, V2),
       (
           (
               get_assoc(B, A0, V0),
               (V1 = V0 ; V2 = V0)
           ) -> (
                  put_assoc(B, BindAssoc0, V0, BindAssoc),
                  TransAssoc = TransAssoc0
           ) ; (
                  put_assoc(B, BindAssoc0, V1, BindAssoc),
                  put_assoc(V2, TransAssoc0, V1, TransAssoc)
           )
       ),
       combine_(A0, A1, A2, Bs, BindAssoc, A, TransAssoc, AT).

refill_and_(_, []) --> [].
refill_and_(A1, [B|Bs])
     --> {get_assoc(B, A1, V)},
         rename_old_to_new(B, V),
         refill_and_(A1, Bs).

make_pattern_unique(Pattern, Unique)
     :- numbervars(Pattern, 0, End),
        empty_assoc(A0),
        phrase(pattern_unique(Pattern, Unique0), [u(End, A0)], _),
        varnumbers(Unique0, Unique).

pattern_unique(event(T, '$VAR'(N)), event(T, '$VAR'(M)))
    --> fresh(M),
        rename_old_to_new(N, M).
pattern_unique(any('$VAR'(N)), any('$VAR'(M)))
    --> fresh(M),
        rename_old_to_new(N, M).
pattern_unique(start('$VAR'(N)), start('$VAR'(M)))
    --> fresh(M),
        rename_old_to_new(N, M).
pattern_unique(iter(P0), iter(P))
    --> renaming(A),
        pattern_unique(P0, P),
        set_renaming(_, A).
pattern_unique(iter(P0, Event0, '$VAR'(N)), iter(P, Event, '$VAR'(M)))
    --> renaming(A),
        pattern_unique(P0, P),
        set_renaming(A1, A),
        {term_vars_renamed(A1, Event0, Event)},
        fresh(M),
        rename_old_to_new(N, M).
pattern_unique(filter(P0, C0), filter(P, C))
    --> pattern_unique(P0, P),
        renaming(A),
        {term_vars_renamed(A, C0, C)}.
pattern_unique(noskip(P0, E0, C0), noskip(P, E, C))
    --> pattern_unique(P0, P),
        renaming(A0),
        pattern_unique(E0, E),
        renaming(A),
        {term_vars_renamed(A, C0, C)},
        set_renaming(_, A0).
pattern_unique(noskip(P0, N0), noskip(P, N))
--> {noskip_pattern_(N0)},
    renaming(A0),
    pattern_unique(N0, N),
    set_renaming(_, A0),
    pattern_unique(P0, P).
pattern_unique(P1 then P2, U1 then U2)
    --> pattern_unique(P1, U1),
        pattern_unique(P2, U2).
pattern_unique(P1 and P2, U1 and U2)
    --> renaming(A0),
        pattern_unique(P1, U1),
        set_renaming(A1, A0),
        pattern_unique(P2, U2),
        renaming(A2),
        {
           assoc_to_keys(A1, B1),
           assoc_to_keys(A2, B2),
           ord_subtract(B1, B2, B)
        },
        refill_and_(A1, B).
pattern_unique(P1 or P2, U1 or U2)
    --> renaming(A0),
        pattern_unique(P1, U1),
        set_renaming(A1, A0),
        pattern_unique(P2, U2_),
        renaming(A2),
        {
           combine(A0, A1, A2, A, AT),
           term_vars_renamed(AT, U2_, U2)
        },
        set_renaming(_, A).
pattern_unique(select(Input0, Output0, P0), select(Input, Output, P))
    --> {
        Input0 =.. [IN|VsIn0],
        dlist_ordset(VsIn0, _)
    }, rename_list_(VsIn0, VsIn),
    pattern_unique(P0, P),
    renaming(A),
    {
        Input =.. [IN|VsIn],
        term_vars_renamed(A, Output0, Output)
    }.
    

rename_list_([],[]) --> [].
rename_list_(['$VAR'(N)|Ls0], ['$VAR'(M)|Ls])
    --> fresh(M),
        rename_old_to_new(N, M),
        rename_list_(Ls0, Ls).
