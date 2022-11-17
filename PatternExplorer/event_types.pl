:- module(event_types, [
        def_event_type/1, 
        def_event_types/1,
        ref/3,
        event_type/2,
        event_time/2,
        update_time/4,
        attr_dom/2,
        def_attr_domains/1,
        attr_type/2,
        attr_types/2,
        use_var/3,
        branch_types/3,
        list_unique/2
   ]).

:- use_module(library(varnumbers)).
:- use_module(library(ordsets)).
:- use_module('patterns_clpfd.pl').
:- use_module('time_constr.pl').
:- use_module('any_event.pl').
:- use_module(library(yall)).
:- use_module(library(assoc)).

update_time(a, T0, T1, _)
   :- T0 #= T1.
update_time(b, T0, T1, DT)
   :-  T1 #< T0 + DT.

:- dynamic attr_dom/2.
:- dynamic ref/3.
:- dynamic event_type/2.
:- dynamic type_domains/2.
:- dynamic attr_type/2.

event_time(Event, Time)
   :- (nonvar(Event)
      -> ref(Event, time, Time)
      ; time_constr(Event, Time)
   ).

def_attr_domains(Defs)
   :- maplist([attr_dom(A, D)]>>assertz((attr_dom(A, X) :- X in D, !)), Defs),
      maplist([attr_dom(A, _), A]>>true, Defs, Attrs),
      assertz(attr_dom(A, _) :- \+ member(A, Attrs)).

list_unique(L, OL)
   :- list_to_ord_set(L, OL),
      length(L, N1), 
      length(OL, N2),
      N1 #= N2.
   
def_event_type(ET)
     :- ET =.. [Type|Args],
        maplist({Type}/[Arg]>>assertz(attr_type(Arg, Type)), Args),
        list_unique(Args, _),
        foldl([_, '$VAR'(N0), N0, N]>>(N is N0 + 1),Args, Vars, 0,_),
        Event0 =.. [Type|Vars],
        varnumbers(Event0, Event),
        assert(event_type(Event, Type)),
        maplist(
            {Event0}/[Arg, Var]>>(
               varnumbers((ref(Event0, Arg, Var) :- attr_dom(Arg, Var)), R),
               assert(R)
            ), Args, Vars
        ).

def_event_types(ETs)
     :- maplist(def_event_type, ETs).

attr_types(Attr, Types)
   :- setof(Type, attr_type(Attr, Type), Types).

:- def_event_type(start(time)).

:- assertz((event_type(E, any) :- any_event(E))).
:- assertz(attr_type(time, any)).

/*
                Typing verification helpers
A variable can have the following typing:
   undefined - it was not yet either used or bound in the pattern, 
               so no type can be inferred. Useful only for input variables.
   scalar - a variable is used as scalar
   any([T₁, T₂, …, Tₙ]) a variable use must be consistent with one of types 
         T₁, T₂, …, Tₙ. List of types is really an ord_set.
   all([T₁, T₂, …, Tₙ]) a variable use must be consistent with all of the
              types T₁, T₂, …, Tₙ
*/
use_var(iter(Vars), A0, A)
   :- foldl([V, A0, A]>>put_assoc(V, A0, scalar, A),Vars, A0, A).
use_var(start(X), A0, A)
   :- put_assoc(X, A0, any([any]), A).
use_var(event(T, X), A0, A)
   :- put_assoc(X, A0, any([T]), A).
use_var('$VAR'(M), A0, A)
   :- get_assoc('$VAR'(M), A0, T0),
      (T0=undefined ; T0=scalar),
      put_assoc('$VAR'(M), A0, scalar, A).
use_var(ref(X, Attr), A0, A)
   :- get_assoc(X, A0, T0),
      attr_types(Attr, Types),
      update_type_(T0, Types, T),
      put_assoc(X, A0, T, A).

update_type_(undefined, L, any(L)) :- L=[_|_].
update_type_(any(L0), L1, any(L))
   :- ord_intersection(L0, L1, L),
      L = [_|_].
update_type_(all(L0), L1, all(L0)) :- ord_subset(L0, L1).

branch_types(scalar, scalar, scalar).
branch_types(all(L1), all(L2), all(L)) :- ord_union(L1, L2, L).
branch_types(all(L0), any([T]), all(L)) :- ord_add_element(L0, T, L).
branch_types(any([T]), all(L0), all(L)) :- ord_add_element(L0, T, L).
branch_types(any([T1]), any([T2]), all(L)) :- list_to_ord_set([T1, T2], L).


%unify_type(undefined, T, T).
%unify_type(T, undefined, T) :- dif(T, undefined).
%unify_type(scalar, scalar, scalar).
%unify_type(event(T1), event(T2), event(T))
%   :- ord_intersection(T1, T2, T),
%      T = [_|_].

%union_type(undefined, T, T).
%union_type(T, undefined, T) :- dif(T, undefined).
%union_type(scalar, scalar, scalar).
%union_type(event(T1), event(T2), event(T))
%   :- ord_union(T1, T2, T). 

%union_assocs(F, A1, A2, A)
%   :- assoc_to_list(A1, Pairs),
%      foldl(add_unify_(F), Pairs, A2, A).

%intersect_assocs(F, A1, A2, A)
%   :- assoc_to_keys(A1, Ks1),
%      assoc_to_keys(A2, Ks2),
%      ord_intersection(Ks1, Ks2, Ks),
%      maplist({F, A1, A2}/[K, K-V]>>(
%         get_assoc(K, A1, V1),
%         get_assoc(K, A2, V2),
%         call(F, V1, V2, V)
%      ), Ks, Pairs),
%      list_to_assoc(Pairs, A).

%dominate_assocs(A1, A2, A)
%   :- assoc_to_list(A2, Pairs),
%      foldl([K-V, X0, X]>>put_assoc(K, X0, V, X), Pairs, A1, A).

%union_types(A1, A2, A) :- union_assocs(unify_type, A1, A2, A).
%intersect_types(A1, A2, A) :- intersect_assocs(unify_type, A1, A2, A).

%add_unify_(F, K-V, A0, A)
%   :- (get_assoc(K, A0, V0) -> call(F, V0, V, V1) ; V1 = V), 
%      put_assoc(K, A0, V1, A).
