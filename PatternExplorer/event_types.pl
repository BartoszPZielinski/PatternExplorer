:- module(event_types, [
        def_event_type/1, 
        def_event_types/1,
        ref/3,
        event_type/2,
        event_time/2,
        update_time/4,
        attr_dom/2,
        def_attr_domains/1
   ]).

:- use_module(library(varnumbers)).
:- use_module(library(ordsets)).
%:- use_module(library(clpfd)).
:- use_module('patterns_clpfd.pl').
:- use_module('time_constr.pl').
:- use_module('any_event.pl').

update_time(a, T0, T1, _)
   :- T0 #= T1.
update_time(b, T0, T1, DT)
   :-  T1 #< T0 + DT.

:- dynamic attr_dom/2.
:- dynamic ref/3.
:- dynamic event_type/2.
:- dynamic type_domains/2.

event_time(Event, Time)
   :- (nonvar(Event)
      -> ref(Event, time, Time)
      ; time_constr(Event, Time)
   ).

extract_attr(attr_dom(A, _), A).


def_attr_domains(Defs)
   :- maplist(def_attr_domain, Defs),
      maplist(extract_attr, Defs, Attrs),
      assertz(attr_dom(A, _) :- \+ member(A, Attrs)).

def_attr_domain(attr_dom(A, D))
   :- assertz((attr_dom(A, X) :- X in D, !)).

 args_vars_next([],[], _).
 args_vars_next([_|Args], ['$VAR'(Next0)|Vars], Next0)
     :- Next #= Next0 + 1,
        args_vars_next(Args, Vars, Next).

assert_ref_args([], _, _).
assert_ref_args([Arg|Args], Event0, N0)
     :- varnumbers((ref(Event0, Arg, '$VAR'(N0)) :- attr_dom(Arg, '$VAR'(N0))), R),
        assert(R),
        N #= N0 + 1,
        assert_ref_args(Args, Event0, N).

def_event_type(ET)
     :- ET =.. [Type|Args],
        list_to_ord_set(Args, ArgsL),
        length(Args, N1),
        length(ArgsL, N2),
        N1 #= N2,
        args_vars_next(Args, Vars, 0),
        Event0 =.. [Type|Vars],
        varnumbers(Event0, Event),
        assert(event_type(Event, Type)),
        assert_ref_args(Args, Event0, 0).

def_event_types(ETs)
     :- maplist(def_event_type, ETs).



:- def_event_type(start(time)).

:- assertz((event_type(E, any) :- var(E), any_event(E))).