:- module(read_patterns, [assert_file/1]).

%:- use_module('pattern.pl').
:- use_module('patterns_clpfd.pl').
:- use_module('event_types.pl').
:- use_module(library(clpfd)).

assert_file_rec
:- read_term(Term, [variable_names(Vars), module('patterns_clpfd')]),
   proc_term_rec(Term, Vars).

proc_term_rec(end_of_file, _).
proc_term_rec(pattern(Id, Select), Vars)
    :- (closed_select(Select, _))
       -> (
            assertz(pattern:pattern(Id, Select, Vars)),  
            assert_file_rec
        ) ; (
            format('Pattern ~w is not closed~n', [Id]),
            halt    
        ).
proc_term_rec(example(Id, Example), Vars)
    :- assertz(pattern:example(Id, Example, Vars)),  
       assert_file_rec.
proc_term_rec(def_event_types(Types), _)
    :- def_event_types(Types),
       assert_file_rec.
proc_term_rec(def_attr_domains(Domains), _)
    :- def_attr_domains(Domains),
       assert_file_rec.

assert_file(File)
:- see(File),
   assert_file_rec,
   seen.