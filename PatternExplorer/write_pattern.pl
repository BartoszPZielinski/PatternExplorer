:- module(write_pattern, [
        pattern_lis/1,
        examples_html/1,
        html_solutions/4
    ]).

:- encoding(utf8).

:- use_module('patterns_clpfd.pl').
:- use_module('pattern.pl').

term_vars_atom(Term, Vars, Atom)
    :- with_output_to(
            atom(Atom), 
            write_term(Term, [variable_names(Vars)])
        ).

start_spaces_list(0, []).
start_spaces_list(N, ['   '|Spaces]) 
      :- N #> 0, N0 #= N - 1, start_spaces_list(N0, Spaces). 
start_spaces(N)
    --> {
            start_spaces_list(N, Spaces), 
            atomic_list_concat(Spaces, SpacAtom)
        }, [SpacAtom].
    

pattern_lines(Pattern, Vars, List)
    :- phrase(pattern_lines_(Pattern, Vars, 0), List).

pattern_lines_(event(Type, X), Vars, N)
    --> start_spaces(N), 
        {term_vars_atom(event(Type, X), Vars, Atom)}, 
        [Atom, '~n'-[]].

pattern_lines_(any(X), Vars, N)
--> start_spaces(N), 
    {term_vars_atom(any(X), Vars, Atom)}, 
    [Atom, '~n'-[]].

pattern_lines_(start(X), Vars, N)
--> start_spaces(N), 
    {term_vars_atom(start(X), Vars, Atom)}, 
    [Atom, '~n'-[]].

pattern_lines_(iter(P), Vars, N)
    --> start_spaces(N), ['iter(~n'-[]], 
        {N1 #= N + 1}, pattern_lines_(P, Vars, N1),
        start_spaces(N), [')~n'-[]].

pattern_lines_(iter(P, Event, X), Vars, N)
--> start_spaces(N), ['iter(~n'-[]], 
    {N1 #= N + 1}, pattern_lines_(P, Vars, N1),
    start_spaces(N), 
    {term_vars_atom(Event, Vars, Atom0),
     term_vars_atom(X, Vars, Atom1)},
    [', ', Atom0, ', ', Atom1, ')~n'-[]].

pattern_lines_(noskip(P, Event, Cond), Vars, N)
--> start_spaces(N), ['noskip(~n'-[]], 
    {N1 #= N + 1}, pattern_lines_(P, Vars, N1),
    start_spaces(N), 
    {term_vars_atom(Event, Vars, Atom0),
     term_vars_atom(Cond, Vars, Atom1)},
    [', ', Atom0, ', ', Atom1, ')~n'-[]].

pattern_lines_(filter(P, Cond), Vars, N)
--> start_spaces(N), ['filter(~n'-[]], 
    {N1 #= N + 1}, pattern_lines_(P, Vars, N1),
    start_spaces(N), 
    {term_vars_atom(Cond, Vars, Atom)},
    [', ', Atom, ')~n'-[]].

pattern_lines_(P1 or P2, Vars, N)
    --> start_spaces(N), ['(~n'-[]],
        {N1 #= N + 1, N2 #= N + 2}, 
        pattern_lines_(P1, Vars, N2),
        start_spaces(N1), ['or~n'-[]],
        pattern_lines_(P2, Vars, N2),
        start_spaces(N), [')~n'-[]].

pattern_lines_(P1 then P2, Vars, N)
--> start_spaces(N), ['(~n'-[]],
    {N1 #= N + 1, N2 #= N + 2}, 
    pattern_lines_(P1, Vars, N2),
    start_spaces(N1), ['then~n'-[]],
    pattern_lines_(P2, Vars, N2),
    start_spaces(N), [')~n'-[]].

pattern_lines_(P1 and P2, Vars, N)
--> start_spaces(N), ['(~n'-[]],
    {N1 #= N + 1, N2 #= N + 2}, 
    pattern_lines_(P1, Vars, N2),
    start_spaces(N1), ['and~n'-[]],
    pattern_lines_(P2, Vars, N2),
    start_spaces(N), [')~n'-[]].

pattern_lines_(select(In, Out, P), Vars, N)
--> {term_vars_atom(In, Vars, Atom0),
     term_vars_atom(Out, Vars, Atom1)},
    start_spaces(N), ['select(', Atom0, ', ', Atom1, ', ~n'-[]], 
    {N1 #= N + 1}, pattern_lines_(P, Vars, N1),
    start_spaces(N), [')~n'-[]].

make_id(Class, LocalId, Id)
    :- term_to_atom(LocalId, Id0),
       atomic_list_concat([Class, '_', Id0], Id).

pattern_link(Pid, a([href=PidLink], [PidAtom]))
    :- term_to_atom(Pid, PidAtom),
       make_id(p, Pid, Pid1),
       atom_concat('#', Pid1, PidLink).
       

pattern_li(
    pattern(Id, Pattern, Vars),
    li([id=FullId],
        [
            a([class='pattern-title', href=IdHref], ['Pattern', ' ', Id0]),
            pre(class='pattern-code',
               List    
            )
        ]
    )
) :- make_id(p, Id, FullId),
     atom_concat('#', FullId, IdHref),
     term_to_atom(Id, Id0),
     pattern_lines(Pattern, Vars, List).

pattern_lis(Lis)
    :- get_patterns(Patterns),
       maplist(pattern_li, Patterns, Lis).



example_html(
    example(Id, ex(Pid1, OutIn, Pid2), Vars),
    li([
        b(['Example ', AtomId, ':']), ' ',
        PidLink1, 
        ' ← ', InOutAtom, ' → ', 
        PidLink2, ' ',
        button(
            [name=id, value=AtomId],
            ['Explore solutions']    
        )
    ])
) :- term_to_atom(Id, AtomId),
     maplist(pattern_link, [Pid1, Pid2], [PidLink1, PidLink2]),
     term_vars_atom(OutIn, Vars, InOutAtom), !.

example_html(
    example(Id, ex(Pid, In), Vars),
    li([
        b(['Example ', AtomId, ':']), ' ',
        PidLink, 
        ' ← ', InAtom, ' ',
        button(
            [name=id, value=AtomId],
            ['Explore solutions']    
        )
    ])
) :- term_to_atom(Id, AtomId),
     pattern_link(Pid, PidLink), 
     term_vars_atom(In, Vars, InAtom), !.

example_html(
        example(Id, ex(Pid), _),
        li([
            b(['Example ', AtomId, ':']), ' ',
            'Pattern ',
            PidLink, ' ',
            button(
                [name=id, value=AtomId],
                ['Explore solutions']    
            )
        ])
) :- term_to_atom(Id, AtomId),
     pattern_link(Pid, PidLink), !. 

examples_html(ExamplesLis)
    :- get_examples(Examples),
       maplist(example_html, Examples, ExamplesLis).

path_mod_list_(X, X, []) :- var(X), !, fail.
path_mod_list_(skip, skip, []) :- !.
path_mod_list_(pos(L), pos(L), []) :- !.
path_mod_list_(pos(L, L1), pos(L), L1).

make_brs_([], []).
make_brs_([A|As0], [br([]),A|As]) :- make_brs_(As0, As).

term_vars_atom_(Vars, Short0, Short)
    :- term_vars_atom(Short0, Vars, Short).

pid_path_short(Pid, Path0, [Short|Shorts2])
    :- pattern(Pid, select(_, _, Pattern), Vars),
       path_mod_list_(Path0, Path, L),
       pattern_path_short(Pattern, Path, Short0),
       maplist(pattern_path_short(Pattern), L, Shorts0),
       term_vars_atom(Short0, Vars, Short),
       maplist(term_vars_atom_(Vars), Shorts0, Shorts1),
       make_brs_(Shorts1, Shorts2). 

pattern_path_short(_, skip, skip).
pattern_path_short(event(T, X), pos([]), event(T, X)).
pattern_path_short(any(X), pos([]), any(X)).
pattern_path_short(start(X), pos([]), start(X)).
pattern_path_short(P1 or _, pos([p(1) | L]), P1Short or '...')
    :- pattern_path_short(P1, pos(L), P1Short).
pattern_path_short(_ or P2, pos([p(2) | L]), '...' or P2Short)
    :- pattern_path_short(P2, pos(L), P2Short).
pattern_path_short(P1 then _, pos([p(1) | L]), P1Short then '...')
    :- pattern_path_short(P1, pos(L), P1Short).
pattern_path_short(_ then P2, pos([p(2) | L]), '...' then P2Short)
    :- pattern_path_short(P2, pos(L), P2Short).
pattern_path_short(P1 and _, pos([p(1) | L]), P1Short and '...')
    :- pattern_path_short(P1, pos(L), P1Short).
pattern_path_short(_ and P2, pos([p(2) | L]), '...' and P2Short)
    :- pattern_path_short(P2, pos(L), P2Short).
pattern_path_short(P1 and P2, pos([c(L1, L2)]), P1Short and P2Short)
    :- pattern_path_short(P1, pos(L1), P1Short),
       pattern_path_short(P2, pos(L2), P2Short).
pattern_path_short(filter(P, _), pos(L), filter(PShort, '...'))
    :- pattern_path_short(P, pos(L), PShort).
pattern_path_short(noskip(P, _, _), pos(L), noskip(PShort, '...', '...'))
    :- pattern_path_short(P, pos(L), PShort).
pattern_path_short(iter(P), pos([i(N) | L]), iter(PShort) * i(N))
    :- pattern_path_short(P, pos(L), PShort).
pattern_path_short(iter(P, _, X), pos([i(N) | L]), iter(PShort, '...', X) * i(N))
    :- pattern_path_short(P, pos(L), PShort).

html_solutions(ExId, MaxDepth, NSols, SolutionLis)
    :- numbered_solutions(ExId, MaxDepth, NSols, Sols),
       maplist(html_solution(ExId), Sols, SolutionLis).

html_solution(ExId, sol(Sid, SidAtom, L, MTrees, Goals), li([
    input([
        type=checkbox,
        id=SidAtom,
        class=invisible
    ], []),
    label([class='open-label', for=SidAtom], ['Solution ',  Sid]),
    div(class='accordion_item', [
        Table, 
        div([p('where'), pre(class=goals, GoalsPre)])    
    ])
])) :- goals_pre(Goals, GoalsPre),
       example(ExId, Example, _),
       stream_table(Example, L, MTrees, Table).

goals_pre([], []).
goals_pre([Goal | Goals], [GAtom, ',~n'-[] | GsAtom])
    :- term_to_atom(Goal, GAtom),
       goals_pre(Goals, GsAtom).

stream_table(ex(Pid1, _, Pid2), L, [MTree1, MTree2], div(table([
    thead([tr([
        th(['Pattern ', Pid1]),
        th(['Events']),
        th(['Pattern ', Pid2])
    ])]),
    tbody(TableLines)    
]))) :- maplist(stream_line2(Pid1-Pid2), MTree1, L, MTree2, TableLines), !.

stream_table(ex(Pid), L, [MTree], div(table([
    thead([tr([
        th(['Pattern ', Pid]),
        th(['Events'])
    ])]),
    tbody(TableLines)    
]))) :- maplist(stream_line1(Pid), MTree, L, TableLines), !.

stream_table(ex(Pid, _), L, [MTree], div(table([
    thead([tr([
        th(['Pattern ', Pid]),
        th(['Events'])
    ])]),
    tbody(TableLines)    
]))) :- maplist(stream_line1(Pid), MTree, L, TableLines), !.

stream_line2(Pid1-Pid2, Node1, Event, Node2, tr([
    td(Short1), td(EventAtom), td(Short2)
])) :- term_to_atom(Event, EventAtom),
       pid_path_short(Pid1, Node1, Short1),
       pid_path_short(Pid2, Node2, Short2).

stream_line1(Pid, Node, Event, tr([
    td(Short), td(EventAtom)
])) :- term_to_atom(Event, EventAtom),
       pid_path_short(Pid, Node, Short). 





