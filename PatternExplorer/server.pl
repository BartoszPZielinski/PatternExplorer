:- use_module(library(http/http_server)).
:- use_module(library(http/html_write)).
:- use_module(library(http/http_parameters)).
:- use_module('pattern.pl').
:- use_module('write_pattern.pl').
:- use_module('read_patterns.pl').
:- use_module('patterns_clpfd.pl').

:- encoding(utf8).

server(Port, File) 
    :-  assert_file(File),
        compile_patterns,
        http_server(http_dispatch, [port(Port)]).


:- http_handler(root(.), listing, []).
:- http_handler(root(explore), explore, []).

:- http_handler('/style.css', http_reply_file('style.css', []), []).

:- multifile user:body//2.
:- multifile user:head//2.

user:head(default_style, Head)
    --> html(head([
        meta(charset='UTF-8', []),
        meta([name='viewport', content='width=device-width, initial-scale=1']),
        link([rel='preconnect', href='https://fonts.gstatic.com'],[]),
        link([
            %href='https://fonts.googleapis.com/css2?family=Inknut+Antiqua:wght@400;700&display=swap', 
            href='https://fonts.googleapis.com/css2?family=Audiowide&family=Roboto:wght@400;700&display=swap',
            rel='stylesheet'
        ],[]),
        link([href('/style.css'), rel('stylesheet')], [])
        | Head
     ])), html_root_attribute(lang, en).

user:body(default_style, Body)
    --> html(body(
            [
                header([
                    h1(
                        a([href('/'), class(header_link)], [
                          'PatternExplorer'
                        ])
                    )
                 ]),
                 div(class='main', Body),
                 footer(class='footer',
                     [
                         div([&(copy), 'Paweł Maślanka, Bartosz Zieliński'])
                     ]
                     )
            ]
        )).

listing(_)
    :-  pattern_lis(Lis),
        examples_html(ExamplesLis),
        reply_html_page(
            default_style,
            [title('List of examples | PatternExplorer')],
            [
                h2('List of tests'),
                h3('List of patterns'),
                ul(class='pattern-list', Lis),
                h3('List of tests'),
                form(
                    [action='/explore', method=get],
                    [
                        div(class=numforms,[
                            label(
                                [for=max_depth],
                                ['Set maximal length of solution: ']
                            ),
                            input(
                                [id=max_depth, type=number, 
                                 name=max_depth, value=10, min=1,max=200],
                                []
                            ), br([]),
                            label(
                                [for=sols],
                                ['Set maximal number of solutions: ']
                            ),
                            input(
                                [id=sols, type=number, 
                                 name=sols, value=3, min=1,max=20],
                                []
                            )
                        ]),
                        ul(class='examples-list', ExamplesLis)
                    ]
                )
            ]
        ).

explore(Request)
    :-  http_parameters(Request, [
            id(ExId, [nonneg]),
            max_depth(MaxDepth, [nonneg]),
            sols(NSols, [nonneg])
        ]),
        html_solutions(ExId, MaxDepth, NSols, SolutionLis),
        reply_html_page(
            default_style,
            [title('List of solutions | CEP Explorer')],
            [
                h2(['List of solutions for example ', ExId]),
                ul(class=solutions, SolutionLis)
            ]
        ).
