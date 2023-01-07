:- use_module('../skip_pattern_syntax.pl').
:- use_module('../skip_pattern_compiler.pl').
:- use_module('../event_types.pl').
:- use_module('auto_simple.pl').
:- use_module('mk_list.pl').
:- use_module(library(statistics)).
:- use_module(library(csv)).
:- use_module(library(clpfd)).
:- use_module(library(random)).
:- use_module(library(yall)).
:- use_module(library(dialect/sicstus/timeout)).

random_stream(Size, Stream)
    :- random_stream(0, Size, Stream, 0).

random_stream(N, Max, [E|Es], T) 
    :- N =< Max, !, 
       random_event(E, T, T1), 
       N1 is N + 1, 
       random_stream(N1, Max, Es, T1).
random_stream(N, Max, [], _) :- N > Max, !.

all_event_types([
    stop_enter(id, stop_id, delta_schedule, time),
    stop_leave(id, stop_id, delta_schedule, time),
    abrupt_accel(id, time),
    abrupt_decel(id, time),
    sharp_turn(id, dir, time),
    driver_in(id, drv_id, time),
    driver_out(id, drv_id, time),
    location(id, location_id, time)
]).

random_event(E, T, T1)
    :- all_event_types(Types),
       random_member(X, Types),
       random_event(X, E, T, T1).

random_event(X, E, T, T1)
    :- X =.. [Type|Attributes],
       reverse(Attributes, [time|RAtts]),
       maplist(random_attribute, RAtts, Values0),
       random_between(1,20, T1),
       reverse([T|Values0], Values),
       E =.. [Type|Values].

random_attribute(id, V)
    :- random_between(1, 4, V).
random_attribute(stop_id, V)
    :- random_between(1, 4, V).
random_attribute(delta_schedule, V)
    :- random_between(1,200, V).
random_attribute(dir, V)
    :- random_member(V, [left, right]).
random_attribute(drv_id, V)
    :- random_between(1,4, V).
random_attribute(location_id, V)
    :- random_between(1,20, V).

/*
       Tests
 */

fnd_(Pred, Stream, Par, Sols, R) 
   :- time_out(findall(x, call(Pred, Stream, Par), Sols), 60000, R).

abstract_stream_search(Pred, ImplName, StreamSize, Par, Row)
    :- random_stream(StreamSize, Stream),
      call_time(fnd_(Pred, Stream, Par, Sols, Result), S),
      %call_with_time_limit(0.001, fnd_(Pred, Stream, Par, Sols, S)),
      ((nonvar(Result), Result = success) -> (
         length(Sols, NSols),
         Row = row(
            ImplName, success, StreamSize, Par, NSols, S.wall, S.cpu, S.inferences
         )
      ) ; Row = row(
         ImplName, timeout, StreamSize, Par, 0, 60.0,60.0,0
      )).

stream_search(p(Opt, StreamSize, Par), _, Row)
    :- abstract_stream_search(run_(Opt), Opt, StreamSize, Par, Row),
       format(user_error, 'Row=~w~n', [Row]).

stream_searches(P-Times, Rows)
    :- length(L, Times),
       maplist(stream_search(P), L, Rows).

run_(d20, Stream, Par) 
   :- Delta is 20 * Par, match_list_ns(1, Stream, _, inp(Par, Delta)).
run_(d40, Stream, Par) 
   :- Delta is 40 * Par, match_list_ns(2, Stream, _, inp(Par, Delta)).
run_(d20_nm, Stream, Par) 
   :- Delta is 20 * Par, match_list_ns(3, Stream, _, inp(Par, Delta)).
run_(d40_nm, Stream, Par) 
   :- Delta is 40 * Par, match_list_ns(4, Stream, _, inp(Par, Delta)).

compile_patterns
    :- pattern(1,Pattern01),
       pattern(1,Pattern02),
       pattern(2,Pattern03),
       pattern(2,Pattern04),
       make_pattern_unique_o(Pattern01, Pattern1),
       make_pattern_unique_o(Pattern02, Pattern2),
       make_pattern_unique_o(Pattern03, Pattern3),
       make_pattern_unique_o(Pattern04, Pattern4),
       assert_regular(1, Pattern1),
       assert_regular(2, Pattern2),
       assert_regular(3, Pattern3),
       assert_regular(4, Pattern4).

run_tests(CsvFile) 
    :-  def_attr_domains([]),
        all_event_types(Types), 
        def_event_types(Types),
        format(user_error, 'Patterns defined~n', []),
        compile_patterns,
        format(user_error, 'Patterns compiled~n', []),
        test_points(Ps),
        maplist(stream_searches, Ps, RowGroups),
        append(RowGroups, Rows0),
        Rows = [row(opt, success, size, parameter, nsols, wall, cpu, inferences)|Rows0],
        csv_write_file(CsvFile, Rows),
        format(user_error, 'Data written~n', []),!,
        halt.


make_point_(Type, Par, Size, p(Type, Size, Par)-10).

type_points_(t(Type, List), Points) 
   :- maplist(par_points_(Type), List, Points0),
      append(Points0, Points). 
par_points_(Type, x(Par, D,  Pairs), Points)
   :- mk_list(Pairs, D, Sizes),
      maplist(make_point_(Type, Par), Sizes, Points).

test_points(Points)
   :- test_points_spec_(Spec),
      maplist(type_points_, Spec, Points0),
      append(Points0, Points).

test_points_spec_([
   t(d20_nm, [
      x(1,0,[4-200, 10-1000]),
      x(3, 10, [4-500, 8-1000]),
      x(5, 20, [10-1000]),
      x(7, 30, [10-1000])
   ]),
   t(d40_nm, [
      x(1,0,[4-200, 10-1000]),
      x(3, 10, [4-500, 8-1000]),
      x(5, 20, [10-1000]),
      x(7, 30, [10-1000])
   ]),
   t(d20, [
      x(1,0,[2-300, 5-500]),
      x(3,30,[2-300, 5-500])
   ]),
   t(d40, [
      x(1,0,[2-300, 5-500]),
      x(3,30,[2-300, 5-500])
   ])
]).

pattern(1, select(inp(P, Delta), out,
   filter(event(stop_enter, Se), ref(Se, delta_schedule) #>= 120)
      then
   noskip(
      filter(
         event(stop_leave, Sl), 
         ref(Sl, id) #= ref(Se, id) #/\ ref(Se, stop_id) #= ref(Sl, stop_id)
      ),
      filter(
         event(stop_leave, S_) or event(driver_in, S_), ref(S_, id) #= ref(Se, id)
      )
   ) 
      then
   noskip(
      filter(
         iter(
            filter(event(abrupt_accel, E) 
                     or event(abrupt_decel, E)
                     or  event(sharp_turn, E), 
                  ref(E, id) #= ref(Se, id) #/\ ref(E, time) #< ref(Sl, time) + Delta
            ),
            [Count = count]
         ), Count #= P
      ),
      filter(event(stop_enter, T), ref(T, id) #= ref(Se, id)) 
   )
)).

pattern(2, select(inp(P, Delta), out,
   filter(event(stop_enter, Se), ref(Se, delta_schedule) #>= 120)
      then
   noskip(
      filter(
         event(stop_leave, Sl), 
         ref(Sl, id) #= ref(Se, id) #/\ ref(Se, stop_id) #= ref(Sl, stop_id)
      ),
      filter(
         event(stop_leave, S_) or event(driver_in, S_), ref(S_, id) #= ref(Se, id)
      )
   ) 
      then
   noskip(
      filter(
         iter(
            filter(
               event(abrupt_accel, E)
                  or event(abrupt_decel, E) or event(sharp_turn, E),
               ref(E, id) #= ref(Se, id) #/\ ref(E, time) #< ref(Sl, time) + Delta
            ),
            [Count = count]
         ), Count #= P
      ),
      filter(
         event(stop_enter, T) or event(abrupt_accel, T) 
            or event(abrupt_decel, T) or event(sharp_turn, T), 
         ref(T, id) #= ref(Se, id)
      )
         or 
      filter(event(any, A), ref(A, time) #>= ref(Sl, time) + Delta)
   ) 
)).

%Run run_tests('test.csv') in the command prompt

