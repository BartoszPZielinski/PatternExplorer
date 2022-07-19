def_attr_domains([
   attr_dom(time, 0..200),
   attr_dom(delta_schedule, 0..200)   
]).


def_event_types([
    /* The bus id enters/leaves stop identified by stop_id.
       the difference between scheduled time and current time is delta_schedule
       current time is time */
    stop_enter(id, stop_id, delta_schedule, time),
    stop_leave(id, stop_id, delta_schedule, time),
    /* Events emitted at abrubt acceleration/deceleration of
       bus id at time time */
    abrupt_accel(id, time),
    abrupt_decel(id, time),
    /* The bus id made a sharp turn to dir (left/right) at time time */
    sharp_turn(id, dir, time),
    /* Driver logs in/out to the bus */
    driver_in(id, drv_id, time),
    driver_out(id, drv_id, time),
    /* The bus id reports max, min, and avg velocity between times start_time 
       and time. */
    velocity(id, max, min, avg, start_time, time),
    /* The bus id reports location location_id at time time.*/
    location(id, location_id, time),
    /* Events used for aggregation only */
    agg(cnt),
    /* Parameter event */
    lambda(par)
]).

pattern(-1,  select(in, out, 
filter(event(location, X), ref(X, location_id) #> 10) 
)).
pattern(0, select(in, out, event(location, X))).
pattern(1, select(in, out, 
        filter(event(location, X), ref(X, location_id) #= 10)
   )).
pattern(2, select(in, out, 
        filter(event(location, X), ref(X, location_id) #= 10) or event(velocity, X)
   )).
pattern(3, select(in, out, 
        filter(
           filter(event(location, X), ref(X, location_id) #= 10) 
                 or event(velocity, X),
           ref(X, time) #> 10
        )
   )).
pattern(4, select(in, out, 
        filter(
           filter(event(location, X), ref(X, location_id) #= 10) 
                 or event(velocity, X),
           ref(X, time) #> 10
        ) then event(driver_in, Y)
   )).

pattern(5, select(in, out, 
   filter(
        filter(
           filter(event(location, X), ref(X, location_id) #= 10) 
                 or event(velocity, X),
           ref(X, time) #> 10
        ) then event(driver_in, Y),
        ref(Y, id) #= ref(X, id)
   )
   )).

pattern(6, select(in, out, 
    event(driver_in, X) then noskip(
             event(abrupt_accel, Y), event(abrupt_accel, Z),
             ref(X, id) = ref(Z, id) 
       )
)).

pattern(7, select(in, out, 
   iter(event(driver_in, X))
)).

pattern(8, select(in, out, 
   filter(iter(event(driver_in, X), agg(count(*)), Y), 
   ref(Y, cnt) #=3
)
)).





pattern(10, select(inp, out(Se, K),
filter(event(stop_enter, Se), ref(Se, delta_schedule) #>= 120) then noskip(
   noskip(
      filter(
         event(stop_leave, Sl), 
         ref(Sl, id) #= ref(Se, id) #/\ ref(Se, stop_id) #= ref(Sl, stop_id)
      ),
      event(stop_leave, L),
      ref(L, id) #= ref(Se, id)
   ), 
   event(driver_in, Di),
   ref(Di, id) #= ref(Se, id)
) then noskip(
      filter(
         iter(
            filter(
               event(abrupt_accel, E) or 
               event(abrupt_decel, E) or 
               event(sharp_turn, E),
               ref(E, id) #= ref(Se, id) 
            ),
            agg(count(*)), 
            I
         ), ref(I, cnt) #>= 3
      ) then filter(
            event(stop_enter, K), ref(K, id) #= ref(Se, id)
      ),
      event(stop_enter, T),
      ref(T, id) #= ref(Se, id)
)
)).

pattern(11, select(inp(Se, K), out, 
   filter(
      event(driver_in, D), 
      ref(D, id) #= ref(Se, id) #/\ 
         ref(D, time) #> ref(Se, time) #/\
         ref(D, time) #< ref(K, time)
   )
)).

pattern(12, select(inp(X), out, 
    filter(event(driver_in, Y),
      ref(Y, id) #= ref(X, id)
   )
)).

pattern(20, select(inp, out, 
   event(driver_in, X) then 
   start(Y) then 
   filter(event(driver_out, Z), ref(Y, id) #= ref(Z, id)) 
)).

pattern(21, select(inp, out, 
   event(driver_in, X) then start(Y) 
)).

pattern(31, select(inp, out, 
    noskip(
       filter(event(driver_in, X), ref(X, id) #= 1),
       event(driver_out, Y), ref(Y, id) #= 1)
)).

pattern(32, select(inp, out, 
    filter(event(driver_out, Z), ref(Z, id) #= 1)
)).

pattern(100, select(inp(Lambda), out(D, M),
    event(driver_in, D) then
    filter(
      iter(
         noskip(
             filter(
                event(abrupt_decel, AD),
                ref(AD, id) #= ref(D, id)
             ), event(driver_out, D2), ref(D2, drv_id) #= ref(D, drv_id)
         ), agg(count(*)), C
      ),
      ref(C, cnt) #= ref(Lambda, par)  
    ) then start(M)
)).

pattern(101, select(inp(D, M, Lambda), out, 
     filter(
         iter(
            filter(
               event(sharp_turn, S),
               ref(S, id) #= ref(D, id) #/\
               ref(S, time) #> ref(D, time) #/\ 
               ref(S, time) #< ref(M, time)
            ), agg(count(*)), H 
         ),
         ref(H, cnt) #= ref(Lambda, par) 
      )
)).

pattern(102, select(inp(D, M, Lambda), out, 
     filter(event(driver_in, D1), 
          ref(D1, time) #= ref(D, time)) then 
     filter(
         iter(
            filter(
               event(sharp_turn, S),
               ref(S, id) #= ref(D, id) #/\
               ref(S, time) #< ref(M, time)
            ), agg(count(*)), H 
         ),
         ref(H, cnt) #= ref(Lambda, par) 
      )
)).

pattern(200, select(inp, out, event(driver_in, X) and event(sharp_turn, S))).

pattern(201, select(inp, out, 
   filter(event(stop_enter, X), ref(X, id) #= 1) then (
      filter(
         start(Y) then event(driver_in, D),
         ref(D, id) #= ref(Y, id)   
      ) and filter(event(sharp_turn, S), ref(S, id) #=2) 
   )
)).


pattern(202, select(inp, out, 
   (
      filter(event(stop_enter, X), ref(X, id) #= 5)
      and 
      filter(event(stop_leave, Y), ref(Y, id) #=10)
   ) then filter(
      start(Z) then event(sharp_turn, T), 
      ref(Z, id) #= ref(T, id)
   )   
)).

pattern(203, select(inp, out, 
   (iter(event(stop_enter, X)) and event(driver_in, Y)) then filter(
      start(Z) then event(sharp_turn, T), 
      ref(Z, id) #= ref(T, id)
   )   
)).

example(1, ex(10, out(X, T)-inp(X, T), 11)).
example(2, ex(0)).
example(3, ex(1)).
example(4, ex(2)).
example(5, ex(3)).
example(6, ex(4)).
example(7, ex(5)).
example(8, ex(6)).
example(9, ex(7)).
example(10, ex(10)).
example(11, ex(8)).
example(20, ex(5, out-in, 0)).
example(21, ex(12, inp(driver_in(10, _, _)))).
example(30, ex(20)).
example(31, ex(21)).
example(32, ex(31, out-inp, 32)).
example(100, ex(100, inp(lambda(3))-out(D, M)-inp(D, M, lambda(3)), 101)).
example(101, ex(100, inp(lambda(3))-out(D, M)-inp(D, M, lambda(3)), 102)).
example(200, ex(200)).
example(201, ex(201)).
example(202, ex(202)).
example(203, ex(203)).