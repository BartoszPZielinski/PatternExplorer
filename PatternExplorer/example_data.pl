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
    location(id, location_id, time)
]).


pattern(0, select(in, out, event(location, X))).

pattern(1,  select(in, out, 
       filter(event(location, X), ref(X, location_id) #> 10) 
)).

pattern(2, select(in, out, 
       filter(event(abrupt_accel, X), ref(X, time) #< 10) 
)).

pattern(3, select(in, out, 
        filter(event(location, X), ref(X, time) #< 10)
      then event(velocity, Y)
)).
pattern(4, select(in, out, 
        filter(event(location, X), ref(X, location_id) #= 10) 
            or filter(event(location, X), ref(X, location_id)#=20)
)).
pattern(5, select(in, out, 
        filter(
           event(velocity, X) or
           event(location, X),
           ref(X, time) #> 10
        )
   )).
pattern(6, select(in, out, 
        filter(
           filter(event(location, X), ref(X, location_id) #= 10) 
                 or event(velocity, X),
           ref(X, time) #> 10
        ) then event(driver_in, Y)
)).

pattern(7, select(in, out, 
   filter(
        filter(
           filter(event(location, X), ref(X, location_id) #= 10) 
                 or event(velocity, X),
           ref(X, time) #> 10
        ) then event(driver_in, Y),
        ref(Y, id) #= ref(X, id)
   )
   )).

pattern(8, select(in, out, 
    event(driver_in, X) then noskip(
             event(abrupt_accel, Y), 
             filter(event(abrupt_accel, Z), ref(X, id) #= ref(Z, id)) 
       )
)).

pattern(9, select(in, out, 
   iter(filter(event(driver_out, Y), ref(Y, id)#=1))
)). 

pattern(10, select(in, out, 
   filter(iter(event(driver_in, X), [Count=count]), Count #< 3)
)).

pattern(11, select(in, out, 
      iter(filter(event(driver_in, X), ref(X, id) #=1), []) 
)).

pattern(12, select(inp, out, 
   event(driver_in, X) and filter(event(sharp_turn, S), ref(S, id) #=1)
)).

pattern(13, select(inp, out, 
   event(sharp_turn, Y) and
   (event(stop_enter, X) or event(stop_leave, T)) 
)).

pattern(14, select(inp, out, 
   noskip(iter(event(stop_enter, X)), event(any, Z))
   and 
   event(stop_leave, Y)
)).

pattern(15, select(inp, out,
   noskip(event(stop_enter, X), 
      filter(
         event(stop_leave, Y) or event(sharp_turn, Y),
         ref(Y, id) #= 1
      )
   )
)).



pattern(50, select(inp, out(X), event(stop_enter, X))).
pattern(51, select(inp(X, T), out, 
   filter(event(stop_leave, Y), ref(X, id) #= ref(Y, id) #/\ ref(Y, time) #= T)
)).

pattern(60, select(inp(P), out(Se, K),
   filter(event(stop_enter, Se), ref(Se, delta_schedule) #>= 120)
      then
   noskip(
      filter(
         event(stop_leave, Sl), 
         ref(Sl, id) #= ref(Se, id) #/\ ref(Se, stop_id) #= ref(Sl, stop_id)
      ),
      filter(
         event(stop_leave, S_) or event(driver_in, S_),
         ref(S_, id) #= ref(Se, id)
      )
   ) 
      then
   noskip(
      filter(
         iter(
            filter(
               event(abrupt_accel, E) or 
               event(abrupt_decel, E) or 
               event(sharp_turn, E),
               ref(E, id) #= ref(Se, id) #/\ ref(E, time) #< ref(Se, time) + 20
            ),
            [Count = count]
         ), Count #=< P
      ) 
         then
      filter(event(stop_enter, K), ref(K, id) #= ref(Se, id)),
      filter(event(stop_enter, T), ref(T, id) #= ref(Se, id))
   ) 
)).

pattern(61, select(inp(Se, K), out, 
   filter(
      event(driver_in, D), 
      ref(D, id) #= ref(Se, id) #/\ 
         ref(D, time) #> ref(Se, time) #/\
         ref(D, time) #< ref(K, time)
   )
)).

pattern(31, select(inp, out, 
    noskip(
       filter(event(driver_in, X), ref(X, id) #= 1),
       filter(event(driver_out, Y), ref(Y, id) #= 1)
    )
)).

pattern(32, select(inp, out, 
    filter(event(driver_out, Z), ref(Z, id) #= 1)
)).

pattern(100, select(inp(Lambda), out(D, Time),
    event(driver_in, D) then
    filter(
      iter(
         noskip(
             filter(
                event(abrupt_decel, AD),
                ref(AD, id) #= ref(D, id)
             ), filter(event(driver_out, D2), ref(D2, drv_id) #= ref(D, drv_id))
         ), [Count=count, Time=time]
      ),
      Count #= Lambda 
    ) 
)).

pattern(101, select(inp(D, Time, Lambda), out, 
     filter(
         iter(
            filter(
               event(sharp_turn, S),
               ref(S, id) #= ref(D, id) #/\
               ref(S, time) #> ref(D, time) #/\ 
               ref(S, time) #< Time
            ), [Count=count]
         ),
         Count #= Lambda
      )
)).


example(0, ex(0)).
example(1, ex(1)).
example(2, ex(2)).
example(3, ex(3)).
example(4, ex(4)).
example(5, ex(5)).
example(6, ex(6)).
example(7, ex(7)).
example(8, ex(8)).
example(9, ex(9)).
example(10, ex(10)).
example(11, ex(11)).
example(12, ex(12)).
example(13, ex(13)).
example(14, ex(14)).
example(15, ex(15)).

example(50, ex(50, out(X)-inp(X, 5), 51)).

example(60, ex(60, inp(3))).
example(61, ex(60, inp(3)-out(X, T)-inp(X, T), 61)).

example(32, ex(31, out-inp, 32)).

example(100, ex(100, inp(3)-out(D, Time)-inp(D, Time, 3), 101)).
