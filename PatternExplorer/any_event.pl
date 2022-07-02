:- module(any_event,[
    any_event/1
]).

any_event(X)
    :- put_attr(Y, any_event, true),
       X = Y. 

attr_unify_hook(_, Y)
    :- (  var(Y) -> put_attr(Y, any_event, true) ; true ).

attribute_goals(X) 
    --> { get_attr(X, any_event, _) },
        [any_event(X)].



