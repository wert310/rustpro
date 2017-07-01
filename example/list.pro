member(X, cons(X, _)).
member(X, cons(_, Y)) :- member(X, Y).
