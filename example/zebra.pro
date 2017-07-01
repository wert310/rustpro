member(X, cons(X, _)).
member(X, cons(_, Zs)) :- member(X,Zs).

rightOf(X, Y, cons(X, cons(Y,_))).
rightOf(X, Y, cons(_,Zs)) :- rightOf(X,Y,Zs).

nextTo(X,Y,Z) :- rightOf(X,Y,Z).
nextTo(X,Y,Z) :- rightOf(Y,X,Z).

unify(X, X).

zebra(W, Z) :- 
  unify(Hs, cons(house(norwegian,_,_,_,_), cons(_, cons(house(_,_,_,milk,_), cons(_, cons(_, nil)))))),
  member(house(englishman,_,_,_,red), Hs),
  member(house(spaniard,dog,_,_,_), Hs),
  member(house(_,_,_,coffee,green), Hs),
  member(house(ukranian,_,_,tea,_), Hs),
  rightOf(house(_,_,_,_,green), house(_,_,_,_,ivory), Hs),
  member(house(_,snails,oldgold,_,_), Hs),
  member(house(_,_,kools,_,yellow), Hs),
  nextTo(house(_,_,chesterfields,_,_), house(_,fox,_,_,_), Hs),
  nextTo(house(_,_,kools,_,_), house(_,horse,_,_,_), Hs),
  member(house(_,_,lukystrike,juice,_), Hs),
  member(house(japanese,_,parliament,_,_), Hs),
  nextTo(house(norwegian,_,_,_,_),house(_,_,_,_,blue), Hs),
  member(house(Z,zebra,_,_,_), Hs),
  member(house(W,_,_,water,_), Hs).
