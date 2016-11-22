module Lec17 where

open import CS410-Prelude
open import CS410-Nat

data PolyP : Set where  -- Jansson and Jeuring
  _+'_ _*'_ : PolyP -> PolyP -> PolyP
  Zero' One' : PolyP
  elt : Two -> PolyP  -- tt for an element; ff for a substructure

List' : PolyP
List' = One' +' (elt tt *' elt ff)

Node : PolyP -> Set -> Set -> Set
Node (s +' t) X R = Node s X R + Node t X R
Node (s *' t) X R = Node s X R * Node t X R
Node Zero' X R = Zero
Node One' X R = One
Node (elt tt) X R = X
Node (elt ff) X R = R

data DataPolyP (t : PolyP)(X : Set) : Set where
  <_> : Node t X (DataPolyP t X) -> DataPolyP t X

LIST : Set -> Set
LIST = DataPolyP List'

-- nil : forall {X} -> LIST X
pattern nil = < inl <> >

-- cons : forall {X} -> X -> LIST X -> LIST X
pattern cons x xs = < (inr (x , xs)) >

append : forall {X} -> LIST X -> LIST X -> LIST X
append nil ys = ys
append (cons x xs) ys = cons x (append xs ys)

mapPolyP : forall (t : PolyP){X Y} -> (X -> Y) -> DataPolyP t X -> DataPolyP t Y
mapsPolyP : forall (r t : PolyP){X Y} -> (X -> Y) -> Node t X (DataPolyP r X)
                                                -> Node t Y (DataPolyP r Y)
mapPolyP t f < nx > = < mapsPolyP t t f nx >
mapsPolyP r (s +' t) f (inl sx) = inl (mapsPolyP r s f sx)
mapsPolyP r (s +' t) f (inr tx) = inr (mapsPolyP r t f tx)
mapsPolyP r (s *' t) f (sx , tx) = mapsPolyP r s f sx , mapsPolyP r t f tx
mapsPolyP r Zero' f nx = nx
mapsPolyP r One' f <> = <>
mapsPolyP r (elt tt) f x = f x
mapsPolyP r (elt ff) f rx = mapPolyP r f rx

mapLIST = mapPolyP List'

Tree' : PolyP
Tree' = elt tt +' (elt ff *' elt ff)

Tree3' : PolyP
Tree3' = elt tt +' (elt ff *' (elt ff *' elt ff))

TREE = DataPolyP Tree'

mapTREE = mapPolyP Tree'

layerFor : Two -> PolyP -> PolyP
layerFor b (s +' t) = layerFor b s +' layerFor b t
layerFor b (s *' t) = (layerFor b s *' t) +' (s *' layerFor b t)
layerFor b Zero' = Zero'
layerFor b One' = Zero'
layerFor tt (elt tt) = One'
layerFor tt (elt ff) = Zero'
layerFor ff (elt tt) = Zero'
layerFor ff (elt ff) = One'

Subtree : PolyP -> Set -> Set
Subtree t X = List (Node (layerFor ff t) X (DataPolyP t X))

leaf : forall {X} -> X -> TREE X
leaf x = < inl x >

node : forall {X} -> TREE X -> TREE X -> TREE X
node l r = < inr (l , r) >

myCtxt : Subtree Tree' Nat
myCtxt =  inr (inl (<> , leaf 4))
       :: inr (inl (<> , leaf 5))
       :: inr (inr ((node (leaf 1) (leaf 2) , <>)))
       :: []

myEltCtxt : Node (layerFor tt Tree') Nat (DataPolyP Tree' Nat)
myEltCtxt = inl <>

Which : Two -> Set -> Set -> Set
Which tt X R = X
Which ff X R = R

plug : forall {X R}(b : Two)(t : PolyP) -> Which b X R -> Node (layerFor b t) X R
         -> Node t X R
plug b (s +' t) w (inl s') = inl (plug b s w s')
plug b (s +' t) w (inr t') = inr (plug b t w t')
plug b (s *' t) w (inl (s' , t1)) = plug b s w s' , t1
plug b (s *' t) w (inr (s1 , t')) = s1 , plug b t w t'
plug b Zero' w ()
plug b One' w ()
plug tt (elt tt) w d = w
plug tt (elt ff) w ()
plug ff (elt tt) w ()
plug ff (elt ff) w d = w

plugs : forall (t : PolyP){X : Set} -> DataPolyP t X -> Subtree t X -> DataPolyP t X
plugs t s [] = s
plugs t s (d :: ds) = plugs t < plug ff t s d > ds

