module Lec10 where

data Maybe (X : Set) : Set where
  yes  : X -> Maybe X  -- use this to say "here's a sensible answer"
  no   : Maybe X       -- use this to say "something went wrong"

_-?>_ : Set -> Set -> Set
A -?> B = A -> Maybe B

id? : {X : Set} -> X -?> X
id? x = yes x

_-?-_ : {R S T : Set} -> (R -?> S) -> (S -?> T) -> (R -?> T)
(g -?- f) r with g r
(g -?- f) r | yes s = f s
(g -?- f) r | no    = no

data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x
infix 1 _==_
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

lunit : forall {X Y}(f : X -?> Y)(x : X) -> (id? -?- f) x == f x
lunit f x = refl

runit : forall {X Y}(f : X -?> Y)(x : X) -> (f -?- id?) x == f x
runit f x with f x
runit f x | yes y = refl
runit f x | no = refl

assoc : forall {Q R S T : Set} ->
        (f : Q -?> R)(g : R -?> S)(h : S -?> T)
        (q : Q) -> ((f -?- g) -?- h) q == (f -?- (g -?- h)) q
assoc f g h q with f q
assoc f g h q | yes r = refl
assoc f g h q | no = refl
        
_>>=_ : {S T : Set} -> Maybe S -> (S -> Maybe T) -> Maybe T
ms >>= k = ((\ x -> x) -?- k) ms

_-?'-_ : {R S T : Set} -> (R -?> S) -> (S -?> T) -> (R -?> T)
(f -?'- g) r =
  f r >>= \ s ->
  g s

data List (X : Set) : Set where  -- X scopes over the whole declaration...
  []    : List X                 -- ...so you can use it here...
  _::_  : X -> List X -> List X  -- ...and here.
infixr 3 _::_

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

may-take : {X : Set} -> Nat -> List X -> Maybe (List X)
may-take zero xs = yes []
may-take (suc n) [] = no
may-take (suc n) (x :: xs) =
  may-take n xs >>= \ ys ->
  yes (x :: ys)

data Chat (V : Set) : Set where
  return : V -> Chat V
  input : (Nat -> Chat V) -> Chat V
  output : Nat -> Chat V -> Chat V

_-C>_ : Set -> Set -> Set
S -C> T = S -> Chat T

idC : {X : Set} -> X -C> X
idC x = return x

_C>>=_ : {S T : Set} -> Chat S -> (S -> Chat T) -> Chat T
return s C>>= k = k s
input f C>>= k = input (\ n -> f n C>>= k)
output n cs C>>= k = output n (cs C>>= k)
