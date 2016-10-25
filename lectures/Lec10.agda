module Lec10 where

open import Agda.Primitive
open import CS410-Prelude
open import CS410-Nat
open import CS410-Functor

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

{-
data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x
infix 1 _==_
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}
-}

lunit? : forall {X Y}(f : X -?> Y)(x : X) -> (id? -?- f) x == f x
lunit? f x = refl

runit? : forall {X Y}(f : X -?> Y)(x : X) -> (f -?- id?) x == f x
runit? f x with f x
runit? f x | yes y = refl
runit? f x | no = refl

assoc? : forall {Q R S T : Set} ->
         (f : Q -?> R)(g : R -?> S)(h : S -?> T)
         (q : Q) -> ((f -?- g) -?- h) q == (f -?- (g -?- h)) q
assoc? f g h q with f q
assoc? f g h q | yes r = refl
assoc? f g h q | no = refl
        
_?>>=_ : {S T : Set} -> Maybe S -> (S -> Maybe T) -> Maybe T
ms ?>>= k = ((\ x -> x) -?- k) ms

_-?'-_ : {R S T : Set} -> (R -?> S) -> (S -?> T) -> (R -?> T)
(f -?'- g) r =
  f r ?>>= \ s ->
  g s

monadMaybe : Monad Maybe
monadMaybe = record
  { return = yes
  ; _>>=_ = _?>>=_
  ; law1 = \ x f -> lunit? f x
  ; law2 = \ t -> runit? (\ _ -> t) <>
  ; law3 = \ f g t -> assoc? (\ _ -> t) f g <>
  }

{-
data List (X : Set) : Set where  -- X scopes over the whole declaration...
  []    : List X                 -- ...so you can use it here...
  _::_  : X -> List X -> List X  -- ...and here.
infixr 3 _::_

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
-}

may-take : {X : Set} -> Nat -> List X -> Maybe (List X)
may-take zero xs = yes []
may-take (suc n) [] = no
may-take (suc n) (x :: xs) =
  may-take n xs ?>>= \ ys ->
  yes (x :: ys)

data Chat (V : Set) : Set where
  retn : V -> Chat V
  input : (Nat -> Chat V) -> Chat V
  output : Nat -> Chat V -> Chat V

_-C>_ : Set -> Set -> Set
S -C> T = S -> Chat T

idC : {X : Set} -> X -C> X
idC x = retn x

_C>>=_ : {S T : Set} -> Chat S -> (S -> Chat T) -> Chat T
retn s C>>= k = k s
input f C>>= k = input (\ n -> f n C>>= k)
output n cs C>>= k = output n (cs C>>= k)

_-C-_ : {R S T : Set} -> (R -C> S) -> (S -C> T) -> (R -C> T)
(f -C- g) r = f r C>>= g

inputC : Chat Nat
inputC = input retn

outputC : Nat -> Chat One
outputC n = output n (retn <>)

add3 : Chat One
add3 =
  inputC C>>= \ x ->
  inputC C>>= \ y ->
  inputC C>>= \ z ->
  outputC (x +N (y +N z))

{-
postulate
  -- morally, functions should be equal when putting
  -- the same thing in always gets you the same thing
  -- out, but that doesn't follow automatically from
  -- our presentation of ==
  ext : forall {k l}{S : Set k}{T : S -> Set l}
        (f g : (x : S) -> T x) ->
        ((x : S) -> f x == g x) ->
        f == g
-}


monadChat : Monad Chat
monadChat =
  record { return = retn ; _>>=_ = _C>>=_
         ; law1 = \ x t -> refl
         ; law2 = help2
         ; law3 = {!!} }
  where
    help2 : {X : Set} (t : Chat X) -> (t C>>= retn) == t
    help2 (retn x) = refl
    help2 (input f) rewrite ext (\ x -> help2 (f x)) = refl
    help2 (output x t) rewrite help2 t = refl

lunitC : forall {X Y}(f : X -C> Y)(x : X) -> (idC -C- f) x == f x
lunitC f x = refl

runitC : forall {X Y}(f : X -C> Y)(x : X) -> (f -C- idC) x == f x
runitC f x = {!!}

assocC : forall {Q R S T : Set} ->
         (f : Q -C> R)(g : R -C> S)(h : S -C> T)
         (q : Q) -> ((f -C- g) -C- h) q == (f -C- (g -C- h)) q
assocC f g h q = {!!}

monadId : Monad id
monadId = {!!}

monadThud : Monad \ _ -> One
monadThud = {!!}

monadList : Monad List
monadList = {!!}

-- transformations

_-:>_ : forall {k l}{X : Set k}(G H : X -> Set l) ->
        X -> Set l
(G -:> H) x = G x -> H x

[_] : forall {k l}{X : Set k}(P : X -> Set l) ->
      Set (k ⊔ l)
[ P ] = forall {x} -> P x

module NATURAL {G H}(FG : Functor G)(FH : Functor H)
                 (f : [ G -:> H ]) where
  open Functor
  record Natural  : Set1 where
    field
      natural : forall {X Y}(e : X -> Y) ->
                  (f o map FG e) == (map FH e o f)

  
