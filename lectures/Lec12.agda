module Lec12 where

open import Agda.Primitive
open import CS410-Prelude
open import CS410-Nat
open import CS410-Functor
open import CS410-Vec

data Maybe (X : Set) : Set where
  yes  : X -> Maybe X  -- use this to say "here's a sensible answer"
  no   : Maybe X       -- use this to say "something went wrong"

{-
allYes : {X : Set}{n : Nat} -> Vec (Maybe X) n -> Maybe (Vec X n)
allYes [] = yes []
allYes (yes x :: xms) with allYes xms
allYes (yes x :: xms) | yes xs = yes (x :: xs)
allYes (yes x :: xms) | no = no
allYes (no :: xms) = no
-}

_?>>=_ : {S T : Set} -> Maybe S -> (S -> Maybe T) -> Maybe T
yes s ?>>= k = k s
no    ?>>= k = no

{-
allYes : {X : Set}{n : Nat} -> Vec (Maybe X) n -> Maybe (Vec X n)
allYes [] = yes []
allYes (xm :: xms) =
  xm ?>>= \ x ->
  allYes xms ?>>= \ xs ->
  yes (x :: xs)
-}

_<*>_ : {S T : Set} -> Maybe (S -> T) -> Maybe S -> Maybe T
mf <*> ms =
  mf ?>>= \ f ->
  ms ?>>= \ s ->
  yes (f s)

infixl 3 _<*>_

vc : {X : Set}{n : Nat} -> X -> Vec X n -> Vec X (suc n)
vc = _::_

allYes : {X : Set}{n : Nat} -> Vec (Maybe X) n -> Maybe (Vec X n)
allYes [] = yes []
allYes (xm :: xms) = yes _::_ <*> xm <*> allYes xms


allId : {X : Set}{n : Nat} -> Vec X n -> Vec X n
allId [] = []
allId (x :: xs) = _::_ x (allId xs)
