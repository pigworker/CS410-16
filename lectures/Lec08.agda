module Lec08 where

open import CS410-Prelude
open import CS410-Monoid

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

_+N_ : Nat -> Nat -> Nat
zero  +N n = n
suc m +N n = suc (m +N n)
infixr 3 _+N_

foo : 3 == 3
foo = refl

goo : 3 == 5 -> Zero
goo ()


data Vec (X : Set) : Nat -> Set where
  []   : Vec X 0
  _::_ : forall {n} ->
         X -> Vec X n -> Vec X (suc n)
infixr 3 _::_

hoo : {X : Set}(m n : Nat) -> m == n -> Vec X m -> Vec X n
hoo m .m refl xs = xs

{-
_+N_ : Nat -> Nat -> Nat
zero  +N n = n
suc m +N n = suc (m +N n)
infixr 3 _+N_
-}

+Mon : Monoid Nat
+Mon = record
  { e = 0
  ; op = _+N_
  ; lunit = \ m -> refl
  ; runit = plus0
  ; assoc = plusA
  } where
  plus0 : (m : Nat) -> m +N 0 == m
  plus0 zero    = refl
  plus0 (suc m) rewrite plus0 m = refl
  plusA : (m m' m'' : Nat) -> m +N m' +N m'' == (m +N m') +N m''
  plusA zero y z = refl
  plusA (suc x) y z rewrite plusA x y z = refl

help : (x y : Nat) -> y +N suc x == suc y +N x
help x y = {!!}

+comm : (x y : Nat) -> x +N y == y +N x
+comm zero y rewrite Monoid.runit +Mon y = refl
+comm (suc x) y = {!!}
