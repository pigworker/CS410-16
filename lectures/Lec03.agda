module Lec03 where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

data H : Set where
  val : Nat -> H
  add : H -> H -> H

ex1 : H
ex1 = add (add (val 2) (val 3)) (val 5)

_+N_ : Nat -> Nat -> Nat
x +N zero = x
x +N suc y = suc x +N y

eval : H -> Nat
eval (val x) = x
eval (add h k) = eval h +N eval k

data Code : Nat -> Nat -> Set where
  PUSH : forall {n} -> Nat -> Code n (suc n)
  ADD : forall {n} -> Code (suc (suc n)) (suc n)
  _/_ : forall {l m n} -> Code l m -> Code m n -> Code l n

data Stk : Nat -> Set where
  S0 : Stk zero
  _<:_ : forall {n} -> Stk n -> Nat -> Stk (suc n)

top : forall {n} -> Stk (suc n) -> Nat
top (s <: x) = x

run : forall {m n} -> Stk m -> Code m n -> Stk n
run s (PUSH x) = s <: x
run ((s <: x) <: y) ADD = s <: (x +N y)
run s (c / d) = run (run s c) d

comp : H -> forall {n} -> Code n (suc n)
comp (val x) = PUSH x
comp (add h k) = (comp h / comp k) / ADD

