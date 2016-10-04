module Lec05 where

-- go back to Lec03 and make the compiler a functor!
-- visit Ex1 and go category-spotting

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

_+N_ : Nat -> Nat -> Nat
x +N zero = x
x +N suc y = suc x +N y

data _+_ (S T : Set) : Set where
  inl : S -> S + T
  inr : T -> S + T

data Two : Set where tt ff : Two
{-# BUILTIN BOOL Two #-}
{-# BUILTIN TRUE tt #-}
{-# BUILTIN FALSE ff #-}

data H : Set where
  val : Nat -> H
  boo : Two -> H
  add : H -> H -> H
  ifte : H -> H -> H -> H  

{-
-- chuck in some Boolean things

-- what happens to the evaluator?

Val : Set
Val = Nat + Two
-}
{-
eval : H -> Nat
eval (val x) = x
eval (add h k) = eval h +N eval k
-}
{-
eval : H -> Val
eval (val x) = inl x
eval (boo x) = inr x
eval (add d e) with eval d | eval e
eval (add d e) | inl x | inl y = inl (x +N y)
eval (add d e) | inl x | inr y = {!!}  -- eek!
eval (add d e) | inr x | z = {!!} -- = inl ({!eval d!} +N {!!})
eval (ifte b t e) = {!!}
-}

-- typed expressions, please
data Ty : Set where nat bool : Ty

data TH : Ty -> Set where
  val : Nat -> TH nat
  boo : Two -> TH bool
  add : TH nat -> TH nat -> TH nat
  ifte : forall {t} -> TH bool -> TH t -> TH t -> TH t  

Val : Ty -> Set
Val nat  = Nat
Val bool = Two

eval : forall {t} -> TH t -> Val t
eval (val x) = x
eval (boo x) = {!x!}
eval (add d e) = eval d +N eval e
eval (ifte b t e) with eval b
eval (ifte b t e) | tt = eval t
eval (ifte b t e) | ff = eval e

-- what happens to stack height ?
data Code : Nat -> Nat -> Set where
  PUSH : forall {n} -> Nat -> Code n (suc n)
  ADD : forall {n} -> Code (suc (suc n)) (suc n)
  _/_ : forall {l m n} -> Code l m -> Code m n -> Code l n
  SKIP : forall {n} -> Code n n

data Bwd (X : Set) : Set where
  [] : Bwd X
  _<:_ : Bwd X -> X -> Bwd X
infixl 4 _<:_

-- how to run code?

-- how to check a type?
-- what's a "type error"?
