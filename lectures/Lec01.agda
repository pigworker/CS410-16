module Lec01 where

-- programs, evidence, counting

-- conjunction

record _*_ (S T : Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T
open _*_ public

swap : forall {S T} -> S * T -> T * S
swap (s , t) = t , s


data Three : Set where c1/3 c2/3 c3/3 : Three
data Five : Set where c1/5 c2/5 c3/5 c4/5 c5/5 : Five

{-
howMany : Three * Five
howMany = {!-s 10 -l!}
-}

-- disjunction

data _+_ (S T : Set) : Set where
  inl : S -> S + T
  inr : T -> S + T

comm : forall {S T} -> S + T -> T + S
comm (inl x) = inr x
comm (inr x) = inl x

{-
howMany : Three + Five
howMany = {!-l!}
-}
{-
brexit : forall {X : Set} -> X
brexit = brexit
-}

-- implication

-- falsity

data Zero : Set where

-- negation

Not : Set -> Set
Not X = X -> Zero

magic : forall {X : Set} -> Zero ->  X
magic ()


-- triviality

record One : Set where
  constructor <>

foo : One
foo = <>


-- natural numbers

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

five : Nat
five = 5

-- <=

_<=_ : Nat -> Nat -> Set
zero <= y = One
suc x <= zero = Zero
suc x <= suc y = x <= y

ex1 : 4 <= 17
ex1 = <>

ex2 : Not (17 <= 4)
ex2 ()

-- reflexivity

refl<= : (n : Nat) -> n <= n
refl<= zero = <>
refl<= (suc n) = refl<= n

-- totality

total<= : (m n : Nat) -> (m <= n) + (n <= m)
total<= zero n = inl <>
total<= (suc x) zero = inr <>
total<= (suc x) (suc x₁) = total<= x x₁

-- transitivity

-- ==

-- antisymmetry

























