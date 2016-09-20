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


howMany : Three + Five
howMany = {!-l!}

{-
brexit : forall {X : Set} -> X
brexit = brexit
-}

-- implication

-- falsity

-- negation

-- triviality

-- natural numbers

-- <=

-- reflexivity

-- totality

-- transitivity

-- ==

-- antisymmetry

























