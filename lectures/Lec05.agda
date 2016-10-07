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
eval (boo x) = x
eval (add d e) = eval d +N eval e
eval (ifte b t e) with eval b
eval (ifte b t e) | tt = eval t
eval (ifte b t e) | ff = eval e

untype : forall {t} -> TH t -> H
untype (val x) = val x
untype (boo x) = boo x
untype (add d e) = add (untype d) (untype e)
untype (ifte b t e) = ifte (untype b) (untype t) (untype e)

data Check (t : Ty) : H -> Set where
  typed : (h : TH t) -> Check t (untype h)
  error : (h : H) -> Check t h

check : (t : Ty)(h : H) -> Check t h
check nat (val x) = typed (val x)
check bool (val x) = error (val x)
check nat (boo x) = error (boo x)
check bool (boo x) = typed (boo x)
check nat (add d' e')                with check nat d' | check nat e'
check nat (add .(untype d) .(untype e)) | typed d | typed e = typed (add d e)
check nat (add .(untype h) e')          | typed h | error .e' = error (add (untype h) e')
check nat (add d' .(untype h))          | error .d' | typed h = error (add d' (untype h))
check nat (add d' e')                   | error .d' | error .e' = error (add d' e')
check bool (add d' e') = error (add d' e')
check t (ifte b' d' e') with check bool b' | check t d' | check t e'
check t (ifte .(untype b) .(untype d) .(untype e)) | typed b | typed d | typed e
  = typed (ifte b d e)
check t (ifte .(untype b) .(untype d) e') | typed b | typed d | error .e'
  = error (ifte (untype b) (untype d) e')
check t (ifte .(untype h) d' e') | typed h | error .d' | z
  = error (ifte (untype h) d' e')
check t (ifte b' d' e') | error .b' | y | z
  = error (ifte b' d' e')

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
