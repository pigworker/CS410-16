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

record One : Set where
  constructor <>

data H' : Set where
  addL : One -> H -> H'
  addR : H -> One -> H'
  ifteC : One -> H -> H -> H'  
  ifteT : H -> One -> H -> H'  
  ifteE : H -> H -> One -> H'  

_>>>_ : H -> H' -> H
h >>> addL <> h2 = add h h2
h >>> addR h1 <> = add h1 h
h >>> ifteC <> h2 h3 = ifte h h2 h3
h >>> ifteT h1 <> h3 = ifte h1 h h3
h >>> ifteE h1 h2 <> = ifte h1 h2 h

data List (X : Set) : Set where
  []   : List X
  _::_ : X -> List X -> List X

_>>>>_ : H -> List H' -> H
h >>>> [] = h
h >>>> (h' :: h's) = (h >>>> h's) >>> h'

data Check (t : Ty) : H -> Set where
  typed : (h : TH t) -> Check t (untype h)
  error : (h : H)(h's : List H') -> Check t (h >>>> h's)

check : (t : Ty)(h : H) -> Check t h
check nat (val x) = typed (val x)
check bool (val x) = error (val x) []
check nat (boo x) = error (boo x) []
check bool (boo x) = typed (boo x)
check nat (add d' e')                with check nat d' | check nat e'
check nat (add .(untype d) .(untype e)) | typed d | typed e = typed (add d e)
check nat (add .(untype h) .(g >>>> g's))
   | typed h | error g g's = error g (addR (untype h) <> :: g's)
check nat (add .(g >>>> g's) .(untype h))          | error g g's | typed h = error g (addL <> (untype h) :: g's)
check nat (add .(g >>>> g's) .(h >>>> h's))                   | error g g's | error h h's = error g (addL <> (h >>>> h's) :: g's)
check bool (add d' e') = error (add d' e') []
check t (ifte b' d' e') with check bool b' | check t d' | check t e'
check t (ifte .(untype b) .(untype d) .(untype e)) | typed b | typed d | typed e
  = typed (ifte b d e)
check t (ifte .(untype b) .(untype d) .(g >>>> g's)) | typed b | typed d | error g g's
  = error g (ifteE (untype b) (untype d) <> :: g's)
check t (ifte .(untype h) .(g >>>> g's) e') | typed h | error g g's | z
  = error g (ifteT (untype h) <> e' :: g's)
check t (ifte .(g >>>> g's) d' e') | error g g's | y | z
  = error g (ifteC <> d' e' :: g's)

myTerm : H
myTerm = ifte (ifte (boo tt) (boo ff) (boo tt))
           (add (val 3) (boo ff)) (val 7)


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
