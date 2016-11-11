module Ex3 where

open import CS410-Prelude
open import CS410-Nat
open import CS410-Indexed


----------------------------------------------------------------------------
-- FUN WITH INDEXED SETS, FUNCTORS AND MONADS
----------------------------------------------------------------------------


-- EPISODE 1
-- FIRST-ORDER TYPED SYNTAX

-- Remember "Typed Hutton's Razor"? Let's add typed variables!

data Ty : Set where nat bool : Ty

data TH (X : Ty -> Set)  -- X t is the set of free variables of type t
        : Ty -> Set where
  var : forall {t} -> X t -> TH X t  -- variables are terms of their own type
  -- and the rest is as before
  val : Nat -> TH X nat
  boo : Two -> TH X bool
  add : TH X nat -> TH X nat -> TH X nat
  ifte : forall {t} -> TH X bool -> TH X t -> TH X t -> TH X t  

-- ???
-- 3.1 Implement the MonadIx which equips this typed syntax with
-- type-safe simultaneous substitution (replacing all the variables at once)

THMonadIx : MonadIx TH
THMonadIx = record { retIx = var ; extendIx = {!!} }

-- ???
-- 3.2 Prove that the MonadIxLaws hold for your implementation.

THMonadIxLaws : MonadIxLaws THMonadIx
THMonadIxLaws = record { lunit = {!!} ; runit = {!!} ; assoc = {!!} }

-- ???
-- 3.3 Implement an interpreter for typed Hutton's razor which uses an
-- *environment* to give values to the variables.

Val : Ty -> Set
Val nat  = Nat
Val bool = Two

eval : forall {X} -> [ X -:> Val ] -> [ TH X -:> Val ]
eval g t = {!!}

-- ???
-- 3.4 Prove that evaluation respects substitution.

module EVALSUB where
  open MonadIx THMonadIx
  open MonadIxLaws THMonadIxLaws
  evalSub : forall {X Y}(sb : [ X -:> TH Y ])(g : [ Y -:> Val ]){ty}(t : TH X ty) ->
            eval g (extendIx sb t) == eval (\ x -> eval g (sb x)) t
  evalSub sb g t = {!!}


-- EPISODE 2
-- Interaction structures and session protocols

-- ???
-- 3.5 Show that for any interaction structure C : I => I,
-- FreeIx C obeys the MonadIxLaws
-- HINT: you will need to make use of "ext".

module FREEIXLAWS {I : Set}(C : I => I) where
  open MonadIx (freeMonadIx C)
  freeMonadIxLaws : MonadIxLaws (freeMonadIx C)
  freeMonadIxLaws = record { lunit = {!!} ; runit = {!!} ; assoc = {!!} }

-- PROTOCOLS

So : Two -> Set
So tt = One
So ff = Zero

data Protocol : Set where
  stop : Protocol  -- communication ends
  send recv :     (chk : Char -> Two)  -- a test of character
              ->  ((c : Char) -> So (chk c) -> Protocol)
                     -- how to continue after sending/receiving an acceptable character
              -> Protocol

-- ???
-- 3.6 Construct an interaction structure which describes how to perform one step
-- of a protocol.

Comms : Protocol => Protocol
Comms = {!!} <! {!!} / {!!}

-- ???
-- 3.7 Given a protocol, show how to construct the "dual" protocol, in which the
-- roles of send and recv have been swapped.

dual : Protocol -> Protocol
dual p = {!!}

-- Signal *traffic* is a list of pairs of bits and characters,
-- recording which data were exchanged

Traffic = List ( Two   -- tt for "sent", ff for "received"
               * Char  -- what was sent or received
               )

-- ???
-- 3.8 Define a type which accurately represents the evidence that some
-- traffic is valid for a given protocol.

Valid : Protocol -> Traffic -> Set
Valid p bcs = {!!}

-- ???
-- 3.9 Show that if traffic is valid for a protocol, flipping the bits in the
-- traffic gives valid traffic for the dual protocol.

mapList : forall {S T} -> (S -> T) -> List S -> List T
mapList f []         = []
mapList f (x :: xs)  = f x :: mapList f xs

not : Two -> Two
not tt = ff
not ff = tt

dualValid : (p : Protocol)(bcs : Traffic) ->
            Valid p bcs -> Valid (dual p) (mapList (\ { (b , c) -> not b , c }) bcs)
dualValid p bcs v = {!!}

-- ???
-- 3.10 Show that any two strategies for interacting according to a protocol and its
-- dual, respectively, can be successfully coroutined to generate valid traffic for the
-- protocol.

communicate : (p : Protocol)
              (me  : FreeIx Comms (_==_ stop) p)
              (you : FreeIx Comms (_==_ stop) (dual p)) ->
              Sg Traffic \ bcs -> Valid p bcs
communicate p me you = {!!}

