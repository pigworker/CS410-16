module Ex2 where

----------------------------------------------------------------------------
-- EXERCISE 2 -- STRUCTURE WITH VECTORS
--
-- VALUE:     25%
-- DEADLINE:  5pm, Friday 28 October (week 6)
--
-- DON'T SUBMIT, COMMIT!
--
-- The purpose of this exercise is to introduce you to some useful
-- mathematical structures and build good tools for working with
-- vectors
--
-- NOTE: Only 15 marks' worth of questions have appeared in this file
-- on 11 Oct 2016. The other 10 will follow, via git. I'll message
-- around when that has happened.
----------------------------------------------------------------------------

open import CS410-Prelude
open import CS410-Monoid
open import CS410-Nat
open import CS410-Vec
open import CS410-Functor

-- HINT: feel free to paste in any useful bits and pieces from Ex1.agda

-- HINT: your tasks are heralded with the eminently searchable tag, "???"


----------------------------------------------------------------------------
-- ??? 2.1 replication to make a constant vector              (score: ? / 1)
----------------------------------------------------------------------------

vec : forall {n X} -> X -> Vec X n
vec x = {!!}

-- HINT: you may need to override default invisibility

-- SUSPICIOUS: no specification? why not?


----------------------------------------------------------------------------
-- ??? 2.2 vectorised application                             (score: ? / 1)
----------------------------------------------------------------------------

-- implement the operator which takes the same number of functions
-- and arguments and computes the applications in corresponding
-- positions

vapp : forall {n X Y} ->
       Vec (X -> Y) n -> Vec X n -> Vec Y n
vapp fs xs = {!!}


----------------------------------------------------------------------------
-- ??? 2.3 one-liners                                         (score: ? / 1)
----------------------------------------------------------------------------

-- implement map and zip for vectors using vec and vapp
-- no pattern matching or recursion permitted

vmap : forall {n X Y} -> (X -> Y) -> Vec X n -> Vec Y n
vmap f xs = {!!}

vzip : forall {n X Y} -> Vec X n -> Vec Y n -> Vec (X * Y) n
vzip xs ys = {!!}


----------------------------------------------------------------------------
-- ??? 2.4 unzipping                                          (score: ? / 2)
----------------------------------------------------------------------------

-- implement unzipping as a view, showing that every vector of pairs
-- is given by zipping two vectors

-- you'll need to complete the view type yourself

data Unzippable {X Y n} : Vec (X * Y) n -> Set where
  unzipped : {- some stuff -> -} Unzippable {!!}
  
unzip : forall {X Y n}(xys : Vec (X * Y) n) -> Unzippable xys
unzip xys = {!!}


----------------------------------------------------------------------------
-- ??? 2.5 vectors are applicative                            (score: ? / 2)
----------------------------------------------------------------------------

-- prove the Applicative laws for vectors

VecApp : forall n -> Applicative \X -> Vec X n
VecApp n = record
  { pure         = vec
  ; _<*>_        = vapp
  ; identity     = {!!}
  ; composition  = {!!}
  ; homomorphism = {!!}
  ; interchange  = {!!}
  } where
  -- lemmas go here


----------------------------------------------------------------------------
-- ??? 2.6 vectors are traversable                            (score: ? / 1)
----------------------------------------------------------------------------

-- show that vectors are traversable; make sure your traverse function
-- acts on the elements of the input once each, left-to-right

VecTrav : forall n -> Traversable \X -> Vec X n
VecTrav = {!!}


----------------------------------------------------------------------------
-- ??? 2.7 monoids make constant applicatives                 (score: ? / 1)
----------------------------------------------------------------------------

-- Show that every monoid gives rise to a degenerate applicative functor

MonCon : forall {X} -> Monoid X -> Applicative \_ -> X
MonCon M = record
             { pure          = {!!}
             ; _<*>_         = op
             ; identity      = {!!}
             ; composition   = {!!}
             ; homomorphism  = {!!}
             ; interchange   = {!!}
             } where open Monoid M


----------------------------------------------------------------------------
-- ??? 2.8 vector combine                                     (score: ? / 1)
----------------------------------------------------------------------------

-- Using your answers to 2.6 and 2.7, rather than any new vector recursion,
-- show how to compute the result of combining all the elements of a vector
-- when they belong to some monoid.

vcombine : forall {X} -> Monoid X ->
           forall {n} -> Vec X n -> X
vcombine M = {!!}


----------------------------------------------------------------------------
-- ??? 2.9 scalar product                                     (score: ? / 1)
----------------------------------------------------------------------------

-- Show how to compute the scalar ("dot") product of two vectors of numbers.
-- (Multiply elements in corresponding positions; compute total of products.)
-- HINT: think zippily, then combine

vdot : forall {n} -> Vec Nat n -> Vec Nat n -> Nat
vdot xs ys = {!!}


----------------------------------------------------------------------------
-- MATRICES
----------------------------------------------------------------------------

-- let's say that an h by w matrix is a column h high of rows w wide

Matrix : Set -> Nat * Nat -> Set
Matrix X (h , w) = Vec (Vec X w) h


----------------------------------------------------------------------------
-- ??? 2.11 identity matrix                                   (score: ? / 1)
----------------------------------------------------------------------------

-- show how to construct the identity matrix of a given size, with
-- 1 on the main diagonal and 0 everywhere else, e.g,
-- (1 :: 0 :: 0 :: []) ::
-- (0 :: 1 :: 0 :: []) ::
-- (0 :: 0 :: 1 :: []) ::
-- []

idMat : forall {n} -> Matrix Nat (n , n)
idMat = {!!}

-- HINT: you may need to do recursion on the side, but then you
-- can make good use of vec and vapp


----------------------------------------------------------------------------
-- ??? 2.10 transposition                                     (score: ? / 1)
----------------------------------------------------------------------------

-- show how to transpose matrices
-- HINT: use traverse, and it's a one-liner

transpose : forall {X m n} -> Matrix X (m , n) -> Matrix X (n , m)
transpose = {!!}


----------------------------------------------------------------------------
-- ??? 2.11 multiplication                                    (score: ? / 2)
----------------------------------------------------------------------------

-- implement matrix multiplication
-- HINT: transpose and vdot can be useful

matMult : forall {m n p} ->
          Matrix Nat (m , n) -> Matrix Nat (n , p) -> Matrix Nat (m , p)
matMult xmn xnp = {!!}


----------------------------------------------------------------------------
-- ??? TO BE CONTINUED...
----------------------------------------------------------------------------



































----------------------------------------------------------------------------
-- INDEXING INTO VECTORS
----------------------------------------------------------------------------

-- This family of "finite sets of a given size" is useful as types for
-- indexing into vectors with no danger of bounds violation.


data Fin : Nat -> Set where
  fz : {n : Nat} -> Fin (suc n)
  fs : {n : Nat} -> Fin n -> Fin (suc n)

-- Failure-free projection.

project : forall {n X} -> Vec X n -> (Fin n -> X)   -- gratuitous extra (..)
-- project [] ()
project (x :: xs) fz     = x
project (x :: xs) (fs i) = project xs i

-- do the gotcha, Conor -- oh, they fixed it

-- here's a wee visualization of the smallest three Fin sets.

-- Fin 0 |    Fin 1 |    Fin 2   |        Fin 3
---------+----------+------------+----------------
--       |    fz{0} |     fz{1}  |         fz{2}
--       |          | fs (fz{0}) |     fs (fz{1})
--       |          |            | fs (fs (fz{0}))


----------------------------------------------------------------------------
-- 2.12 tabulation                                            (score: ? / 2)
----------------------------------------------------------------------------

tabulate : forall {n X} -> (Fin n -> X) -> Vec X n
tabulate {n} f = {!!}

-- make sure that project (tabulate f) i == f i

----------------------------------------------------------------------------
-- THINNINGS (A CATEGORY)
----------------------------------------------------------------------------

-- A thinning is an order-preserving embedding between Fin types. E.g.

--              fz  ---------------->  fz
--           fs fz  -----,___          fs fz
--      fs (fs fz)  ---,__   '------>  fs (fs fz)
--                        '---,__      fs (fs (fs fz))
--                               '-->  fs (fs (fs (fs fz)))

-- We can represent them by this family of types:

data Thinning : Nat -> Nat -> Set where
  noThin :                                Thinning zero    zero
  fzToFz : {m n : Nat} -> Thinning m n -> Thinning (suc m) (suc n)
  skipFz : {m n : Nat} -> Thinning m n -> Thinning m       (suc n)

thin : {m n : Nat} -> Thinning m n -> (Fin m -> Fin n)
thin noThin ()
thin (fzToFz t) fz     = fz
thin (fzToFz t) (fs i) = fs (thin t i)
thin (skipFz t) i      = fs (thin t i)

myThinning : Thinning 3 5
myThinning = fzToFz (skipFz (fzToFz (skipFz (fzToFz noThin))))


----------------------------------------------------------------------------
-- 2.13 category of thinnings                                 (score: ? / 5)
----------------------------------------------------------------------------

-- Construct the identity thinning and composition of thinnings, then
-- show that the categorical laws hold.

idThin : {n : Nat} -> Thinning n n
idThin {n} = {!!}

_-thn-_ : {l m n : Nat} -> Thinning l m -> Thinning m n -> Thinning l n
s -thn- t = {!!}

id-thn : {m n : Nat}(t : Thinning m n) -> (idThin -thn- t) == t
id-thn t = {!!}

thn-id : {m n : Nat}(t : Thinning m n) -> (t -thn- idThin) == t
thn-id t = {!!}

thn-assoc : {k l m n : Nat}
            (r : Thinning k l)(s : Thinning l m)(t : Thinning m n) ->
            ((r -thn- s) -thn- t) == (r -thn- (s -thn- t))
thn-assoc r s t = {!!}

-- By the way, (suc, fzToFz) should be a functor from (Nat, Thinning)
-- to itself.


----------------------------------------------------------------------------
-- 2.14 functoriality of "thin"                               (score: ? / 2)
----------------------------------------------------------------------------

-- Show that (Fin, thin) is a functor from (Nat, Thinning) to (Set, ->).
-- That is, complete the following.

thinId : {n : Nat}(i : Fin n) -> thin idThin i == i
thinId i = {!!}

thinThn : {l m n : Nat}(s : Thinning l m)(t : Thinning m n)(i : Fin l) ->
          thin t (thin s i) == thin (s -thn- t) i
thinThn s t i = {!!}


----------------------------------------------------------------------------
-- 2.15 Vector "selection"                                    (score: ? / 1)
----------------------------------------------------------------------------

-- Give a function using a thinning to select from a vector just those
-- elements in positions which the thinning targets.

selection : forall {m n X} -> Thinning m n -> Vec X n -> Vec X m
selection t xs = {!!}

-- Your function should satisfy the property that
--    proj (selection t xs) i == proj xs (thin t i)
-- but there are no marks available for the proof.
-- Similarly, there are no marks for thinking about
-- whether selection is the arrow action of a functor.

