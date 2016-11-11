module Lec15 where

open import CS410-Prelude
open import CS410-Nat
open import CS410-Vec
open import CS410-Indexed


Rect : Set
Rect = Nat * Nat   -- width , height

Matrix : Set -> (Rect -> Set)
Matrix X (w , h) = Vec (Vec X w) h


record Partition (P : Set) : Set1 where
  field
    Cuts    : P -> Set
    pieces  : {p : P} -> Cuts p -> List P

data AxisCuts (p : Rect) : Set where
  lrCut : (wl wr : Nat) -> (wl +N wr) == fst p -> AxisCuts p
  tbCut : (ht hb : Nat) -> (ht +N hb) == snd p -> AxisCuts p

axisPieces : forall {p} -> AxisCuts p -> List Rect
axisPieces {w , h} (lrCut wl wr wq) = (wl , h) :: (wr , h) :: []
axisPieces {w , h} (tbCut ht hb hq) = (w , ht) :: (w , hb) :: []

Axis : Partition Rect
Axis = record { Cuts = AxisCuts ; pieces = axisPieces }

All : {X : Set} -> (X -> Set) -> List X -> Set
All P []        = One
All P (x :: xs) = P x * All P xs

module SPACEMONAD {P}(Part : Partition P) where

  open Partition Part

  data Interior (X : P -> Set)(p : P) : Set where

    <_>  :    X p ->
            ---------------------
              Interior X p

    _8><_ :   (c : Cuts p) ->
              All (Interior X) (pieces c) ->
            --------------------------------
              Interior X p

  infixr 4 _8><_


  inlay : forall {X Y} ->
            [ X -:> Interior Y ] ->
            [ Interior X -:> Interior Y ]
  inlays : forall {X Y} -> [ X -:> Interior Y ] ->
            [ All (Interior X) -:> All (Interior Y) ]
  inlay x2yI < x > = x2yI x
  inlay x2yI (c 8>< xIs) = c 8>< inlays x2yI xIs
  inlays x2yI {[]} <> = <>
  inlays x2yI {p :: ps} (xI , xIs) = inlay x2yI xI , inlays x2yI xIs

  spaceMonadIx : MonadIx Interior
  spaceMonadIx = record { retIx = <_> ; extendIx = inlay } where

  open MonadIx spaceMonadIx



module AXISSTUFF where
  open module AXIS = SPACEMONAD Axis

  data Square : Rect -> Set where
    square : forall {n} -> Square (n , n)

-- 8------+2+3-+
-- |      |+2| |
-- |      |11+-3
-- |      |5---+
-- |      ||   |
-- |      ||   |
-- |      ||   |
-- +------8+---5

{-
  goo : Interior Square (13 , 8)
  goo = lrCut 8 5 refl 8>< < square > , (tbCut 3 5 refl 8>< {!!} , < square > , <>) , <>
-}

  foo : Interior Square (13 , 8)
  foo =
    lrCut 8 5 refl
    8>< < square >
    ,   (tbCut 3 5 refl
         8>< (lrCut 2 3 refl
              8>< (tbCut 2 1 refl
                   8>< < square >
                   ,   (lrCut 1 1 refl
                        8>< < square >
                        ,   < square >
                        ,   <>)
                   ,   <>)
              , < square >
              , <>)
         ,   < square >
         ,   <>)
    ,   <>

_+V_ : forall {m n X} -> Vec X m -> Vec X n -> Vec X (m +N n)
_+V_ {zero} xs ys = ys
_+V_ {suc x} (x₁ :: x₂) ys = x₁ :: (x₂ +V ys)

vec : forall {n X} -> X -> Vec X n
vec {zero} x = []
vec {suc x} x₁ = x₁ :: vec x₁

_<*>_ : forall {n S T} -> Vec (S -> T) n -> Vec S n -> Vec T n
[] <*> ss = []
(x :: x₁) <*> (x₂ :: x₃) = x x₂ :: (x₁ <*> x₃)

module PASTING {P}(Part : Partition P)(X : P -> Set) where
  open Partition Part public
  open SPACEMONAD Part public
  module PASTER

      (paste : forall {p}(c : Cuts p) -> All X (pieces c) -> X p)

    where

    pasteI  : [ Interior X -:> X ]
    pasteIs : [ All (Interior X) -:> All X ]

    pasteI < x >        = x
    pasteI (c 8>< xIs)  = paste c (pasteIs xIs)

    pasteIs {[]}      <>          = <>
    pasteIs {p :: ps} (xI , xIs)  = pasteI xI , pasteIs xIs


{-----------------------------------------------}


module MATRIXPASTER (X : Set) where
  open PASTING Axis (Matrix X) public
  open PASTER (\ { {.(wl +N wr) , h} (lrCut wl wr refl) (lm , rm , <>) -> (vec _+V_ <*> lm) <*> rm
                 ; {w , .(ht +N hb)} (tbCut ht hb refl) (tm , bm , <>) -> tm +V bm
                 })





