module Lec19 where


open import CS410-Prelude
open import CS410-Nat
open import CS410-Indexed

data Desc (I : Set) : Set1 where
  sub : I -> Desc I
  One' : Desc I
  _*'_ : Desc I -> Desc I -> Desc I
  sg' pi' : (A : Set) -> (A -> Desc I) -> Desc I

infixr 5 _*'_

Node : forall {I} -> Desc I -> (I -> Set) -> Set
Node (sub i) X = X i
Node One' X = One
Node (S *' T) X = Node S X * Node T X
Node (sg' A B) X = Sg A (\ a -> Node (B a) X)
Node (pi' A B) X = (a : A) -> Node (B a) X
  
Vec' : Nat -> Desc (One + Nat)
Vec' zero    = One'
Vec' (suc n) = sub (inl <>) *' sub (inr n)

case : {I J : Set} -> (I -> Set) -> (J -> Set) -> (I + J -> Set)
case X Y (inl i) = X i
case X Y (inr j) = Y j

data Data {I J : Set}(F : J -> Desc (I + J))(X : I -> Set)(j : J) : Set where
  <_> : Node (F j) (case X (Data F X)) -> Data F X j

VEC : Set -> Nat -> Set
VEC X n = Data Vec' (\ _ -> X) n

nil : forall {X} -> VEC X zero
nil = < <> >

cons : forall {X n} -> X ->  VEC X n ->  VEC X (suc n)
cons x xs = < x , xs >

data Col : Set where red blk : Col

RBT : (Col * Nat) -> Desc (One + (Col * Nat))
RBT (red , h) = sub (inr (blk , h)) *' sub (inl <>) *' sub (inr (blk , h))
RBT (blk , zero) = One'
RBT (blk , suc h) = sg' Col \ lc -> sub (inr (lc , h))
                    *' sub (inl <>)
                    *' sg' Col \ lc -> sub (inr (lc , h))

Command : forall {I} -> Desc I -> Set
Command D = Node D (\ _ -> One)

Response : forall {I}(D : Desc I) -> Command D -> Set
Response (sub x) <> = One
Response One' <> = Zero
Response (D *' E) (d , e) = Response D d + Response E e
Response (sg' A B) (a , b) = Response (B a) b
Response (pi' A B) f = Sg A \ a -> Response (B a) (f a)

next : forall {I}(D : Desc I)(c : Command D) -> Response D c -> I
next (sub i) <> <> = i
next One' <> ()
next (D *' E) (d , e) (inl r) = next D d r
next (D *' E) (d , e) (inr r) = next E e r
next (sg' A B) (a , b) r = next (B a) b r
next (pi' A B) f (a , r) = next (B a) (f a) r

NODE :  forall {I J : Set} -> (J -> Desc I) -> (I -> Set) -> (J -> Set)
NODE F = IC ((\ j -> Command (F j)) <! (\ j -> Response (F j)) / ((\ j -> next (F j))))
