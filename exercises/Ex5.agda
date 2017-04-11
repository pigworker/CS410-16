module Ex5 where

open import CS410-Prelude
open import CS410-Nat
open import CS410-Vec
open import CS410-Indexed
open import CS410-Monoid
open import Ex4AgdaSetup


---------------------------------------------------------------------------
--                                                                       --
-- EPISODE 1: BOXES                                           [5 marks]  --
--                                                                       --
---------------------------------------------------------------------------

-- Boxes are sized rectangular tilings which fit together precisely.
-- They allow us to talk about the use of 2D space, e.g., on a screen.

data Box (X : Nat * Nat -> Set)(wh : Nat * Nat) : Set where
--        ^basic-tile             width^   ^height

  tile : X wh -> Box X wh
--       a basic tile is a tiling

  leri : (wl : Nat)   (bl : Box X (wl , snd wh))
         (wr : Nat)   (br : Box X (wr , snd wh))
         -> wl +N wr == fst wh -> Box X wh
-- combine "left" and "right" tilings the same height
-- to make a tiling with their total width

  tobo : (ht : Nat)   (bt : Box X (fst wh , ht))
         (hb : Nat)   (bb : Box X (fst wh , hb))
         -> ht +N hb == snd wh -> Box X wh
-- combine "top" and "bottom" tilings the same width
-- to make a tiling with their total height


---------------------------------------------------------------------------
-- MONADIC STRUCTURE                                                     --
---------------------------------------------------------------------------

-- Show that Box has the MonadIx structure:
--   every X-tile can be made into an X-tiling;
--   if you can turn X-tiles into Y-tilings,
--     then you can turn X-tilings into Y-tilings.
-- (2 marks, one for boxExtendIx, one for proving the laws)

boxMonadIx : MonadIx Box
boxMonadIx = record { retIx = tile ; extendIx = boxExtendIx } where
  boxExtendIx : {X Y : Nat * Nat → Set} ->
                [ X -:> Box Y ] -> [ Box X -:> Box Y ]
  boxExtendIx k b = {!!}

boxMonadIxLaws : MonadIxLaws boxMonadIx
boxMonadIxLaws = record
  { lunit = {!!}
  ; runit = {!!}
  ; assoc = {!!}
  } where
  open MonadIx boxMonadIx


---------------------------------------------------------------------------
-- PASTE KITS AND MATRICES                                               --
---------------------------------------------------------------------------

-- A "paste kit" for sized stuff is whatever you need to combine stuff
-- left-to-right and top-to-bottom

record PasteKit (X : Nat * Nat -> Set) : Set where
  field
    leriPaste : (wl wr : Nat){h : Nat} ->
                X (wl , h) -> X (wr , h) -> X ((wl +N wr) , h)
    toboPaste : {w : Nat}(ht hb : Nat) ->
                X (w , ht) -> X (w , hb) -> X (w , (ht +N hb))

-- Show that a PasteKit is just what you need to turn a tiling of
-- stuff into some stuff. (1 mark)

pasteBox : {X : Nat * Nat -> Set} -> PasteKit X -> [ Box X -:> X ]
pasteBox {X} pk = go where
  open PasteKit pk -- brings leriPaste and toboPaste into scope
  go : [ Box X -:> X ]
  go b = {!!}

-- If you were wondering what any of this had to do with part 1, here we
-- go...

Matrix : Set -> Nat * Nat -> Set
Matrix C (w , h) = Vec (Vec C w) h
-- matrices are "sized stuff", represented as a vector the right height
-- of rows which are vectors the right width of some sort of unit "cell".

-- Copying in any useful equipment you built in earlier exercises
-- (yes, it was all done for a reason!), give matrices their PasteKit.

-- For a start, and to make the exercise file typecheck, I've gone on a
-- raid for...

vec : forall {n X} -> X -> Vec X n
vec {zero}  x = []
vec {suc n} x = x :: vec {n} x

-- ...but you will need a bunch more stuff for working with vectors.

matrixPasteKit : {C : Set} -> PasteKit (Matrix C)
matrixPasteKit = record
  { leriPaste = {!!}
  ; toboPaste = {!!}
  }
-- (2 marks)


---------------------------------------------------------------------------
-- INTERLUDE: TESTING WITH TEXT                                          --
---------------------------------------------------------------------------

-- Turn a list into a vector, either by truncating or padding with
-- a given dummy element.
paddy : {X : Set} -> X -> List X -> {n : Nat} -> Vec X n
paddy _ _         {zero}   = []
paddy x []        {suc n}  = x :: paddy x [] {n}
paddy x (y :: ys) {suc n}  = y :: paddy x ys {n}

-- Use that to make vectors of characters from strings, padding with space.
[-_-] : String -> {n : Nat} -> Vec Char n
[- s -] = paddy ' ' (primStringToList s)

-- Here are some.
mat43-1 : Matrix Char (4 , 3)
mat43-1 = [- "post" -] :: [- "cake" -] :: [- "flop" -] :: []

mat43-2 : Matrix Char (4 , 3)
mat43-2 = [- "horn" -] :: [- "walk" -] :: [- "ping" -] :: []

mat22 : Matrix Char (2 , 2)
mat22 = [- "go" -] :: [- "do" -] :: []

mat62 : Matrix Char (6 , 2)
mat62 = [- "getter" -] :: [- "gooder" -] :: []

-- Put them together as a tiling.
myTiling : Box (Matrix Char) (8 , 5)
myTiling = tobo 3 (leri 4 (tile mat43-1) 4 (tile mat43-2) refl)
                2 (leri 2 (tile mat22) 6 (tile mat62) refl) refl

-- Paste all the pieces and see what you get!
myText : Matrix Char (8 , 5)
myText = pasteBox matrixPasteKit myTiling


---------------------------------------------------------------------------
--                                                                       --
-- EPISODE 2: CUT KITS AND MATRICES                           [2 marks]  --
--                                                                       --
---------------------------------------------------------------------------

-- A "cut kit" for sized stuff is whatever you need to cut stuff into
-- smaller pieces: left-and-right pieces, or top-and-bottom pieces.

record CutKit (X : Nat * Nat -> Set) : Set where
  field
    cutLR : (w h wl wr : Nat) -> wl +N wr == w ->
            X (w , h) -> X (wl , h) * X (wr , h)
    cutTB : (w h ht hb : Nat) -> ht +N hb == h ->
            X (w , h) -> X (w , ht) * X (w , hb)

-- Equip matrices with their CutKit. (1 mark)

matrixCutKit : {C : Set} -> CutKit (Matrix C)
matrixCutKit {C} = record 
  {  cutLR = {!!}
  ;  cutTB = {!!}
  }


---------------------------------------------------------------------------
-- HOLES                                                                 --
---------------------------------------------------------------------------

-- We might want to make sure that, whatever other basic tiles are in play,
-- we can have tiles which are "missing", as if we had cut rectangular
-- holes in a piece of paper.

data HoleOr (X : Nat * Nat -> Set)(wh : Nat * Nat) : Set where
  hole  : HoleOr X wh
  stuff : X wh -> HoleOr X wh

-- A HoleOr X is (you guessed it) either a hole or an X.

-- Show that if X has a CutKit, so has HoleOr X. What do you get when you
-- cut up a hole? (1 mark)

holeCutKit : {X : Nat * Nat -> Set} -> CutKit X -> CutKit (HoleOr X)
holeCutKit {X} ck = record { cutLR = clr ; cutTB = ctb } where
  open CutKit ck
  clr : (w h wl wr : Nat) -> wl +N wr == w ->
        HoleOr X (w , h) -> HoleOr X (wl , h) * HoleOr X (wr , h)
  clr w h wl wr wq y = {!!}
  ctb : (w h ht hb : Nat) -> ht +N hb == h ->
        HoleOr X (w , h) -> HoleOr X (w , ht) * HoleOr X (w , hb)
  ctb w h ht hb hq y = {!!}


---------------------------------------------------------------------------
-- A BIT OF FUN                                                          --
---------------------------------------------------------------------------

-- Show that you can turn holes into spaces.

holeSpace : [ HoleOr (Matrix Char) -:> Matrix Char ]
holeSpace = {!!}

-- Show how to render a tiling made of text or holes as text.

renderHoleOrText : [ Box (HoleOr (Matrix Char)) -:> Matrix Char ]
renderHoleOrText = {!!}
  where open FunctorIx (monadFunctorIx boxMonadIx)

-- Make a test example and see!

myTest : Matrix Char (8 , 6)
myTest = renderHoleOrText
  (leri 3 (tobo 4 (tile (stuff (vec (vec '*')))) 2 (tile hole) refl)
        5 (tobo 2 (tile hole) 4 (tile (stuff (vec (vec '=')))) refl) refl)


---------------------------------------------------------------------------
--                                                                       --
-- EPISODE 3: CUTTING UP BOXES AND OVERLAYING WITH HOLES      [8 marks]  --
--                                                                       --
---------------------------------------------------------------------------

-- Previously...
-- ... we established what it is to be a CutKit, and we built CutKits
-- for some sorts of basic tile. Now we need to build the CutKit for
-- Box. Let's think about what that involves for a moment. We're going
-- to need a CutKit for basic tiles to stand a chance. But how do we
-- cut compound tiles?
--
-- Suppose we're writing cutLR, and we have some
--   cq : cwl + cwr == w   -- the "cut widths" equation
-- telling us where we want to make the cut in something of width w.
--
--             v
--    +--------:------+
--    |        :      |
--    |        :      |
--    +--cwl---:-cwr--+
--    :        ^      :
--    :.......w.......:
--
-- The tricky part is when the box we're cutting here is built with
--   leri bwl bl bwr br bq
-- where
--   bq : bwl + bwr == w   -- the "box widths" equation
--
-- There are three possible situations, all of which you must detect
-- and handle.
--
-- (i) you hit the sweet spot...
--
--             v
--    +--bwl---+-bwr--+
--    |        |      |
--    |        |      |
--    +--cwl---+-cwr--+
--    :        ^      :
--    :.......w.......:
--
--     ...where the box is already divided in the place where the cut
--     has to go. Happy days.
--
-- (ii) you're cutting to the left of the join...
--
--             v
--    +--bwl-----+bwr-+
--    |        : |    |
--    |        : |    |
--    +--cwl---:-cwr--+
--    :        ^      :
--    :.......w.......:
--
--     ...so you'll need to cut the left box in the correct place. You
--     will need some evidence about widths to do that. And then you'll
--     the have three pieces you can see in my diagram, so to complete
--     the cut, you will need to put two of those pieces together, which
--     will take more evidence.
--
-- (iii) you're cutting to the right of the join...
--
--             v
--    +--bwl-+--bwr---+
--    |      | :      |
--    |      | :      |
--    +--cwl---:-cwr--+
--    :        ^      :
--    :.......w.......:
--
--     ...so you'll need to cut the right box in the correct place, and
--     reassemble the bits.
--
-- HINT: THE NEXT FOUR MARKS IN THIS EPISODE COME FROM ONE PROBLEM.
-- TREAT THEM AS A WHOLE.


---------------------------------------------------------------------------
-- COMPARING THE CUT POSITION                                            --
---------------------------------------------------------------------------

data CutCompare (x x' y y' n : Nat) : Set where
  cutLt : -- add evidence here
    CutCompare x x' y y' n
  cutEq : -- add evidence here
    CutCompare x x' y y' n
  cutGt : -- add evidence here
    CutCompare x x' y y' n
  -- Give three constructors for this type which characterize the three
  -- possibilities described above whenever
  --   x + x' == n   and   y + y' == n
  -- (E.g., take n to be w, x and x' to be cwl and cwr, y and y' to be
  -- bwl and bwr. But later, you'll need to do use the same tool for
  -- heights.)
  --
  -- You will need to investigate what evidence must be packaged in each
  -- situation. On the one hand, you need to be able to *generate* the
  -- evidence, with cutCompare, below. On the other hand, the evidence
  -- must be *useful* when you come to write boxCutKit, further below.
  -- Don't expect to know what to put here from the get-go. Figure it
  -- out by discovering what you *need*.
  --
  -- (1 mark)

-- Show that whenever you have two ways to express the same n as a sum,
-- you can always deliver the CutCompare evidence. (1 mark)

cutCompare : (x x' y y' n : Nat) -> x +N x' == n -> y +N y' == n ->
             CutCompare x x' y y' n
cutCompare x x' y y' n xq yq = {!!}


---------------------------------------------------------------------------
-- A CUTKIT FOR BOXES                                                    --
---------------------------------------------------------------------------

-- Now, show that you can construct a CutKit for Box X, given a CutKit
-- for X. There will be key points where you get stuck for want of crucial
-- information. The purpose of CutCompare is to *describe* that
-- information. The purpose of cutCompare is to *compute* that information.
-- Note that cutLR and cutTB will work out very similarly, just exchanging
-- the roles of width and height.
-- (2 marks)

boxCutKit : {X : Nat * Nat -> Set} -> CutKit X -> CutKit (Box X)
boxCutKit {X} ck = record { cutLR = clr ; cutTB = ctb } where
  open CutKit ck
  clr : (w h wl wr : Nat) -> wl +N wr == w ->
        Box X (w , h) -> Box X (wl , h) * Box X (wr , h)
  clr w h wl wr wq b = {!!}
  ctb : (w h ht hb : Nat) -> ht +N hb == h ->
        Box X (w , h) -> Box X (w , ht) * Box X (w , hb)
  ctb w h ht hb hq b = {!!}


---------------------------------------------------------------------------
-- CROP                                                                  --
---------------------------------------------------------------------------

-- Show that, given a CutKit, you can implement the "crop" operation which
-- trims a small rectangle out of an enclosing rectangle.
-- (1 mark)

crop : {X : Nat * Nat -> Set} -> CutKit X ->
       (wl wc wr ht hc hb : Nat) ->
       X ((wl +N wc +N wr) , (ht +N hc +N hb)) -> X (wc , hc)
crop ck wl wc wr ht hc hb x = {!!}
  where open CutKit ck

-- For fun, practice, and the chance to test your work, try building
-- a nontrivially tiled...

testBigBox : Box (HoleOr (Matrix Char)) (20 , 15)
testBigBox = {!!}

-- ...so that you can see this stuff in action:

textDisplayCutKit : CutKit (Box (HoleOr (Matrix Char)))
textDisplayCutKit = boxCutKit (holeCutKit matrixCutKit)

testWeeBox : Box (HoleOr (Matrix Char)) (10 , 5)
testWeeBox = crop textDisplayCutKit 5 10 5 5 5 5 testBigBox


---------------------------------------------------------------------------
-- MASK                                                                  --
---------------------------------------------------------------------------

-- We can now implement a general purpose superimposition operator.
-- The idea is that a tiling of X-tiles (which might, e.g., have holes)
-- is in front and a tiling of Y-tiles is behind it.
-- If have a CutKit for Y, and a function that combines X-tiles and
-- Y-tilings to make Z-tilings, you can cut up the back layer into
-- regions which are masked by the tiles in the front layer, then
-- combine them. E.g., if the front layer is made of (HoleOr Y)
-- and the back is made of Y, then you can arrange to fill the holes
-- in the front with the regions from the back that you would be able
-- to see through the holes. (2 marks)

mask : {X Y Z : Nat * Nat -> Set} -> CutKit Y ->
       [ X -:> Box Y -:> Box Z ] ->
                     [
       {- front -}     Box X -:>
       {- back  -}     Box Y -:>
       {- combined -}  Box Z ]
mask {X}{Y}{Z} ck m = go where
  open CutKit (boxCutKit ck)
  go : [ Box X -:> Box Y -:> Box Z ]
  go xb yb = {!!}

-- If you like, check that you can indeed see through holes in the
-- front to the tiling at the back. It's good practice for the
-- next bit, which *is* worth a mark. Note, that *mask* is the key
-- piece of work that you did which gives you these operations
-- cheaply.
seeThrough : {X : Nat * Nat -> Set} -> CutKit X ->
                        [
          {- front -}     Box (HoleOr X) -:>
          {- back  -}     Box X -:>
          {- combined -}  Box X ]
seeThrough ck = mask ck {!!}

-- Now go further, and make Box (HoleOr X) a monoid for all widths and heights,
-- where the monoid operation is superimposition of holey overlays.
-- That is, there is such a thing as a totally
-- transparent layer, and you can overlay *any* number of layers by
-- combining any two neighbouring layers at a time.

-- I don't require you to prove the monoid laws, apart from left unit, which
-- should be very easy if you've done the thing a sensible way. (1 mark)

postulate IGiveUp : {X : Set} -> X

overlayMonoid : {X : Nat * Nat -> Set} -> CutKit X -> {wh : Nat * Nat} ->
  Monoid (Box (HoleOr X) wh)
overlayMonoid {X} ck {wh} =
  record { e     = {!!}
         ; op    = overlay
         ; lunit = {!!}
         ; runit = IGiveUp
         ; assoc = IGiveUp
         } where
    overlay : [ Box (HoleOr X) -:> Box (HoleOr X) -:> Box (HoleOr X) ]
    overlay = {!!}

-- You may find the following useful later.

accumulate : forall {X Y} -> Monoid Y -> (X -> Y) -> List X -> Y
accumulate {X}{Y} m f = go where
  open Monoid m
  go : List X -> Y
  go [] = e
  go (x :: xs) = op (f x) (go xs)

-- For fun, and the shape of things to come, build two box tilings.
-- Make sure each has a rectangle of text in the middle and Hole all
-- around. Make sure that the rectangles overlap each other, but not
-- completely. See what happens when you overlay them, either way
-- around.

module TestOverlay where

  open module _Goo {X}{wh : Nat * Nat}
    = Monoid (overlayMonoid (matrixCutKit {X}){wh})

  rectangleA : Box (HoleOr (Matrix Char)) (20 , 15)
  rectangleA = -- {!!}
    leri 3 (tile hole) 17 (leri 10
     (tobo 3 (tile hole) 12 (tobo 6
      (tile (stuff (
          [- "+--------+" -] ::
          [- "|Let joy |" -] ::
          [- "|be uncon|" -] ::
          [- "|fined!  |" -] ::
          [- "|(thanks)|" -] ::
          [- "+--------+" -] :: [] )))  6 (tile hole) refl) refl)
    7 (tile hole) refl) refl

  rectangleB : Box (HoleOr (Matrix Char)) (20 , 15)
  rectangleB = -- {!!}
    leri 7 (tile hole) 13 (leri 10
     (tobo 6 (tile hole) 9 (tobo 6 
      (tile (stuff (
          [- "+--------+" -] ::
          [- "|My heart|" -] ::
          [- "|has gone|" -] ::
          [- "|but I   |" -] ::
          [- "|live on.|" -] ::
          [- "+--------+" -] :: [] ))) 3 (tile hole) refl) refl)
    3 (tile hole) refl) refl

  frontA_backB : Matrix Char (20 , 15)
  frontA_backB = renderHoleOrText (op rectangleA rectangleB)

  frontB_backA : Matrix Char (20 , 15)
  frontB_backA = renderHoleOrText (op rectangleB rectangleA)


---------------------------------------------------------------------------
--                                                                       --
--  EPISODE 4: APPLICATIONS                                   [6 marks]  --
--                                                                       --
---------------------------------------------------------------------------

-- You may need to look at the Ex4AgdaSetup file to find some of the
-- relevant kit for this episode, and it's worth looking there for
-- goodies, anyway. We start from the idea of a main loop.

{- This is the bit of code I wrote in Haskell to animate your code. -}
postulate
  mainAppLoop : {S : Set} ->             -- program state
    -- INITIALIZER
    S ->                              -- initial state
    -- EVENT HANDLER
    (Event -> S ->                    -- event and state in
     S ** List Action) ->              -- new state and screen actions out
    -- PUT 'EM TOGETHER AND YOU'VE GOT AN APPLICATION!
    IO One
{-# COMPILED mainAppLoop (\ _ -> HaskellSetup.mainAppLoop) #-}


-- To make a thing you can run, you need to
--   (i)    choose a type to represent the program's internal state S
--   (ii)   give the initial state
--   (iii)  explain how, given an event and the current state, to
--            produce a new state and a list of actions to update the
--            display.


---------------------------------------------------------------------------
-- PAINTINGS                                                             --
---------------------------------------------------------------------------

-- Now that we're in colour, one cell of display will be a ColourChar ...

data ColourChar : Set where
  _-_/_ : (fg : Colour)(c : Char)(bg : Colour) -> ColourChar

-- ... e.g.     green - '*' / black    for a green * on black.

-- a painting is a Box structure whose basic tiles are either transparent
-- holes or opaque rectangles of coloured text.

Painting : Nat * Nat -> Set
Painting = Box (HoleOr (Matrix ColourChar))

-- Now your turn. Making use of the equipment you developed in epsiode 2,
-- get us from a Painting to a List Action in two hops. Note that you will
-- have to decide how to render a hole: some bland background stuff, please.
-- (2 marks)

paintMatrix : [ Painting -:> Matrix ColourChar ]
paintMatrix p = {!!}

paintAction : {wh : Nat * Nat} -> Matrix ColourChar wh -> List Action
paintAction m = {!!}


---------------------------------------------------------------------------
-- APPLICATIONS (I've done this bit for you.)                            --
---------------------------------------------------------------------------

-- Here's a general idea of what it means to be an "application".
-- The "coinductive" keyword means that an application is a recursive
-- structure which is defined by its observable behaviour, which is
-- generated on demand. Applications are indexed by their size: the
-- amount of space in which they must fit.

record Application (wh : Nat * Nat) : Set where
  coinductive
  field
    handleKey     : Key -> Application wh
      -- on getting a keystroke, the application should evolve into a new
      -- application, the same size
    handleResize  : (wh' : Nat * Nat) -> Application wh'
      -- an application can be told to resize, so it must become a new
      -- application of the demanded size
    paintMe       : Painting wh
      -- an application must know how to display itself
    cursorMe      : Nat * Nat  -- x,y coords
      -- an application must know where its cursor is
open Application public

-- I found I needed ordinary list concatentation.
_+L_ : {X : Set} -> List X -> List X -> List X
[] +L ys = ys
(x :: xs) +L ys = x :: (xs +L ys)
infixr 3 _+L_

APP : Set
APP = Sg (Nat * Nat) Application

appPaint : APP -> List Action
appPaint (_ , app) =
  goRowCol 0 0 :: (paintAction o paintMatrix) p
     -- must have composition here, to work around compiler bug
     -- paintAction (paintMatrix p)
     -- segfaults, because p is erased
  +L (goRowCol (snd xy) (fst xy) :: [])
  where
    p  = paintMe app
    xy = cursorMe app

appHandler : Event -> APP -> APP ** List Action
appHandler (key k) (wh , app) = app' , appPaint app'
  where
    app' : APP
    app' = _ , handleKey app k
appHandler (resize w h) (wh , app) = app' , appPaint app'
  where
    app' : APP
    app' = _ , handleResize app (w , h)

appMain : (forall {wh} -> Application wh) -> IO One
appMain app = mainAppLoop ((0 , 0) , app) appHandler
  -- will get resized dynamically to size of terminal, first thing


---------------------------------------------------------------------------
-- AN EXAMPLE APPLICATION                                                --
---------------------------------------------------------------------------

sillyChar : Char -> forall {wh} -> Painting wh
sillyChar c = tile (stuff (vec (vec (green - c / black)) ))

sillyApp : forall {wh} -> Char -> Application wh
handleKey    (sillyApp _) (char c) = sillyApp c
handleKey    (sillyApp c) _ = sillyApp c
handleResize (sillyApp c) wh' = sillyApp c
paintMe      (sillyApp {suc (suc w) , suc (suc h)} c) =
  tobo 1 (sillyChar c)
          (suc h) (tobo h
            (leri 1 (sillyChar c) (suc w)
             (leri w (sillyChar ' ') 1 (sillyChar c) (plusCommFact w 1))
             refl)
            1 (sillyChar c) (plusCommFact h 1) )
          refl
paintMe      (sillyApp {_} c) = sillyChar c
cursorMe     (sillyApp c) = 0 , 0

{-(-}
main : IO One
main = appMain (sillyApp '*')
{-)-}


---------------------------------------------------------------------------
-- COMPARING TWO NUMBERS                                                 --
---------------------------------------------------------------------------

-- You've done the tricky part in episode 3, comparing two splittings of
-- the same number. Here's an easy way to reuse that code just to compare
-- two numbers. It may help in what is to come.

Compare : Nat -> Nat -> Set
Compare x y = CutCompare x y y x (x +N y)

compare : (x y : Nat) -> Compare x y
compare x y = cutCompare x y y x (x +N y) refl (plusCommFact y x)

-- To make sure you've got the message, try writing these things
-- "with compare" to resize paintings. If you need to make a painting
-- bigger, pad its right or bottom with a hole. If you need to make it
-- smaller, trim off the right or bottom excess. You have all the gadgets
-- you need! (1 mark)

cropPadLR : (w h w' : Nat) -> Painting (w , h) -> Painting (w' , h)
cropPadLR w h w' p = {!!}

cropPadTB : (w h h' : Nat) -> Painting (w , h) -> Painting (w , h')
cropPadTB w h h' p = {!!}


---------------------------------------------------------------------------
-- THE MOVING RECTANGLE                                                  --
---------------------------------------------------------------------------

-- This is the crux of the episode. Please build me an application which
-- displays a movable resizeable rectangle drawn with ascii art as follows
--
--           +--------------+
--           |              |
--           |              |
--           +--------------+
--
-- The "size" of the application is the terminal size: the rectangle should
-- be freely resizable *within* the terminal, so you should pad out the
-- rectangle to the size of the screen using "hole".
-- That is, only the rectangle is opaque; the rest is transparent.
-- The background colour of the rectangle should be given as an argument.
-- The foreground colour of the rectangle should be white.
-- The rectangle should have an interior consisting of opaque space with
-- the given background colour.
--
-- The arrow keys should move the rectangle around inside the terminal
-- window, preserving its size (like when you drag a window around).
-- Shifted arrow keys should resize the rectangle by moving its bottom
-- right corner (again, like you might do with a mouse).
-- You do not need to ensure that the rectangle fits inside the terminal.
-- The cursor should sit at the bottom right corner of the rectangle.
--
-- Mac users: the Terminal application which ships with OS X does NOT
-- give the correct treatment to shift-up and shift-down. You can get a
-- suitable alternative from http://iterm2.com/ (Thank @sigfpe for the tip!)

record RectState : Set where
  constructor rect
  field
    gapL rectW : Nat
    gapT rectH : Nat

rectKey : Key -> RectState -> RectState
rectKey k r = {!!}
-- (1 mark)

rectApp : Colour -> RectState -> forall {wh} -> Application wh
handleKey    (rectApp c r) k   = rectApp c (rectKey k r)
handleResize (rectApp c r) wh' = rectApp c r
paintMe      (rectApp c (rect gapL rectW gapT rectH)) = {!!}
cursorMe     (rectApp c (rect gapL rectW gapT rectH)) = {!!}
-- (2 marks, being 1.5 for paintMe, 0.5 for cursorMe)


{-+}
main : IO One
main = appMain (rectApp blue (rect 10 40 3 15))
{+-}


---------------------------------------------------------------------------
--                                                                       --
-- EPISODE 5: COMBINING APPLICATIONS IN LAYERS                [4 marks]  --
--                                                                       --
---------------------------------------------------------------------------

{-
Implement an application which combines a list of applications into *one*
layered application, like a desktop in a windowing environment. The first
layer in the list should be displayed at the front, and the others behind
it in order, using the overlay monoid to combine the images.

The expected keystroke behaviour is as follows:
  escape   generates a new rectangle application of the next colour in
             the given list of colours
  delete   closes the first application in the list if there is one
  tab      cycles the list of applications, so the hold front layer
             moves to the back and all the others move forward
  all other keys should be passed on to the application at the front
    (so that if it is a rectangle application, moving and resizing should
    work)

The cursor should be wherever the front application says it should be,
or at (0 , 0) if there are no applications.
-}

defaultRect : RectState
defaultRect = rect 10 40 3 15

layered : forall {wh} -> List Colour -> List (Application wh) -> Application wh
handleKey    (layered cs as) x   = {!!}
handleResize (layered cs as) wh' = {!!}
paintMe      (layered cs as)     = {!!}
cursorMe     (layered cs as)     = {!!}
-- (4 marks, being one for each of the four fields)

{-+} -- comment this back in when you're ready
main : IO One
main = appMain (layered
  (blue :: red :: green :: magenta :: cyan :: yellow :: [])
  [])
{+-}
