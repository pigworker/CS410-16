module Lec14 where

open import CS410-Prelude
open import CS410-Indexed

data Status : Set where
  opened closed : Status

data FileCommand : Status -> Set where
  fopen  : String -> FileCommand closed
  fgetc  : FileCommand opened
  fclose : FileCommand opened

FileResponse : (s : Status)(c : FileCommand s) -> Set
FileResponse .closed (fopen x) = Status
FileResponse .opened fgetc = Char
FileResponse .opened fclose = One

FileNext : (s : Status)(c : FileCommand s)(r : FileResponse s c) -> Status
FileNext .closed (fopen x) r = r
FileNext .opened fgetc r = opened
FileNext .opened fclose <> = closed

foo : FreeIx (FileCommand <! FileResponse / FileNext) (\ s -> (s == closed) * List Char)
        closed
foo = do (fopen "mumble.txt" , (\
  { opened -> do (fgetc , (\ c -> do (fclose , (\ { <> -> ret (refl , (c :: [])) }))))
  ; closed -> ret (refl , [])
  }))
