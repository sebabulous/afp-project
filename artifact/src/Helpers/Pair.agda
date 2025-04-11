module Helpers.Pair where

-- source: https://agda.readthedocs.io/en/v2.5.2/language/record-types.html
record Pair (A B : Set): Set where
  constructor _,_
  field
    fst : A
    snd : B