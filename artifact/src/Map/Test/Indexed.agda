module Map.Test.Indexed where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.String
open import Agda.Builtin.Equality

open import Map.Test.Cases
open import Helpers.Comparable
open import Map.Indexed
open import Map.Construction
open import Map.Conversion
open import Map.Map
open import Helpers.Pair

private variable
  K A : Set
  k : K
  a : A
  m n : Nat

inp1 : List (Pair Nat Nat)
inp1 = (101 , 2) ∷ (103 , 5) ∷ (107 , 4) ∷ (109 , 1) ∷ (113 , 6) ∷ (127 , 7) ∷ (131 , 3) ∷ (137 , 8) ∷ (139 , 9) ∷ (149 , 10) ∷ (151 , 11) ∷ (157 , 12) ∷ (163 , 13) ∷ (167 , 14) ∷ []

lookupIndex-fail : lookupIndex 13 (fromList inp1) ≡ nothing
lookupIndex-fail = refl

lookupIndex-succeed : lookupIndex 113 (fromList inp1) ≡ just 4
lookupIndex-succeed = refl

take≡takeList : toAscList (take 3 (fromList inp1)) ≡ takeList 3 (sortKeysAsc inp1)
take≡takeList = refl

take≡takeList-too-many : toAscList (take 100 (fromList inp1)) ≡ takeList 100 (sortKeysAsc inp1)
take≡takeList-too-many = refl

drop≡dropList : toAscList (drop 3 (fromList inp1)) ≡ dropList 3 (sortKeysAsc inp1)
drop≡dropList = refl

drop≡dropList-too-many : toAscList (drop 100 (fromList inp1)) ≡ dropList 100 (sortKeysAsc inp1)
drop≡dropList-too-many = refl