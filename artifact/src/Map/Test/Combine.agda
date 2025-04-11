module Map.Test.Combine where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Agda.Builtin.Equality
open import Helpers.Pair

open import Map.Test.Cases
open import Map.Combine
open import Map.Construction
open import Map.Conversion
open import Helpers.Comparable
open import Map.Map

-- inp1 : Map Nat Nat
-- inp1 = fromList ((23 , 1) ∷ (2 , 6) ∷ (42 , 3) ∷ (12 , 8) ∷ (32 , 15) ∷ (15 , 3) ∷ (7 , 26) ∷ [])
inp1 : List (Pair Nat Nat)
inp1 = (23 , 1) ∷ (2 , 6) ∷ (42 , 3) ∷ (13 , 8) ∷ (32 , 15) ∷ (15 , 3) ∷ (1 , 26) ∷ []

-- inp2 : Map Nat Nat
-- inp2 = fromList ((14 , 3) ∷ (7 , 8) ∷ (29 , 5) ∷ (12 , 10) ∷ (20 , 1) ∷ (33 , 6) ∷ [])
inp2 : List (Pair Nat Nat)
inp2 = (14 , 3) ∷ (7 , 8) ∷ (29 , 5) ∷ (12 , 10) ∷ (20 , 1) ∷ (33 , 6) ∷ []

_ : toAscList (union (fromList inp1) (fromList inp2)) ≡ sortKeysAsc (inp1 ++ inp2)
_ = refl

inp3 : List (Pair Nat Nat)
inp3 = (11 , 2) ∷ (8 , 5) ∷ (22 , 3) ∷ (30 , 7) ∷ (13 , 6) ∷ []

inp4 : List (Pair Nat Nat)
inp4 = (2 , 4) ∷ (25 , 9) ∷ (37 , 8) ∷ (16 , 3) ∷ (10 , 7) ∷ (21 , 1) ∷ (6 , 5) ∷ (27 , 6) ∷ (5 , 2) ∷ (35 , 10) ∷ (32 , 11) ∷ (28 , 12) ∷ []

_ : toAscList (unionWith _*_ (fromList inp3) (fromList inp4)) ≡ sortKeysAsc (combineWith _*_ inp3 inp4)
_ = refl

inp5 : List (Pair Nat Nat)
inp5 = (1 , 10) ∷ (3 , 15) ∷ (5 , 4) ∷ (7 , 7) ∷ (9 , 9) ∷ (11 , 3) ∷ (13 , 6) ∷ (15 , 2) ∷ (17 , 14) ∷ (19 , 1) ∷ (21 , 8) ∷ (23 , 13) ∷ (25 , 12) ∷ (27 , 5) ∷ (29 , 11) ∷ (31 , 16) ∷ (33 , 20) ∷ (35 , 18) ∷ (37 , 17) ∷ (39 , 19) ∷ (41 , 21) ∷ (43 , 22) ∷ (45 , 23) ∷ (47 , 24) ∷ (49 , 25) ∷ (51 , 26) ∷ (53 , 27) ∷ (55 , 28) ∷ (57 , 29) ∷ (59 , 30) ∷ []

inp6 : List (Pair Nat Nat)
inp6 = (6 , 5) ∷ (18 , 3) ∷ (24 , 4) ∷ (36 , 7) ∷ (48 , 6) ∷ (60 , 8) ∷ (72 , 2) ∷ (84 , 1) ∷ []

f : Nat → Nat → Nat → Nat
f k a a' = k + (a * a')

_ : toAscList (unionWithKey f (fromList inp5) (fromList inp6)) ≡ sortKeysAsc (combineWithKey f inp5 inp6)
_ = refl