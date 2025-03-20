module artifact.Tests.TestCases where

open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.List

open import artifact.Construction
open import artifact.Main

test1 : Map Nat String
test1 = fromList ((5 , "a") ∷ (3 , "b") ∷ [])

test2 : Map Nat String
test2 = fromList []

test3 : Map Nat String
test3 = fromList ((5 , "a") ∷ (3 , "b") ∷ (7 , "c") ∷ [])

test4 : Map Nat String
test4 = fromList ((5 , "a") ∷ (7 , "c") ∷ [])

test5 : Map Nat String
test5 = fromList ((3 , "b") ∷ (5 , "a") ∷ []) 