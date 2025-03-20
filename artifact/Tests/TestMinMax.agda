
module artifact.Tests.TestMinMax where

open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Maybe
open import Agda.Builtin.Equality

open import artifact.Tests.TestCases
open import artifact.Main
open import artifact.MinMax

_ : lookupMin test1 ≡ just (5 , "a")
_ = refl

_ : lookupMin test2 ≡ nothing
_ = refl

_ : lookupMax test1 ≡ just (5 , "a")
_ = refl

_ : lookupMax test2 ≡ nothing
_ = refl

_ : findMin test1 ≡ 3 , "b"
_ = refl

_ : findMax test1 ≡ 5 , "a"
_ = refl

-- Test error findMin and findMax

_ : deleteMin test3 ≡ test4
_ = refl

_ : deleteMax test3 ≡ test5
_ = refl

_ : deleteFindMin test3 ≡ (3 , "b") , test4
_ = refl

_ : deleteFindMax test3 ≡ (7 , "c") , test1
_ = refl

-- TO DO: write more tests