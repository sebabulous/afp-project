module SizedMap.Test.Traversal where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.String
open import Agda.Builtin.Equality

open import SizedMap.Test.Cases
open import SizedMap.Test.Valid
open import SizedMap.Construction
open import Helpers.Comparable
open import Helpers.Pair
open import SizedMap.Map
open import SizedMap.Traversal

-- All the tests should be on the left side of ≡ with test53 instead of test35
_ : map (λ x → primStringAppend x "x") test35 ≡ test35addX
_ = refl

_ : mapWithKey (λ key x → primStringAppend (primStringAppend (primShowNat key) ":") x) test53 ≡ test35update35
_ = refl

-- Add tests for traverseWithKey and traverseMaybeWithKey

_ : mapAccum (λ a b → primStringAppend a b , primStringAppend b "x") "Everything: " test35 ≡ ("Everything: ba" , test35addX) 
_ = refl

_ : mapAccumWithKey (λ a k b → primStringAppend a (primStringAppend " " (primStringAppend (primShowNat k) (primStringAppend "-" b))) , primStringAppend b "x") "Everything:" test35 ≡ ("Everything: 3-b 5-a" , test35addX) 
_ = refl

-- Add tests for mapAccumRWithKey

-- _ : mapKeys (λ x → x + 1) test35 ≡ test35add1 
-- _ = refl

-- _ : mapKeys (λ _ → 3) test35 ≡ singleton (Pair.fst KV3b) (Pair.snd KV5a)
-- _ = refl

-- _ : mapKeys (λ _ → 5) test35 ≡ singleton (Pair.fst KV5a) (Pair.snd KV5a) 
-- _ = refl

-- _ : mapKeysWith primStringAppend (λ _ → 3) test35 ≡ singleton 3 "ab" 
-- _ = refl

-- _ : mapKeysWith primStringAppend (λ _ → 5) test35 ≡ singleton 5 "ab" 
-- _ = refl

_ : mapKeysMonotonic (λ k → k * 2) test35 ≡ test35times2 
_ = refl

-- _ : valid (mapKeysMonotonic (λ k → k * 2) test35) ≡ true 
-- _ = {!  refl !}

-- _ : valid (mapKeysMonotonic (λ _ → 1) test35) ≡ false 
-- _ = {!  refl !}