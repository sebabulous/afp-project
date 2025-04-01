module Test.Traversal where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.String
open import Agda.Builtin.Equality

open import Test.Cases
open import Test.Valid
open import Map.Construction
open import Map.Map
open import Map.Traversal

_ : map (λ x → primStringAppend x "x") test35 ≡ test35addX
_ = refl

_ : mapWithKey (λ key x → primStringAppend (primStringAppend (primShowNat key) ":") x) test35 ≡ test35update35
_ = refl

-- Add test traverseWithKey f m == fromList <$> traverse (\(k, v) -> (,) k <$> f k v) (toList m)
_ : {K V B : Set}{F : Set → Set}{m : Map K V} → {{Applicative F}} → {f : K → V → F B} → {! traverseWithKey ? ?  !} ≡ {!   !}
_ = {!   !}
-- Add tests for traverseMaybeWithKey

_ : mapAccum (λ a b → primStringAppend a b , primStringAppend b "x") "Everything: " test35 ≡ ("Everything: ba" , test35addX) 
_ = refl

_ : mapAccumWithKey (λ a k b → primStringAppend a (primStringAppend " " (primStringAppend (primShowNat k) (primStringAppend "-" b))) , primStringAppend b "x") "Everything:" test35 ≡ ("Everything: 3-b 5-a" , test35addX) 
_ = refl

-- Add tests for mapAccumRWithKey

_ : mapKeys (λ x → x + 1) test35 ≡ test35add1 
_ = refl

_ : mapKeys (λ _ → 3) test35 ≡ singleton (Pair.fst KV3b) (Pair.snd KV5a)
_ = refl

_ : mapKeys (λ _ → 5) test35 ≡ singleton (Pair.fst KV5a) (Pair.snd KV5a) 
_ = refl

_ : mapKeysWith primStringAppend (λ _ → 3) test35 ≡ singleton 3 "ab" 
_ = refl

_ : mapKeysWith primStringAppend (λ _ → 5) test35 ≡ singleton 5 "ab" 
_ = refl

_ : mapKeysMonotonic (λ k → k * 2) test35 ≡ test35times2 
_ = refl

_ : valid (mapKeysMonotonic (λ k → k * 2) test35) ≡ true 
_ = refl

_ : valid (mapKeysMonotonic (λ _ → 1) test35) ≡ false 
_ = refl