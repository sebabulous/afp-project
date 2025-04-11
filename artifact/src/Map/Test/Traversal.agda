module Map.Test.Traversal where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.String
open import Agda.Builtin.Maybe
open import Agda.Builtin.Equality

open import Map.Test.Cases
open import Map.Test.Valid
open import Map.Construction
open import Map.Map
open import Map.Balance
open import Map.Traversal
open import Map.Conversion

_ : map (λ x → primStringAppend x "x") test35 ≡ test35addX
_ = refl

_ : mapWithKey (λ key x → primStringAppend (primStringAppend (primShowNat key) ":") x) test35 ≡ test35update35
_ = refl

_ : traverseWithKey (λ k v → if odd k then just (suc v) else nothing) test15Nat ≡ just test15SucNat
_ = refl

_ : traverseWithKey (λ k v → if odd k then just (suc v) else nothing) test2Nat ≡ nothing
_ = refl

_ : fmap toAscList (traverseMaybeWithKey (λ k v → if odd k then just (just (suc v)) else nothing) test15Nat) ≡ fmap toAscList (just test15SucNat) --node 2 1 2 tip (node 1 5 6 tip tip)
_ = refl

_ : traverseMaybeWithKey (λ k v → if odd k then just (just (suc v)) else nothing) test2Nat ≡ nothing
_ = refl

_ : mapAccum (λ a b → primStringAppend a b , primStringAppend b "x") "Everything: " test35 ≡ ("Everything: ba" , test35addX) 
_ = refl

_ : mapAccumWithKey (λ a k b → primStringAppend a (primStringAppend " " (primStringAppend (primShowNat k) (primStringAppend "-" b))) , primStringAppend b "x") "Everything:" test35 ≡ ("Everything: 3-b 5-a" , test35addX) 
_ = refl

_ : mapAccumRWithKey (λ a k b → primStringAppend a (primStringAppend " " (primStringAppend (primShowNat k) (primStringAppend "-" b))) , primStringAppend b "x") "Everything:" test35 ≡ ("Everything: 5-a 3-b" , test35addX) 
_ = refl

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