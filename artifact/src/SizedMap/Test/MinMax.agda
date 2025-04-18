module SizedMap.Test.MinMax where

open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Maybe
open import Agda.Builtin.Equality

open import SizedMap.Test.Cases
open import SizedMap.Construction
open import Helpers.Comparable
open import Helpers.Pair
open import SizedMap.MinMax
open import SizedMap.Map

_ : lookupMin test53 ≡ just KV3b
_ = refl

_ : lookupMin testEmpty ≡ nothing
_ = refl

_ : lookupMax test53 ≡ just KV5a
_ = refl

_ : lookupMax testEmpty ≡ nothing
_ = refl

_ : findMin test53 ≡ KV3b
_ = refl

_ : findMax test53 ≡ KV5a
_ = refl

_ : deleteMin test537 ≡ test57
_ = refl

_ : deleteMax test537 ≡ test53
_ = refl

_ : deleteFindMin test537 ≡ KV3b , test57
_ = refl

_ : deleteFindMax test537 ≡ KV7c , test53
_ = refl

_ : updateMin (λ a -> just (primStringAppend "3:"  a)) test53 ≡ modId test35update3
_ = refl

_ : updateMin (λ a -> nothing) test53 ≡ modDelete (singleton (Pair.fst KV5a) (Pair.snd KV5a))
_ = refl

_ : updateMax (λ a -> just (primStringAppend "5:"  a)) test53 ≡ modId test35update5
_ = refl

_ : updateMax (λ a -> nothing) test53 ≡ modDelete (singleton (Pair.fst KV3b) (Pair.snd KV3b))
_ = refl

_ : updateMinWithKey (\ k a -> just (primStringAppend (primShowNat k) (primStringAppend ":" a))) test53 ≡ modId test35update3
_ = refl

_ : updateMinWithKey (\ _ _ -> nothing) test53 ≡ modDelete (singleton (Pair.fst KV5a) (Pair.snd KV5a))
_ = refl

_ : updateMaxWithKey (\ k a -> just (primStringAppend (primShowNat k) (primStringAppend ":" a))) test53 ≡ modId test35update5
_ = refl

_ : updateMaxWithKey (\ _ _ -> nothing) test53 ≡ modDelete (singleton (Pair.fst KV3b) (Pair.snd KV3b))
_ = refl

_ : minView test53 ≡ (Pair.snd KV3b , singleton (Pair.fst KV5a) (Pair.snd KV5a))
_ = refl

_ : maxView test53 ≡ (Pair.snd KV5a , singleton (Pair.fst KV3b) (Pair.snd KV3b))
_ = refl

_ : minViewWithKey test53 ≡ (KV3b , singleton (Pair.fst KV5a) (Pair.snd KV5a)) 
_ = refl

_ : maxViewWithKey test53 ≡ (KV5a , singleton (Pair.fst KV3b) (Pair.snd KV3b)) 
_ = refl
