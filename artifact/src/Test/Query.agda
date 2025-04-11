module Test.Query where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Maybe
open import Agda.Builtin.Equality

open import Test.Cases
open import Map.Construction
open import Map.Query
open import Map.Map

-- %%%%%%%%%%%%%%%%%%%%%%%%% Size functions %%%%%%%%%%%%%%%%%%%%%%%%%

-- _ : null testEmpty ≡ true
-- _ = refl

-- _ : null (singleton (Pair.fst KV5a) (Pair.snd KV5a)) ≡ false
-- _ = refl

_ : size testEmpty ≡ 0
_ = refl

_ : size (singleton (Pair.fst KV5a) (Pair.snd KV5a)) ≡ 1
_ = refl

_ : size test537 ≡ 3
_ = refl

-- %%%%%%%%%%%%%%%%%%%%%%%%% Lookup functions %%%%%%%%%%%%%%%%%%%%%%%%%

-- TO DO: write tests lookup

_ : test53 !? 1 ≡ nothing
_ = refl

_ : test53 !? Pair.fst KV5a ≡ just (Pair.snd KV5a)
_ = refl

-- TO DO: write test ! of error

_ : test53 ! Pair.fst KV5a ≡ Pair.snd KV5a
_ = refl

_ : findWithDefault "x" 1 test53 ≡ "x"
_ = refl

_ : findWithDefault "x" (Pair.fst KV5a) test53 ≡ Pair.snd KV5a
_ = refl

_ : member (Pair.fst KV5a) test53 ≡ true
_ = refl

_ : member 1 test53 ≡ false
_ = refl

_ : notMember (Pair.fst KV5a) test53 ≡ false
_ = refl

_ : notMember 1 test53 ≡ true
_ = refl

_ : lookupLT 3 test35 ≡ nothing
_ = refl

_ : lookupLT 4 test35 ≡ just KV3b
_ = refl

_ : lookupGT 5 test35 ≡ nothing
_ = refl

_ : lookupGT 4 test35 ≡ just KV5a
_ = refl

_ : lookupLE 2 test35 ≡ nothing
_ = refl

_ : lookupLE 4 test35 ≡ just KV3b
_ = refl

_ : lookupLE 5 test35 ≡ just KV5a
_ = refl

_ : lookupGE 3 test35 ≡ just KV3b
_ = refl

_ : lookupGE 4 test35 ≡ just KV5a
_ = refl

_ : lookupGE 6 test35 ≡ nothing
_ = refl