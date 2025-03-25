module Test.Folds {V K A : Set}{{Comparable K}}{z : V} where

open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Equality

open import Test.Cases
open import Map.Folds
open import Map.Construction
open import Map.Conversion
open import Map.Map

-- foldr f z == foldr f z . elems
_ : {m : Map K A}{f : A → V → V} → foldr f z m ≡ foldrList f z (elems m)
_ = {!   !}

-- foldl f z == foldl f z . elems
_ : {m : Map K A}{f : V → A → V} → foldl f z m ≡ foldlList f z (elems m)
_ = {!   !}

-- foldrWithKey f z == foldr (uncurry f) z . toAscList
_ : {m : Map K A}{f : K → A → V → V} → foldrWithKey f z m ≡ foldrList (λ p x → f (Pair.fst p) (Pair.snd p) x) z (toAscList m)
_ = {!   !}

-- foldlWithKey f z == foldl (\z' (kx, x) -> f z' kx x) z . toAscList
_ : {m : Map K A}{f : V → K → A → V} → foldlWithKey f z m ≡ foldlList (λ x p → f x (Pair.fst p) (Pair.snd p)) z (toAscList m)
_ = {!   !}

-- foldMapWithKey f = fold . mapWithKey f
_ : {m : Map K A}{M : Set} → {{Monoid M}} → {f : K → A → M} → foldMapWithKey f m ≡ {!   !}
_ = {!   !}

-- TO DO: add tests for the strict folds. Are they the same as the above??