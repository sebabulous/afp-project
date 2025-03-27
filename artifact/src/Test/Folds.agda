module Test.Folds where

open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Equality

open import Test.Cases
open import Map.Folds
open import Map.Construction
open import Map.Conversion
open import Map.Map

private variable
    V K A : Set
    z : V

-- foldr f z == foldr f z . elems
testFoldr : {{Comparable K}} → (f : A → V → V) → (z : V) → (m : Map K A) → foldr f z m ≡ foldrList f z (elems m)
testFoldr f z tip = refl
testFoldr f z (node x x₁ x₂ m m₁) = 
    trans (testFoldr f (f x₂ (foldr f z m₁)) m) 
    (trans (cong (λ y → foldrList f (f x₂ y) (elems m)) (testFoldr f z m₁)) 
    (trans {!   !} {!   !})) 
    -- foldrList f (f x₂ (foldr f z m₁)) (elems m) ≡ 
    -- foldrList f (f x₂ (foldrList f z (elems m₁))) (elems m) ≡
    -- foldrList f (foldrList f z (x₂ ∷ (elems m₁))) (elems m)  
    -- 
    -- foldrList f z (foldr _∷_ [] (node x x₁ x₂ m m₁))
    -- foldrList f z (elems (node x x₁ x₂ m m₁))

-- foldl f z == foldl f z . elems
testFoldl : {{Comparable K}} → (f : V → A → V) → (z : V) → (m : Map K A) → foldl f z m ≡ foldlList f z (elems m)
testFoldl _ _ tip = refl
testFoldl f z (node x x₁ x₂ m m₁) = 
    trans (testFoldl f (f (foldl f z m) x₂) m₁) 
    (trans {!   !} {!   !}) 

-- foldrWithKey f z == foldr (uncurry f) z . toAscList
testFoldrWithKey : {f : K → A → V → V} → {{Comparable K}} → (m : Map K A) → foldrWithKey f z m ≡ foldrList (λ p x → f (Pair.fst p) (Pair.snd p) x) z (toAscList m)
testFoldrWithKey tip = refl
testFoldrWithKey (node x x₁ x₂ m m₁) = trans {!   !} {!   !}

-- foldlWithKey f z == foldl (\z' (kx, x) -> f z' kx x) z . toAscList
testFoldlWithKey : {f : V → K → A → V} → {{Comparable K}} → (m : Map K A) → foldlWithKey f z m ≡ foldlList (λ x p → f x (Pair.fst p) (Pair.snd p)) z (toAscList m)
testFoldlWithKey tip = refl
testFoldlWithKey (node x x₁ x₂ m m₁) = trans {!   !} {!   !}

-- foldMapWithKey f = fold . mapWithKey f
--_ : {M : Set} → {{Monoid M}} → {f : K → A → M} → foldMapWithKey f m ≡ {!   !}
-- _ = {!   !}
    
-- TO DO: add tests for the strict folds. Are they the same as the above?? 