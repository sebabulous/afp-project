module Test.Folds where

open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Equality
open import Agda.Builtin.List

open import Test.Cases
open import Map.Folds
open import Map.Construction
open import Map.Conversion
open import Map.Map

private variable
    V K A : Set
    z : V


foldrIsElems : {{Comparable K}} → (m : Map K A) 
    → foldr _∷_ [] m ≡ elems m
foldrIsElems tip = refl
foldrIsElems (node x k v l r) = cong (λ inner → foldr _∷_ inner l) (cong (v ∷_) (foldrIsElems r))

elemsIsFoldr : {{Comparable K}} → ∀{x} → (k : K) → (v : A) → (l : Map K A) → (r : Map K A)
    → elems (node x k v l r) ≡ foldr _∷_ (v ∷ foldr _∷_ [] r) l
elemsIsFoldr k v l r = refl

mutual
    foldrListFoldr : {{Comparable K}} → (f : A → V → V) → (z : V) → (v : A) → (l : Map K A) → (r : Map K A) 
        → foldr f (f v (foldr f z r)) l ≡ foldrList f z (foldr _∷_ (v ∷ foldr _∷_ [] r) l)
    foldrListFoldr f z v tip r = cong (λ y → f v y) (trans (foldrTest f z r) (sym (cong (λ y → foldrList f z y) (foldrIsElems r))))
    foldrListFoldr f z v (node x kₗ vₗ lₗ rₗ) r = {!  !}

    foldrTest : {{Comparable K}} → (f : A → V → V) → (z : V) → (m : Map K A) 
        → foldr f z m ≡ foldrList f z (elems m)
    foldrTest f z tip = refl
    foldrTest f z (node x k v l r) = foldrListFoldr f z v l r


--foldrFoldr : {{Comparable K}} → (f : A → V → V) → (z : V) → (m : Map K A) → foldrList f z (foldr _∷_ [] m) ≡ foldrList f z (elems m)
--foldrFoldr f z m = cong (λ lst → foldrList f z lst) (foldIsElems m)



foldrThing : {{Comparable K}} → (f : A → V → V) → (z : V) → (k : K) → (v : A) → (l : Map K A) → (r : Map K A) 
    → foldr f (f v (foldr f z r)) l ≡ foldrList f z (foldr _∷_ (v ∷ foldr _∷_ [] r) l)
foldrThing f z k v tip r = {! foldrIsElems r  !}
foldrThing f z k v (node x x₁ x₂ l l₁) r = {!   !}

-- foldr f z == foldr f z . elems
testFoldr : {{Comparable K}} → (f : A → V → V) → (z : V) → (m : Map K A) → foldr f z m ≡ foldrList f z (elems m)
testFoldr f z tip = refl
--testFoldr f z (node x k v l r) = {! cong (λ lst → foldrList f z lst) (foldIsElems (node x k v l r)) !}
testFoldr f z (node x k v l r) = {! foldrIsElems (node x k v l r) !}
--testFoldr f z (node x k v l r) = {! (testFoldr f z r)  !}
--testFoldr f z (node x k v l r) = {! cong (λ inner → foldr f inner l) (cong (λ a → f v a) (testFoldr f z r))  !}
{-
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
-}

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