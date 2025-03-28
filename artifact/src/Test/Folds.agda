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

-- foldrList f z (foldr _∷_ ( x :: xs) l)
-- foldrList f z (x ∷ (foldr _∷_ xs l))
-- f x (foldrList f z (foldr _∷_ xs l))
-- f x (foldrList f (foldrList f z l) xs)   Induction
-- foldrList f (foldrList f z l) (x :: xs)

help1 : {{Comparable K}} → (f : A → V → V) → (z : V) → (l : Map K A) → (x : A) → (xs : List A) 
   → foldrList f z (foldr _∷_ (x ∷ xs) l) ≡ f x (foldrList f z (foldr _∷_ xs l))
help1 f z l x xs = trans {!   !} -- foldr _∷_ (x ∷ xs) l becomes x ∷ (foldr _∷_ xs l)
    {!   !} -- Definition foldrList

foldrThing : {{Comparable K}} → (f : A → V → V) → (z : V) → (l : Map K A) → (xs : List A) 
    → foldrList f z (foldr _∷_ xs l) ≡ foldrList f (foldrList f z xs) (elems l)
foldrThing f z l [] = refl
foldrThing f z l (x ∷ xs) = trans (help1 f z l x xs) 
     (trans (cong (λ y → f x y) (foldrThing f z l xs)) 
     {!   !}) -- Defintion of foldrList

-- foldr f z == foldr f z . elems
testFoldr : {{Comparable K}} → (f : A → V → V) → (z : V) → (m : Map K A) → foldr f z m ≡ foldrList f z (elems m)
testFoldr f z tip = refl
testFoldr f z (node x k v l r) = trans (testFoldr f (f v (foldr f z r)) l) 
     (trans (cong (λ y → foldrList f (f v y) (elems l)) (testFoldr f z r))  
     (trans (sym(foldrThing f z l (v ∷ elems r))) refl))                                         

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