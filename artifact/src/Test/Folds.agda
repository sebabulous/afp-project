module Test.Folds where

open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Equality

open import Test.Cases
open import Map.Folds
open import Map.Construction
open import Map.Conversion
open import Map.Traversal
open import Map.Map

private variable
  K A B : Set
  m n : Nat


foldrVec-split : (f : A → B → B) → (z : B) → (ls : Vec A m) → (rs : Vec A n) → foldrVec f z (ls ++ rs) ≡ foldrVec f (foldrVec f z rs) ls
foldrVec-split f z [] rs = refl
foldrVec-split f z (x ∷ ls) rs = (foldrVec-split f z ls rs) under (f x)

mutual
  elems≡elems : {{Comparable K}} → ∀ k → (v : A) → (l : Map K A m) → (r : Map K A n) → elems (node k v l r) ≡ elems l ++ (v ∷ elems r)
  elems≡elems k v l r = refl

  foldr≡foldrList-elems : {{Comparable K}} → (f : A → B → B) → (z : B) → (map : Map K A n) → foldr f z map ≡ foldrVec f z (elems map)
  foldr≡foldrList-elems {K} {A} {B} {n} ⦃ x ⦄ f z tip = refl
  foldr≡foldrList-elems f z (node k v l r) = 
      foldr f z (node k v l r) 
          ≡⟨ ((foldr≡foldrList-elems f z r) under (f v)) under (λ y → foldr f y l) ⟩ 
      (foldr f (f v (foldrVec f z (elems r))) l 
          ≡⟨ foldr≡foldrList-elems f (f v (foldrVec f z (elems r))) l ⟩ 
      (foldrVec f (f v (foldrVec f z (elems r))) (elems l) 
          ≡⟨ sym (foldrVec-split f z (elems l) (v ∷ elems r)) ⟩ 
      (foldrVec f z (elems l ++ (v ∷ elems r)) 
          ≡⟨ (sym (elems≡elems k v l r)) under (foldrVec f z) ⟩ 
      (foldrVec f z (elems (node k v l r)) ∎))))