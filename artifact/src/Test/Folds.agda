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
open import Map.Traversal

private variable
    V K A M : Set
    z : V

foldrIdent : (as : List A)
    → foldrList _∷_ [] as ≡ as
foldrIdent [] = refl
foldrIdent (x ∷ as) = cong (x ∷_) (foldrIdent as)

foldrList-split : (f : A → V → V) → (z : V) → (ls : List A) → (rs : List A)
    → foldrList f z (ls ++ rs) ≡ foldrList f (foldrList f z rs) ls
foldrList-split f z [] rs = refl
foldrList-split f z (x ∷ ls) rs = cong (f x) (foldrList-split f z ls rs)

foldlList-split : (f : V → A → V) → (z : V) → (ls : List A) → (rs : List A)
    → foldlList f z (ls ++ rs) ≡ foldlList f (foldlList f z ls) rs
foldlList-split f z [] rs = refl
foldlList-split f z (x ∷ ls) rs = foldlList-split f (f z x) ls rs

mutual
    elems≡elems : {{Comparable K}} → ∀ x k → (v : A) → (l : Map K A) → (r : Map K A)
        → elems (node x k v l r) ≡ elems l ++ (v ∷ elems r)
    elems≡elems x k v l r = 
        elems (node x k v l r) 
           ≡⟨ foldr≡foldrList-elems _∷_ (v ∷ elems r) l ⟩ 
        ((foldrList _∷_ (v ∷ elems r) (elems l) 
           ≡⟨ cong (λ y → foldrList _∷_ (v ∷ y) (elems l)) (foldr≡foldrList-elems _∷_ [] r) ⟩ 
        ((foldrList _∷_ (v ∷ foldrList _∷_ [] (elems r)) (elems l) 
           ≡⟨ sym (foldrList-split _∷_ [] (elems l) (v ∷ elems r)) ⟩ 
        ((foldrList _∷_ [] (elems l ++ (v ∷ elems r)) 
           ≡⟨ (foldrIdent (elems l ++ (v ∷ elems r))) ⟩ 
        ((elems l ++ (v ∷ elems r)) ∎) ))))))
    
    -- foldr f z == foldr f z . elems  
    foldr≡foldrList-elems : {{Comparable K}} → (f : A → V → V) → (z : V) → (m : Map K A)
        → foldr f z m ≡ foldrList f z (elems m)
    foldr≡foldrList-elems f z tip = refl
    foldr≡foldrList-elems f z (node x k v l r) = 
        foldr f z (node x k v l r) 
           ≡⟨ cong (λ y → foldr f y l) (cong (f v) (foldr≡foldrList-elems f z r)) ⟩ 
        (foldr f (f v (foldrList f z (elems r))) l 
           ≡⟨ foldr≡foldrList-elems f (f v (foldrList f z (elems r))) l ⟩ 
        (foldrList f (f v (foldrList f z (elems r))) (elems l) 
           ≡⟨ sym (foldrList-split f z (elems l) (v ∷ elems r)) ⟩ 
        (foldrList f z (elems l ++ (v ∷ elems r)) 
           ≡⟨ cong (foldrList f z) (sym (elems≡elems  x k v l r)) ⟩ 
        (foldrList f z (elems (node x k v l r)) ∎)))) 

-- foldl f z == foldl f z . elems
foldl≡foldlList-elems : {{Comparable K}} → (f : V → A → V) → (z : V) → (m : Map K A)
    → foldl f z m ≡ foldlList f z (elems m) 
foldl≡foldlList-elems f z tip = refl
foldl≡foldlList-elems f z (node x k v l r) = 
    foldl f z (node x k v l r) 
        ≡⟨ cong (λ y → foldl f y r) (cong (λ y → f y v) (foldl≡foldlList-elems f z l)) ⟩ 
    ((foldl f (f (foldlList f z (elems l)) v) r 
        ≡⟨ foldl≡foldlList-elems f (f (foldlList f z (elems l)) v) r ⟩ 
    ((foldlList f (f (foldlList f z (elems l)) v) (elems r) 
        ≡⟨ sym (foldlList-split f z (elems l) (v ∷ elems r)) ⟩ 
    (foldlList f z (elems l ++ (v ∷ elems r)) 
        ≡⟨ cong (foldlList f z) (sym (elems≡elems  x k v l r)) ⟩ 
    (foldlList f z (elems (node x k v l r)) ∎)))))) 

mutual 
    toAscList≡toAscList : {{Comparable K}} → ∀ x k → (v : A) → (l : Map K A) → (r : Map K A)
            → toAscList (node x k v l r) ≡ toAscList l ++ ((k , v) ∷ toAscList r) 
    toAscList≡toAscList x k v l r = 
        toAscList (node x k v l r) 
            ≡⟨ testFoldrWithKey ((λ k v kvs → (k , v) ∷ kvs)) ((k , v) ∷ toAscList r) l ⟩ 
        (foldrList (λ p kvs → (Pair.fst p , Pair.snd p) ∷ kvs) ((k , v) ∷ toAscList r) (toAscList l) 
            ≡⟨ cong (λ y → foldrList _∷_ ((k , v) ∷ y) (toAscList l)) (testFoldrWithKey (λ k v kvs → (k , v) ∷ kvs) [] r) ⟩ 
        (foldrList _∷_ ((k , v) ∷ foldrList (λ p kvs → (Pair.fst p , Pair.snd p) ∷ kvs) [] (toAscList r)) (toAscList l) 
            ≡⟨ sym (foldrList-split _∷_ [] (toAscList l) ((k , v) ∷ toAscList r)) ⟩ 
        (foldrList _∷_ [] (toAscList l ++ ((k , v) ∷ toAscList r)) 
            ≡⟨ foldrIdent (toAscList l ++ ((k , v) ∷ toAscList r)) ⟩ 
        ((toAscList l ++ ((k , v) ∷ toAscList r)) ∎)))) 

    -- foldrWithKey f z == foldr (uncurry f) z . toAscList
    testFoldrWithKey : {{Comparable K}} → (f : K → A → V → V) → (z : V) → (m : Map K A) 
        → foldrWithKey f z m ≡ foldrList (λ p x → f (Pair.fst p) (Pair.snd p) x) z (toAscList m)
    testFoldrWithKey f z tip = refl
    testFoldrWithKey f z (node x k v l r) = 
        foldrWithKey f z (node x k v l r) 
            ≡⟨ cong (λ y → foldrWithKey f y l) (cong (f k v) (testFoldrWithKey f z r)) ⟩ 
        (foldrWithKey f (f k v (foldrList (λ p → f (Pair.fst p) (Pair.snd p)) z (toAscList r))) l 
            ≡⟨ testFoldrWithKey f (f k v (foldrList (λ p → f (Pair.fst p) (Pair.snd p)) z (toAscList r))) l ⟩ 
        (foldrList (λ p → f (Pair.fst p) (Pair.snd p)) (f k v (foldrList (λ p → f (Pair.fst p) (Pair.snd p)) z (toAscList r))) (toAscList l) 
            ≡⟨ sym (foldrList-split ((λ p → f (Pair.fst p) (Pair.snd p))) z (toAscList l) ((k , v) ∷ toAscList r)) ⟩ 
        (foldrList (λ p → f (Pair.fst p) (Pair.snd p)) z (toAscList l ++ ((k , v) ∷ toAscList r)) 
            ≡⟨ sym (cong (foldrList (λ p x → f (Pair.fst p) (Pair.snd p) x) z) (toAscList≡toAscList  x k v l r)) ⟩ 
        (foldrList (λ p x → f (Pair.fst p) (Pair.snd p) x) z (toAscList (node x k v l r)) ∎)))) 

-- foldlWithKey f z == foldl (\z' (kx, x) -> f z' kx x) z . toAscList
testFoldlWithKey : {{Comparable K}} → (f : V → K → A → V) → (z : V) → (m : Map K A) 
    → foldlWithKey f z m ≡ foldlList (λ x p → f x (Pair.fst p) (Pair.snd p)) z (toAscList m)
testFoldlWithKey f z tip = refl
testFoldlWithKey f z (node x k v l r) = 
    foldlWithKey f z (node x k v l r) 
        ≡⟨ cong (λ y → foldlWithKey f y r) (cong (λ y → f y k v) (testFoldlWithKey f z l)) ⟩ 
    ((foldlWithKey f (f (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z (toAscList l)) k v) r 
        ≡⟨ testFoldlWithKey f (f (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z (toAscList l)) k v) r ⟩ 
    (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) (f (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z (toAscList l)) k v) (toAscList r) 
        ≡⟨ sym (foldlList-split (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z (toAscList l) ((k , v) ∷ toAscList r)) ⟩ 
    (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z (toAscList l ++ ((k , v) ∷ toAscList r)) 
    ≡⟨ sym (cong (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z) (toAscList≡toAscList x k v l r)) ⟩ 
    (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z (toAscList (node x k v l r)) ∎))))) 

mappend≡foldrMappend : (x : Map K Nat) → (y : Nat) → foldr mappend y x ≡ mappend (fold x) y  
mappend≡foldrMappend x zero = {!   !}
mappend≡foldrMappend x (suc y) = cong {!   !} (mappend≡foldrMappend x y)

-- foldMapWithKey f = fold . mapWithKey f
-- proof with Nat because that is an instance of monoid
proofFoldMapWithKey : (f : K → V → Nat) → (m : Map K V) -- {K V M : Set} → {{Monoid M}} → (K → V → M) → Map K V → M 
    → foldMapWithKey f m ≡ fold (mapWithKey f m)
proofFoldMapWithKey f tip = refl
proofFoldMapWithKey f (node 1 k v l r) = {!   !} 
-- f k v ≡ ... ≡ mappend (f k v) zero ≡ 
-- mappend (f k v) (foldr mappend zero tip) ≡ foldr mappend (mappend (f k v) (foldr mappend zero tip)) tip ≡ 
-- foldr mappend zero (node 1 k (f k v) tip tip) ≡ fold (node 1 k (f k v) tip tip) ≡ fold (mapWithKey f m)
proofFoldMapWithKey f (node n k v l r) = 
    foldMapWithKey f (node n k v l r) 
        ≡⟨ {!   !} ⟩ 
    (mappend (foldMapWithKey f l) (mappend (f k v) (foldMapWithKey f r)) 
        ≡⟨ cong (mappend (foldMapWithKey f l)) (cong (mappend (f k v)) (proofFoldMapWithKey f r)) ⟩ 
    (mappend (foldMapWithKey f l) (mappend (f k v) (fold (mapWithKey f r))) 
        ≡⟨ cong (λ y → mappend y (mappend (f k v) (fold (mapWithKey f r)))) (proofFoldMapWithKey f l) ⟩ 
    (mappend (fold (mapWithKey f l)) (mappend (f k v) (fold (mapWithKey f r)))
        ≡⟨ sym (mappend≡foldrMappend (mapWithKey f l) (mappend (f k v) (fold (mapWithKey f r)))) ⟩ 
    (foldr mappend (mappend (f k v) (fold (mapWithKey f r))) (mapWithKey f l) 
        ≡⟨ refl ⟩ 
    (fold (mapWithKey f (node n k v l r)) ∎)))))
 
-- TO DO: add tests for the strict folds. Are they the same as the above??     