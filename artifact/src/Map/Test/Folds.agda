module Map.Test.Folds where

open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Strict

open import Map.Test.Cases
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
foldrIdent (x ∷ as) = (foldrIdent as) under (x ∷_) 

foldrList-split : (f : A → V → V) → (z : V) → (ls : List A) → (rs : List A)
    → foldrList f z (ls ++ rs) ≡ foldrList f (foldrList f z rs) ls
foldrList-split f z [] rs = refl
foldrList-split f z (x ∷ ls) rs = (foldrList-split f z ls rs) under (f x)

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
           ≡⟨ (foldr≡foldrList-elems _∷_ [] r) under (λ y → foldrList _∷_ (v ∷ y) (elems l)) ⟩ 
        ((foldrList _∷_ (v ∷ foldrList _∷_ [] (elems r)) (elems l) 
           ≡⟨ sym (foldrList-split _∷_ [] (elems l) (v ∷ elems r)) ⟩ 
        ((foldrList _∷_ [] (elems l ++ (v ∷ elems r)) 
           ≡⟨ (foldrIdent (elems l ++ (v ∷ elems r))) ⟩ 
        ((elems l ++ (v ∷ elems r)) ∎) ))))))
    
    foldr≡foldrList-elems : {{Comparable K}} → (f : A → V → V) → (z : V) → (m : Map K A)
        → foldr f z m ≡ foldrList f z (elems m)
    foldr≡foldrList-elems f z tip = refl
    foldr≡foldrList-elems f z (node x k v l r) = 
        foldr f z (node x k v l r) 
           ≡⟨ ((foldr≡foldrList-elems f z r) under (f v)) under (λ y → foldr f y l) ⟩ 
        (foldr f (f v (foldrList f z (elems r))) l 
           ≡⟨ foldr≡foldrList-elems f (f v (foldrList f z (elems r))) l ⟩ 
        (foldrList f (f v (foldrList f z (elems r))) (elems l) 
           ≡⟨ sym (foldrList-split f z (elems l) (v ∷ elems r)) ⟩ 
        (foldrList f z (elems l ++ (v ∷ elems r)) 
           ≡⟨ (sym (elems≡elems  x k v l r)) under (foldrList f z) ⟩ 
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
        ≡⟨ {!   !} ⟩ 
    (foldlList f z (elems l ++ (v ∷ elems r)) 
        ≡⟨ cong (foldlList f z) (sym (elems≡elems  x k v l r)) ⟩ 
    (foldlList f z (elems (node x k v l r)) ∎)))))) 

mutual 
    toAscList≡toAscList : {{Comparable K}} → ∀ x k → (v : A) → (l : Map K A) → (r : Map K A)
            → toAscList (node x k v l r) ≡ toAscList l ++ ((k , v) ∷ toAscList r) 
    toAscList≡toAscList x k v l r = 
        toAscList (node x k v l r) 
            ≡⟨ foldrWithKey≡foldr ((λ k v kvs → (k , v) ∷ kvs)) ((k , v) ∷ toAscList r) l ⟩ 
        (foldrList (λ p kvs → (Pair.fst p , Pair.snd p) ∷ kvs) ((k , v) ∷ toAscList r) (toAscList l) 
            ≡⟨ (foldrWithKey≡foldr (λ k v kvs → (k , v) ∷ kvs) [] r) under (λ y → foldrList _∷_ ((k , v) ∷ y) (toAscList l)) ⟩ 
        (foldrList _∷_ ((k , v) ∷ foldrList (λ p kvs → (Pair.fst p , Pair.snd p) ∷ kvs) [] (toAscList r)) (toAscList l) 
            ≡⟨ sym (foldrList-split _∷_ [] (toAscList l) ((k , v) ∷ toAscList r)) ⟩ 
        (foldrList _∷_ [] (toAscList l ++ ((k , v) ∷ toAscList r)) 
            ≡⟨ foldrIdent (toAscList l ++ ((k , v) ∷ toAscList r)) ⟩ 
        ((toAscList l ++ ((k , v) ∷ toAscList r)) ∎)))) 

    -- foldrWithKey f z == foldr (uncurry f) z . toAscList
    foldrWithKey≡foldr : {{Comparable K}} → (f : K → A → V → V) → (z : V) → (m : Map K A) 
        → foldrWithKey f z m ≡ foldrList (λ p x → f (Pair.fst p) (Pair.snd p) x) z (toAscList m)
    foldrWithKey≡foldr f z tip = refl
    foldrWithKey≡foldr f z (node x k v l r) = 
        foldrWithKey f z (node x k v l r) 
            ≡⟨ ((foldrWithKey≡foldr f z r) under (f k v)) under (λ y → foldrWithKey f y l) ⟩ 
        (foldrWithKey f (f k v (foldrList (λ p → f (Pair.fst p) (Pair.snd p)) z (toAscList r))) l 
            ≡⟨ foldrWithKey≡foldr f (f k v (foldrList (λ p → f (Pair.fst p) (Pair.snd p)) z (toAscList r))) l ⟩ 
        (foldrList (λ p → f (Pair.fst p) (Pair.snd p)) (f k v (foldrList (λ p → f (Pair.fst p) (Pair.snd p)) z (toAscList r))) (toAscList l) 
            ≡⟨ sym (foldrList-split ((λ p → f (Pair.fst p) (Pair.snd p))) z (toAscList l) ((k , v) ∷ toAscList r)) ⟩ 
        (foldrList (λ p → f (Pair.fst p) (Pair.snd p)) z (toAscList l ++ ((k , v) ∷ toAscList r)) 
            ≡⟨ sym ((toAscList≡toAscList  x k v l r) under (foldrList (λ p x → f (Pair.fst p) (Pair.snd p) x) z)) ⟩ 
        (foldrList (λ p x → f (Pair.fst p) (Pair.snd p) x) z (toAscList (node x k v l r)) ∎)))) 

-- foldlWithKey f z == foldl (\z' (kx, x) -> f z' kx x) z . toAscList
foldlWithKey≡foldl : {{Comparable K}} → (f : V → K → A → V) → (z : V) → (m : Map K A) 
    → foldlWithKey f z m ≡ foldlList (λ x p → f x (Pair.fst p) (Pair.snd p)) z (toAscList m)
foldlWithKey≡foldl f z tip = refl
foldlWithKey≡foldl f z (node x k v l r) = 
    foldlWithKey f z (node x k v l r) 
        ≡⟨ ((foldlWithKey≡foldl f z l) under (λ y → f y k v)) under (λ y → foldlWithKey f y r) ⟩ 
    ((foldlWithKey f (f (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z (toAscList l)) k v) r 
        ≡⟨ foldlWithKey≡foldl f (f (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z (toAscList l)) k v) r ⟩ 
    (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) (f (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z (toAscList l)) k v) (toAscList r) 
        ≡⟨ sym (foldlList-split (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z (toAscList l) ((k , v) ∷ toAscList r)) ⟩ 
    (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z (toAscList l ++ ((k , v) ∷ toAscList r)) 
    ≡⟨ sym ((toAscList≡toAscList x k v l r) under (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z)) ⟩ 
    (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z (toAscList (node x k v l r)) ∎))))) 

assoc-mappend : (xs ys zs : Nat)
         → mappend xs (mappend ys zs) ≡ mappend (mappend xs ys) zs 
assoc-mappend zero ys zs = refl
assoc-mappend (suc xs) ys zs = (assoc-mappend xs ys zs) under suc

mappend≡foldrMappend : (x : Map K Nat) → (y : Nat) → foldr mappend y x ≡ mappend (fold x) y  
mappend≡foldrMappend tip x = refl
mappend≡foldrMappend (node n k v l r) x = 
    foldr mappend x (node n k v l r) 
        ≡⟨ (mappend≡foldrMappend r x) under (λ y → foldr mappend (mappend v y) l) ⟩ 
    (foldr mappend (mappend v (mappend (fold r) x)) l 
        ≡⟨ mappend≡foldrMappend l (mappend v (mappend (fold r) x)) ⟩ 
    (mappend (fold l) (mappend v (mappend (fold r) x)) 
        ≡⟨ (assoc-mappend v (fold r) x) under (mappend (fold l)) ⟩ 
    (mappend (fold l) (mappend (mappend v (fold r)) x) 
        ≡⟨ assoc-mappend (fold l) (mappend v (fold r)) x ⟩ 
    (mappend (mappend (fold l) (mappend v (fold r))) x 
        ≡⟨ (sym (mappend≡foldrMappend l (mappend v (fold r)))) under (λ y → mappend y x) ⟩  
    (mappend (fold (node n k v l r)) x ∎)))))

mappendZeroY≡mappendYZero : (x : Nat) → mappend zero x ≡ mappend x zero
mappendZeroY≡mappendYZero zero = refl
mappendZeroY≡mappendYZero (suc n) = (mappendZeroY≡mappendYZero n) under suc 

-- foldMapWithKey f = fold . mapWithKey f
-- proof with Nat because that is an instance of monoid
foldMapWithKey≡foldMapWithKey : (f : K → V → Nat) → (m : Map K V) -- {{Monoid M}} → (f : K → V → M) → (m : Map K V) 
    → foldMapWithKey f m ≡ fold (mapWithKey f m)
foldMapWithKey≡foldMapWithKey f tip = refl
foldMapWithKey≡foldMapWithKey f (node 1 k v tip tip) = mappendZeroY≡mappendYZero (f k v)
foldMapWithKey≡foldMapWithKey f (node (suc (suc n)) k v l r) = 
    foldMapWithKey f (node (suc (suc n)) k v l r) 
        ≡⟨ ((foldMapWithKey≡foldMapWithKey f r) under (mappend (f k v))) under (mappend (foldMapWithKey f l)) ⟩ 
    (mappend (foldMapWithKey f l) (mappend (f k v) (fold (mapWithKey f r))) 
        ≡⟨ (foldMapWithKey≡foldMapWithKey f l) under (λ y → mappend y (mappend (f k v) (fold (mapWithKey f r)))) ⟩ 
    (mappend (fold (mapWithKey f l)) (mappend (f k v) (fold (mapWithKey f r)))
        ≡⟨ sym (mappend≡foldrMappend (mapWithKey f l) (mappend (f k v) (fold (mapWithKey f r)))) ⟩ 
    (fold (mapWithKey f (node (suc (suc n)) k v l r)) ∎)))
foldMapWithKey≡foldMapWithKey f _ = {! error  !}
      
-- %%%%%%%%%%%%% Strict folds %%%%%%%%%%%%%%%%%%%%%%

-- foldr' f z == foldr f z . elems  
foldr'≡foldrList-elems : {{Comparable K}} → (f : A → V → V) → (z : V) → (m : Map K A)
    → foldr' f z m ≡ foldrList f z (elems m)
foldr'≡foldrList-elems f z tip = refl
foldr'≡foldrList-elems f z (node x k v l r) = 
    foldr' f z (node x k v l r) 
       ≡⟨ ((foldr'≡foldrList-elems f z r) under (λ y → primForce y (f v))) under (λ y → foldr' f y l) ⟩ 
    (foldr' f (primForce (foldrList f z (foldr _∷_ [] r)) (f v)) l 
       ≡⟨ foldr'≡foldrList-elems f (primForce (foldrList f z (foldr _∷_ [] r)) (f v)) l ⟩ 
    (foldrList f (primForce (foldrList f z (foldr _∷_ [] r)) (f v)) (elems l) 
       ≡⟨ primForceLemma (foldrList f z (foldr _∷_ [] r)) (f v) under (λ y → foldrList f y (elems l)) ⟩ 
    (foldrList f (f v (foldrList f z (foldr _∷_ [] r))) (elems l)
        ≡⟨ sym (foldrList-split f z (elems l) (v ∷ elems r)) ⟩ 
    (foldrList f z (elems l ++ (v ∷ elems r)) 
       ≡⟨ (sym (elems≡elems  x k v l r)) under (foldrList f z) ⟩ 
    (foldrList f z (elems (node x k v l r)) ∎))))) 

-- foldl' f z == foldl f z . elems
foldl'≡foldlList-elems : {{Comparable K}} → (f : V → A → V) → (z : V) → (m : Map K A)
    → foldl' f z m ≡ foldlList f z (elems m) 
foldl'≡foldlList-elems f z tip = refl
foldl'≡foldlList-elems f z (node x k v l r) = 
    foldl' f z (node x k v l r) 
        ≡⟨ ((foldl'≡foldlList-elems f z l) under (λ y → primForce y (λ x₁ → f x₁ v))) under (λ y → foldl' f y r) ⟩ 
    ((foldl' f (primForce (foldlList f z (foldr _∷_ [] l)) (λ x₁ → f x₁ v)) r 
        ≡⟨ foldl'≡foldlList-elems f (primForce (foldlList f z (foldr _∷_ [] l)) (λ x₁ → f x₁ v)) r ⟩ 
    ((foldlList f (primForce (foldlList f z (foldr _∷_ [] l)) (λ x₁ → f x₁ v)) (elems r) 
        ≡⟨ primForceLemma (foldlList f z (foldr _∷_ [] l)) (λ x₁ → f x₁ v) under (λ y → foldlList f y (elems r)) ⟩ 
    (foldlList f (f (foldlList f z (foldr _∷_ [] l)) v) (elems r)
        ≡⟨ sym (foldlList-split f z (elems l) (v ∷ elems r)) ⟩ 
    (foldlList f z (elems l ++ (v ∷ elems r)) 
        ≡⟨ (sym (elems≡elems  x k v l r)) under (foldlList f z) ⟩ 
    (foldlList f z (elems (node x k v l r)) ∎)))))))

-- foldrWithKey' f z == foldr (uncurry f) z . toAscList
foldrWithKey'≡foldr : {{Comparable K}} → (f : K → A → V → V) → (z : V) → (m : Map K A) 
    → foldrWithKey' f z m ≡ foldrList (λ p x → f (Pair.fst p) (Pair.snd p) x) z (toAscList m)
foldrWithKey'≡foldr f z tip = refl
foldrWithKey'≡foldr f z (node x k v l r) = 
    foldrWithKey' f z (node x k v l r) 
        ≡⟨ ((foldrWithKey'≡foldr f z r) under (λ y → primForce y (f k v))) under (λ y → foldrWithKey' f y l) ⟩ 
    (foldrWithKey' f (primForce (foldrList (λ p → f (Pair.fst p) (Pair.snd p)) z (foldrWithKey (λ k₁ v₁ → _∷_ (k₁ , v₁)) [] r)) (f k v)) l 
        ≡⟨ foldrWithKey'≡foldr f (primForce (foldrList (λ p → f (Pair.fst p) (Pair.snd p)) z (foldrWithKey (λ k₁ v₁ → _∷_ (k₁ , v₁)) [] r)) (f k v)) l ⟩ 
    (foldrList (λ p → f (Pair.fst p) (Pair.snd p)) (primForce (foldrList (λ p → f (Pair.fst p) (Pair.snd p)) z (foldrWithKey (λ k₁ v₁ → _∷_ (k₁ , v₁)) [] r)) (f k v)) (toAscList l) 
        ≡⟨ primForceLemma (foldrList (λ p → f (Pair.fst p) (Pair.snd p)) z (foldrWithKey (λ k₁ v₁ → _∷_ (k₁ , v₁)) [] r)) (f k v) under (λ y → foldrList (λ p → f (Pair.fst p) (Pair.snd p)) y (toAscList l)) ⟩ 
    (foldrList (λ p → f (Pair.fst p) (Pair.snd p)) (f k v (foldrList (λ p → f (Pair.fst p) (Pair.snd p)) z (foldrWithKey (λ k₁ v₁ → _∷_ (k₁ , v₁)) [] r))) (toAscList l)    
        ≡⟨ sym (foldrList-split ((λ p → f (Pair.fst p) (Pair.snd p))) z (toAscList l) ((k , v) ∷ toAscList r)) ⟩ 
    (foldrList (λ p → f (Pair.fst p) (Pair.snd p)) z (toAscList l ++ ((k , v) ∷ toAscList r)) 
        ≡⟨ sym ((toAscList≡toAscList  x k v l r) under (foldrList (λ p x → f (Pair.fst p) (Pair.snd p) x) z)) ⟩ 
    (foldrList (λ p x → f (Pair.fst p) (Pair.snd p) x) z (toAscList (node x k v l r)) ∎))))) 

-- foldlWithKey' f z == foldl (\z' (kx, x) -> f z' kx x) z . toAscList
foldlWithKey'≡foldl : {{Comparable K}} → (f : V → K → A → V) → (z : V) → (m : Map K A) 
    → foldlWithKey' f z m ≡ foldlList (λ x p → f x (Pair.fst p) (Pair.snd p)) z (toAscList m)
foldlWithKey'≡foldl f z tip = refl
foldlWithKey'≡foldl f z (node x k v l r) = 
    foldlWithKey' f z (node x k v l r) 
        ≡⟨ ((foldlWithKey'≡foldl f z l) under (λ y → primForce y (λ x₁ → f x₁ k v))) under (λ y → foldlWithKey' f y r) ⟩ 
    ((foldlWithKey' f (primForce (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z (foldrWithKey (λ k₁ v₁ → _∷_ (k₁ , v₁)) [] l)) (λ x₁ → f x₁ k v)) r 
        ≡⟨ foldlWithKey'≡foldl f (primForce (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z (foldrWithKey (λ k₁ v₁ → _∷_ (k₁ , v₁)) [] l)) (λ x₁ → f x₁ k v)) r ⟩ 
    (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) (primForce (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z (foldrWithKey (λ k₁ v₁ → _∷_ (k₁ , v₁)) [] l)) (λ x₁ → f x₁ k v)) (toAscList r) 
        ≡⟨ primForceLemma (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z (foldrWithKey (λ k₁ v₁ → _∷_ (k₁ , v₁)) [] l)) (λ x₁ → f x₁ k v) under (λ y → foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) y (toAscList r)) ⟩ 
    (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) (f (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z (foldrWithKey (λ k₁ v₁ → _∷_ (k₁ , v₁)) [] l)) k v) (toAscList r)
        ≡⟨ sym (foldlList-split (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z (toAscList l) ((k , v) ∷ toAscList r)) ⟩ 
    (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z (toAscList l ++ ((k , v) ∷ toAscList r)) 
    ≡⟨ sym ((toAscList≡toAscList x k v l r) under (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z)) ⟩ 
    (foldlList (λ x₁ p → f x₁ (Pair.fst p) (Pair.snd p)) z (toAscList (node x k v l r)) ∎)))))) 