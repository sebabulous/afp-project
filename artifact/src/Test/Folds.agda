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

_++_ : (l : List A) → (r : List A) → List A
[] ++ r = r
(x ∷ l) ++ r = x ∷ l ++ r

[]++≡id : (as : List A) → [] ++ as ≡ as
[]++≡id as = refl

id≡++[] : (as : List A) → as ++ [] ≡ as
id≡++[] [] = refl
id≡++[] (x ∷ as) = cong (x ∷_) (id≡++[] as)

mutual
    elems≡elems1 : {{Comparable K}} → (v : A) → (l : Map K A) → (r : Map K A)
        → foldrList _∷_ (v ∷ elems r) (elems l) ≡ foldrList _∷_ (v ∷ (foldrList _∷_ [] (elems r))) (elems l)
    elems≡elems1 v l r =  cong (λ y → foldrList _∷_ (v ∷ y) (elems l)) (foldr≡foldrList-elems _∷_ [] r)

    foldrIdent : (as : List A)
        → foldrList _∷_ [] as ≡ as
    foldrIdent [] = refl
    foldrIdent (x ∷ as) = cong (x ∷_) (foldrIdent as)

    elems≡elems : {{Comparable K}} → ∀ x k → (v : A) → (l : Map K A) → (r : Map K A)
        → elems (node x k v l r) ≡ elems l ++ (v ∷ elems r)
    elems≡elems x k v l r = trans
        (
            trans
            (
                trans
                (foldr≡foldrList-elems _∷_ (v ∷ elems r) l)
                (elems≡elems1 v l r)
            )
            (
                sym (foldrList-split _∷_ [] (elems l) (v ∷ elems r))
            )
        )
        (foldrIdent (elems l ++ (v ∷ elems r)))

    foldrList-v-r : (f : A → V → V) → (z : V) → (v : A) → (r : Map K A)
        → foldrList f z (v ∷ elems r) ≡ f v (foldrList f z (elems r))
    foldrList-v-r f z v r = refl

    foldrList-split : (f : A → V → V) → (z : V) → (ls : List A) → (rs : List A)
        → foldrList f z (ls ++ rs) ≡ foldrList f (foldrList f z rs) ls
    foldrList-split f z [] rs = refl
    foldrList-split f z (x ∷ ls) rs = cong (f x) (foldrList-split f z ls rs)

    elemsthing : {{Comparable K}} → (f : A → V → V) → (z : V) → ∀ x k → (v : A) → (l : Map K A) → (r : Map K A)
        → foldrList f z (elems (node x k v l r)) ≡ foldrList f (f v (foldrList f z (elems r))) (elems l)
    elemsthing f z x k v l r = trans
        (cong (foldrList f z) (elems≡elems  x k v l r)) 
        (foldrList-split f z (elems l) (v ∷ elems r))

    foldr≡foldrList-elems : {{Comparable K}} → (f : A → V → V) → (z : V) → (m : Map K A)
        → foldr f z m ≡ foldrList f z (elems m)
    foldr≡foldrList-elems f z tip = refl
    foldr≡foldrList-elems f z (node x k v l r) = trans
        (
            trans
            (
                cong (λ y → foldr f y l)
                (cong (f v) (foldr≡foldrList-elems f z r))
            )
            (
                foldr≡foldrList-elems f (f v (foldrList f z (elems r))) l
            )
        )
        (sym (elemsthing f z x k v l r))


-- elems (node x k v l r)
-- foldr _∷_ (v ∷ foldr _∷_ [] r) l
-- (foldr _∷_ [] l) ++ (v ∷ foldr _∷_ [] r)
-- (foldr _∷_ [] l) ++ (v ∷ []) ++ (foldr _∷_ [] r)
-- elems l ++ (v ∷ []) ++ elems r

--                foldr  f  ( f  v (foldr  f   z r)) l
-- ≡
-- foldrList f z (foldr _∷_ (_∷_ v  foldr _∷_ [] r)  l  )
-- foldrList f z (foldr _∷_ (_∷_ v  foldr _∷_ [] r)  (l ∷ ls)  )
-- f l (foldrList f z (foldr _∷_ (_∷_ v  foldr _∷_ [] r) ls))
-- 1
-- foldrList f z ((foldr _∷_ [] l) ++ (v ∷ foldr _∷_ [] r))
-- foldrList f z ((foldr _∷_ [] l) ++ (v ∷ []) ++ (foldr _∷_ [] r))
-- foldrList f z (elems l ++ (v ∷ []) ++ elems r)
-- foldrList f (foldrList f (foldrList f z (elems r)) (v ∷ [])) (elems l)


-- foldrList f z (foldr _∷_ (v ∷ foldr _∷_ [] r) l)
-- foldrList f z (foldr _∷_ (v ∷ elems r) l)
-- foldrList f z (foldrList _∷_ (v ∷ elems r) (elems l))
-- foldrList f z ((foldrList _∷_ [] (elems l)) ++ (v ∷ elems r))
-- foldrList f z ((elems l) ++ (v ∷ elems r))


-- foldrList f z (foldr _∷_ (v ∷ foldr _∷_ [] r) l)
-- f (elems l) (foldrList f z (v ∷ (elems r)))
-- f (elems l) (foldrList f z (v ∷ (elems r)))                 
--      Z = (foldrList f z (v ∷ (elems r)))
-- f (elems l) Z
-- f (elems l) (foldrList f Z [])
-- foldrList f Z (elems l ∷ [])
-- foldrList f (foldrList f z (v ∷ (elems r))) (elems l)
-- foldrList f (f v (foldrList f z (elems r))) (elems l)



-- foldrList f z (foldr _∷_ ( x :: xs) l)
-- foldrList f z (x ∷ (foldr _∷_ xs l))
-- f x (foldrList f z (foldr _∷_ xs l))
-- f x (foldrList f (foldrList f z l) xs)   Induction
-- foldrList f (foldrList f z l) (x :: xs)


-- elems m ≡ elems l ++ (v ∷ []) ++ elems r

{-
foldr≡foldrList-elems : {{Comparable K}} → (f : A → V → V) → (z : V) → (m : Map K A)
    → foldr f z m ≡ foldrList f z (elems m)
foldr≡foldrList-elems f z tip = refl
foldr≡foldrList-elems f z (node x k v tip r) = {!   !}
foldr≡foldrList-elems f z (node x k v (node x₁ x₂ x₃ l l₁) tip) = {!   !}
foldr≡foldrList-elems f z (node x k v (node x₁ x₂ x₃ l l₁) (node x₄ x₅ x₆ r r₁)) = {!   !}
-}

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
-- testFoldr f z (node x k v l r) =  ({! testFoldr f (f v (foldr f z r)) l !}) 
testFoldr f z (node x k v l r) = trans (testFoldr f (f v (foldr f z r)) l ) 
     (trans (cong (λ y → foldrList f (f v y) (elems l)) (testFoldr f z r))  
     ({!   !}))   


{-

_++_ : (l : List A) → (r : List A) → List A
[] ++ r = r
(x ∷ l) ++ r = x ∷ l ++ r


[]++≡id : (as : List A) → [] ++ as ≡ as
[]++≡id as = refl

id≡++[] : (as : List A) → as ++ [] ≡ as
id≡++[] [] = refl
id≡++[] (x ∷ as) = cong (x ∷_) (id≡++[] as)

cons≡++ : (a : A) → (as : List A) → a ∷ as ≡ a ∷ [] ++ as
cons≡++ a as = refl

foldr≡elems : {{Comparable K}} → (m : Map K A)
    → foldr _∷_ [] m ≡ elems m
foldr≡elems m = refl

foldr∷l : {{Comparable K}} → (a : A) → (as : List A) → (m : Map K A)
    → foldr _∷_ (a ∷ as) m ≡ foldr _∷_ (a ∷ [] ++ as) m
foldr∷l a as m = refl

foldr∷r : {{Comparable K}} → (a : A) → (as : List A) → (m : Map K A)
    → foldr _∷_ [] m ++ (a ∷ as) ≡ foldr _∷_ [] m ++ (a ∷ [] ++ as)
foldr∷r a as m = refl

foldr∷[] : {{Comparable K}} → (a : A) → (as : List A) → (m : Map K A)
    → foldr _∷_ (a ∷ []) m ++ as ≡ foldr _∷_ [] m ++ (a ∷ as)
foldr∷[] a [] m = {!   !}
foldr∷[] a (x ∷ as) m = {!   !}

foldr≡++ : {{Comparable K}} → (ls : List A) → (rs : List A) → (m : Map K A)
    → foldr _∷_ (ls ++ rs) m ≡ (foldr _∷_ ls m) ++ rs
foldr≡++ [] [] m = sym (id≡++[] (foldr _∷_ [] m))
foldr≡++ [] (x ∷ rs) m = {!  (foldr≡++ (x ∷ []) rs m)  !}
foldr≡++ (x ∷ ls) rs m = {!   !}
-}

{-
foldr≡++ : {{Comparable K}} → (as : List A) → (m : Map K A)
    → foldr _∷_ as m ≡ (foldr _∷_ [] m) ++ as
foldr≡++ [] m = {!   !}
foldr≡++ (x ∷ as) tip = refl
foldr≡++ (x ∷ as) (node x₁ k v l r) = {! 
    cong (λ y → y ++ (x ∷ as))
    (
        trans 
        ((foldr≡++ (v ∷ foldr _∷_ [] r) l)) 
        (sym (foldr≡++ ((v ∷ foldr _∷_ [] r)) l))
    )
    !} 
-- (foldr≡++ (v ∷ foldr _∷_ [] r) l)
-- cong (λ y → y ++ (x ∷ as))



foldr≡foldrList-foldr : {{Comparable K}} → (f : A → V → V) → (z : V) → (m : Map K A)
    → foldr f z m ≡ foldrList f z (foldr _∷_ [] m)
foldr≡foldrList-foldr f z tip = refl
foldr≡foldrList-foldr f z (node x k v l r) = {!   !}


foldr≡foldrList-elems : {{Comparable K}} → (f : A → V → V) → (z : V) → (m : Map K A)
    → foldr f z m ≡ foldrList f z (elems m)
foldr≡foldrList-elems f z m = {! cong (λ y → foldrList f z y) (sym (foldr≡elems m))  !}


-- elems = ls ++ (v ∷ []) ++ rs

-}

{-
elems-node≡foldr : {{Comparable K}} → ∀ x k → (v : A) → (l : Map K A) → (r : Map K A)
    → elems (node x k v l r) ≡ foldr _∷_ (v ∷ foldr _∷_ [] r) l
elems-node≡foldr _ _ v l r = refl


foldr≡foldr-foldrList : {{Comparable K}} → (f : A → V → V) → (z : V) → ∀ x k → (v : A) → (l : Map K A) → (r : Map K A)
    → foldr f (f v (foldr f z r)) l ≡ foldrList f z (foldr _∷_ (v ∷ foldr _∷_ [] r) l)
foldr≡foldr-foldrList f z x k v tip tip = refl
foldr≡foldr-foldrList f z x k v (node x₁ x₂ x₃ l l₁) tip = {!   !}
foldr≡foldr-foldrList f z x k v l (node x₁ x₂ x₃ r r₁) = {!   !}


foldr≡foldrList-elems : {{Comparable K}} → (f : A → V → V) → (z : V) → (m : Map K A)
    → foldr f z m ≡ foldrList f z (elems m)
foldr≡foldrList-elems f z tip = refl
foldr≡foldrList-elems f z (node x k v l r) = sym (trans (cong (λ y → foldrList f z y) (elems-node≡foldr x k v l r)) (sym (foldr≡foldr-foldrList f z x k v l r)))
-}

{-
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
-}   