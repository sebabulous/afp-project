open import Agda.Builtin.Nat

--data Map (K : Set) (A : Set) (N : Nat) : Set where
--data Map (K : Set) (A : Set) : Nat → Set where
--data Map (K : Set) (A : Set) (N : Nat) (M : Nat) : Nat → Set where
--  tip : Map K A N M 0
--node : {n : Nat} → K → A → Map K A ((n - 1) / 2) → Map K A ((n - 1) - ((n - 1) / 2)) → Map K A n
--node : {n : Nat}{m : Nat} → K → A → Map K A n → Map K A m → Map K A (n + m + 1)
--  node : {n : Nat}{m : Nat} → K → A → Map K A N M n → Map K A N M m → Map K A N M (n + m + 1)

data Ord : Set where
  gt : Ord
  lt : Ord
  eq : Ord

record Comparable (A : Set) : Set where
  field
    compare : A → A → Ord

open Comparable {{...}} public

instance
    NatCmp : Comparable Nat
    compare {{ NatCmp }} x y = gt -- TODO

data Map (K : Set) (V : Set) : Set where -- TODO : restrict K to comparable (maybe only for insert function etc?)
    node : Nat → K → V → Map K V → Map K V → Map K V
    -- Node Int K V (Map K V) (Map K V)
    tip : Map K V
    -- Tip

{-
insert :: Ord k => k -> a -> Map k a -> Map k a
insert kx x = kx `seq` go
  where
    go Tip = singleton kx x
    go (Bin sz ky y l r) =
        case compare kx ky of
            LT -> balance ky y (go l) r
            GT -> balance ky y l (go r)
            EQ -> Bin sz kx x l r
-}

size : {K : Set}{V : Set} → Map K V → Nat
size tip = 0
size (node s _ _ _ _) = s

bogus : {K : Set}{V : Set} → K → V → Map K V
bogus k v = node 1000 k v tip tip

{-
test : {n : Nat}{K : Set}{A : Set} → Map K A n → Nat
test (node _ _ _ _ n) = n
test tip          = 0
-}

--Vec Nat zero
--Vec Nat (succ _)

data Vec (E : Set) : Nat → Set where
    [] : Vec E 0
    _::_ : {n : Nat} → E → Vec E n → Vec E (suc n)

--size : {E : Set} → Vec E zero → Nat
--size _ = 0

--size : {n : Nat}{E : Set} → Vec E n → Nat
--size [] = 0
--size (_ :: xs) = suc (size xs)

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B
infixr 4 _,_

data VecMap (A : Set) (B : Set) : Nat → Set where
  [] : VecMap A B 0
  _::_ : {n : Nat} → (A × B) → VecMap A B n → VecMap A B (suc n)