open import Agda.Builtin.Nat

data Map (K : Set) (A : Set) : Set where
  tip : Map K A
  node : Nat → K → A → Map K A → Map K A → Map K A


data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B
infixr 4 _,_

data VecMap (A : Set) (B : Set) : Nat → Set where
  [] : VecMap A B 0
  _::_ : {n : Nat} → (A × B) → VecMap A B n → VecMap A B (suc n)