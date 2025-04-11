module BalancedMap.Balance where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Bool
open import Agda.Primitive

open import BalancedMap.Map

private variable
  ℓa ℓb : Level
  ℓA : Set ℓa
  K A B : Set
  m n p m₁ n₁ : Nat

balanceL : {{Comparable K}} → K → A → BalancedMap K A m → BalancedMap K A n → BalancedMap K A (suc (m + n))
balanceL k a tip tip = {! node  !}
balanceL k a tip r@(node rk ra rl rr {rp}) = {!   !}
balanceL k a l@(node lk la ll lr {lp}) tip = {!   !}
balanceL k a l@(node lk la ll lr {lp}) r@(node rk ra rl rr {rp}) = {!   !}