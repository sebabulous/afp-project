module SizedMap.Test.Balance where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

open import SizedMap.Map
open import SizedMap.Balance
open import SizedMap.Query
open import Helpers.Comparable
open import Helpers.Pair
open import SizedMap.Test.Valid

private variable
  K A : Set
  m n : Nat

-- balance : {{Comparable K}} → K → A → Map K A m → Map K A n → Map K A (suc (m + n))
-- balance k a tip tip = node k a tip tip
-- balance k a tip (node rk ra rl rr) = {!   !}
-- balance k a (node lk la ll lr) tip = {!   !}
-- balance k a (node lk la ll lr) (node rk ra rl rr) = {!   !}

balanceWorks : {{_ : Comparable K}} → {k : K} → {a : A} → {l : Map K A m} → {r : Map K A n} → {balanced l ≡ true} → {balanced r ≡ true} → balanced (balance k a l r) ≡ true
balanceWorks {K} {A} {m} {n} ⦃ x ⦄ {k} {a} {tip} {tip} = refl
balanceWorks {K} {A} {m} {n} ⦃ x ⦄ {k} {a} {tip} {node rk ra tip rr} {prfl} {prfr} with rr
balanceWorks {K} {A} {m} {n} ⦃ x ⦄ {k} {a} {tip} {node rk ra tip rr} {prfl} {prfr} | tip = refl
-- balanceWorks {K} {A} {m} {n} ⦃ x ⦄ {k} {a} {tip} {node rk ra tip rr} {prfl} {prfr} | (node rrk rra rrl rrr) = {!   !}
balanceWorks {K} {A} {m} {n} ⦃ x ⦄ {k} {a} {tip} {node rk ra tip rr} {prfl} {prfr} | (node rrk rra rrl rrr) with (compare (size rr) delta , compare 1 (delta * size rr))
balanceWorks {K} {A} {m} {n} ⦃ x ⦄ {k} {a} {tip} {node rk ra tip rr} {prfl} {prfr} | (node rrk rra rrl rrr) | (gt , _) with (size rrl) < ratio * (size rrr)
balanceWorks {K} {A} {m} {n} ⦃ x ⦄ {k} {a} {tip} {node rk ra tip rr} {prfl} {prfr} | (node rrk rra rrl rrr) | (gt , _) | true = {!   !}
balanceWorks {K} {A} {m} {n} ⦃ x ⦄ {k} {a} {tip} {node rk ra tip rr} {prfl} {prfr} | (node rrk rra rrl rrr) | (gt , _) | false = {!   !}
balanceWorks {K} {A} {m} {n} ⦃ x ⦄ {k} {a} {tip} {node rk ra tip rr} {prfl} {prfr} | (node rrk rra rrl rrr) | (_ , gt) = {!   !}
balanceWorks {K} {A} {m} {n} ⦃ x ⦄ {k} {a} {tip} {node rk ra tip rr} {prfl} {prfr} | (node rrk rra rrl rrr) | _ = {!   !}
balanceWorks {K} {A} {m} {n} ⦃ x ⦄ {k} {a} {tip} {node rk ra (node rlk rla rll rlr) tip} = {!   !}
balanceWorks {K} {A} {m} {n} ⦃ x ⦄ {k} {a} {tip} {node rk ra (node rlk rla rll rlr) (node rrk rra rrl rrr)} = {!   !}
balanceWorks {K} {A} {m} {n} ⦃ x ⦄ {k} {a} {node lk la ll lr} {tip} = {!   !}
balanceWorks {K} {A} {m} {n} ⦃ x ⦄ {k} {a} {node lk la ll lr} {node rk ra rl rr} = {!   !}