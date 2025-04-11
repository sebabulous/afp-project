module BalancedMap.Workspace where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

open import BalancedMap.Map

private variable
  K A : Set
  m n m₁ n₁ : Nat

thm56 : compare m (suc n) ≡ lt → m ≤ n
thm56 {zero} {zero} prf = look₂ refl
thm56 {zero} {suc n} prf = look₁ refl
thm56 {suc zero} {zero} ()
thm56 {suc (suc m)} {zero} ()
thm56 {suc m} {suc n} prf = thm25 (thm56 {m} {n} prf)

thm57 : compare m n ≡ eq → m ≤ n
thm57 {zero} {zero} prf = look₂ refl
thm57 {suc m} {suc n} prf = thm25 (thm57 {m} {n} prf)

thm58 : suc (suc n₁) ≤ 3 → (n₁ ≡ 0) ∨ (n₁ ≡ 1)
thm58 {zero} (look₁ refl) = or₁ refl
thm58 {suc zero} p = or₂ refl
thm58 {suc (suc n₁)} (look₁ ())
thm58 {suc (suc n₁)} (look₂ ())

thm61 : suc m ≤ n → m ≡ n → ⊥
thm61 {zero} {zero} (look₁ ()) p₂
thm61 {zero} {zero} (look₂ ()) p₂
thm61 {suc m} {suc n} p₁ p₂ = thm61 {m} {n} (thm13 p₁) (thm34 p₂)

thm60 : suc m ≤ n → compare m n ≡ eq → ⊥
thm60 {m} {n} p₁ p₂ = thm61 p₁ (thm14 p₂)

thm62 : suc m ≤ n → m ≤ n
thm62 {zero} {zero} (look₁ ())
thm62 {zero} {zero} (look₂ ())
thm62 {zero} {suc n} p = look₁ refl
thm62 {suc m} {zero} (look₁ ())
thm62 {suc m} {zero} (look₂ ())
thm62 {suc m} {suc n} p = thm25 (thm62 {m} {n} (thm13 p))

thm59 : Comparable.compare NatCmp (suc n) (suc (suc (suc (suc (suc ((suc m₁) + (suc n₁) + ((suc m₁) + (suc n₁) + ((suc m₁) + (suc n₁))))))))) ≡ lt → Comparable.compare NatCmp ((suc m₁) + (suc n₁)) (suc ((suc n) + ((suc n) + (suc n)))) ≡ eq → suc (suc m₁) ≤ suc (suc (suc ((suc n₁) + ((suc n₁) + (suc n₁))))) → suc (suc n₁) ≤ suc (suc (suc ((suc m₁) + ((suc m₁) + (suc m₁))))) → ((suc (m₁ + n₁ + n)) ≤ 1) ∨ ((suc (m₁ + n₁) ≤ (n + (n + n))) ∧ (n ≤ suc (suc (suc (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁))))))) → ⊥
thm59 {zero} {zero} {suc (suc zero)} p₁ p₂ p₃ p₄ (or₁ (look₁ ()))
thm59 {zero} {zero} {suc (suc zero)} p₁ p₂ p₃ p₄ (or₁ (look₂ ()))
thm59 {zero} {zero} {suc (suc zero)} p₁ p₂ p₃ p₄ (or₂ (look₁ () & x₁))
thm59 {zero} {zero} {suc (suc zero)} p₁ p₂ p₃ p₄ (or₂ (look₂ () & x₁))
thm59 {zero} {suc (suc zero)} {zero} p₁ p₂ p₃ p₄ (or₁ (look₁ ()))
thm59 {zero} {suc (suc zero)} {zero} p₁ p₂ p₃ p₄ (or₁ (look₂ ()))
thm59 {zero} {suc (suc zero)} {zero} p₁ p₂ p₃ p₄ (or₂ (look₁ () & x₁))
thm59 {zero} {suc (suc zero)} {zero} p₁ p₂ p₃ p₄ (or₂ (look₂ () & x₁))
thm59 {zero} {suc m₁} {suc n₁} p₁ p₂ p₃ p₄ (or₁ (look₁ ()))
thm59 {zero} {suc m₁} {suc n₁} p₁ p₂ p₃ p₄ (or₁ (look₂ ()))
thm59 {zero} {suc m₁} {suc n₁} p₁ p₂ p₃ p₄ (or₂ (look₁ () & x₁))
thm59 {zero} {suc m₁} {suc n₁} p₁ p₂ p₃ p₄ (or₂ (look₂ () & x₁))
thm59 {suc n} {zero} {suc (suc (suc (suc (suc n₁))))} p₁ p₂ p₃ (look₁ ()) p₅
thm59 {suc n} {zero} {suc (suc (suc (suc (suc n₁))))} p₁ p₂ p₃ (look₂ ()) p₅
thm59 {suc n} {suc (suc (suc (suc (suc m₁))))} {zero} p₁ p₂ (look₁ ()) p₄ p₅
thm59 {suc n} {suc (suc (suc (suc (suc m₁))))} {zero} p₁ p₂ (look₂ ()) p₄ p₅
thm59 {suc n} {suc m₁} {suc n₁} p₁ p₂ p₃ p₄ (or₁ (look₁ ()))
thm59 {suc n} {suc m₁} {suc n₁} p₁ p₂ p₃ p₄ (or₁ (look₂ ()))
thm59 {suc zero} {suc (suc m₁)} {suc zero} p₁ p₂ p₃ p₄ (or₂ (look₁ () & x₁))
thm59 {suc zero} {suc (suc m₁)} {suc zero} p₁ p₂ p₃ p₄ (or₂ (look₂ () & x₁))
thm59 {suc zero} {suc m₁} {suc (suc n₁)} p₁ p₂ p₃ p₄ (or₂ (look₁ () & x₁))
thm59 {suc zero} {suc m₁} {suc (suc n₁)} p₁ p₂ p₃ p₄ (or₂ (look₂ () & x₁))
thm59 {suc (suc zero)} {suc zero} {suc (suc (suc (suc (suc n₁))))} p₁ p₂ p₃ p₄ (or₂ (look₁ () & x₁))
thm59 {suc (suc zero)} {suc zero} {suc (suc (suc (suc (suc n₁))))} p₁ p₂ p₃ p₄ (or₂ (look₂ () & x₁))
thm59 {suc (suc zero)} {suc (suc zero)} {suc (suc (suc (suc n₁)))} p₁ p₂ p₃ p₄ (or₂ (look₁ () & x₁))
thm59 {suc (suc zero)} {suc (suc zero)} {suc (suc (suc (suc n₁)))} p₁ p₂ p₃ p₄ (or₂ (look₂ () & x₁))
thm59 {suc (suc zero)} {suc (suc (suc zero))} {suc (suc (suc n₁))} p₁ p₂ p₃ p₄ (or₂ (look₁ () & x₁))
thm59 {suc (suc zero)} {suc (suc (suc zero))} {suc (suc (suc n₁))} p₁ p₂ p₃ p₄ (or₂ (look₂ () & x₁))
thm59 {suc (suc zero)} {suc (suc (suc (suc zero)))} {suc (suc n₁)} p₁ p₂ p₃ p₄ (or₂ (look₁ () & x₁))
thm59 {suc (suc zero)} {suc (suc (suc (suc zero)))} {suc (suc n₁)} p₁ p₂ p₃ p₄ (or₂ (look₂ () & x₁))
thm59 {suc (suc zero)} {suc (suc (suc (suc (suc m₁))))} {suc n₁} p₁ p₂ p₃ p₄ (or₂ (look₁ () & x₁))
thm59 {suc (suc zero)} {suc (suc (suc (suc (suc m₁))))} {suc n₁} p₁ p₂ p₃ p₄ (or₂ (look₂ () & x₁))
thm59 {suc (suc (suc zero))} {suc m₁} {suc n₁} p₁ p₂ p₃ p₄ (or₂ (x & x₁)) = thm60 {m₁ + n₁} {9} (thm62 (thm62 x)) p₂
thm59 {suc (suc (suc (suc zero)))} {suc m₁} {suc n₁} p₁ p₂ p₃ p₄ (or₂ (x & x₁)) = thm60 {m₁ + n₁} {12} (thm62 (thm62 x)) p₂
thm59 {suc (suc (suc (suc (suc zero))))} {suc m₁} {suc n₁} p₁ p₂ p₃ p₄ (or₂ (x & x₁)) = thm60 {m₁ + n₁} {15} (thm62 (thm62 x)) p₂
thm59 {suc (suc (suc (suc (suc (suc n)))))} {suc m₁} {suc n₁} p₁ p₂ p₃ p₄ (or₂ (x & x₁)) = {!   !}

thm63 : compare n (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁))))))))))))) ≡ eq → compare (m₁ + n₁) (suc (suc (n + (n + n)))) ≡ eq → ⊥
thm63 {suc n} {zero} {suc n₁} p₁ p₂ with compare n n₁
thm63 {suc n} {zero} {suc n₁} p₁ p₂ | res = {!   !}
thm63 {suc n} {suc m₁} {zero} p₁ p₂ = {!   !}
thm63 {suc n} {suc m₁} {suc n₁} p₁ p₂ = {!   !}

thm55 : {m₁ n₁ : Nat} → n ≤ (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁))) → (m₁ + n₁) ≤ (n + (n + n)) → (m₁ ≤ (n₁ + (n₁ + n₁))) ∧ (n₁ ≤ (m₁ + (m₁ + m₁))) → (m ≡ (m₁ + n₁)) → ((suc (m₁ + n₁ + n)) ≤ 1) ∨ ((suc (m₁ + n₁) ≤ (n + (n + n))) ∧ (n ≤ suc (suc (suc (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁)))))))
thm55 {zero} {zero} {zero} {zero} p₁ p₂ (p₃ & p₄) p₅ = or₁ (look₂ refl)
thm55 {zero} {suc m} {zero} {suc n₁} p₁ p₂ (p₃ & look₁ ()) p₅
thm55 {zero} {suc m} {zero} {suc n₁} p₁ p₂ (p₃ & look₂ ()) p₅
thm55 {zero} {suc m} {suc m₁} {zero} p₁ p₂ (look₁ () & p₄) p₅
thm55 {zero} {suc m} {suc m₁} {zero} p₁ p₂ (look₂ () & p₄) p₅
thm55 {zero} {suc m} {suc m₁} {suc n₁} p₁ (look₁ ()) (p₃ & p₄) p₅
thm55 {zero} {suc m} {suc m₁} {suc n₁} p₁ (look₂ ()) (p₃ & p₄) p₅
thm55 {suc n} {zero} {zero} {zero} (look₁ ()) p₂ (p₃ & p₄) p₅
thm55 {suc n} {zero} {zero} {zero} (look₂ ()) p₂ (p₃ & p₄) p₅
thm55 {suc n} {suc m} {zero} {suc n₁} p₁ p₂ (p₃ & look₁ ()) p₅
thm55 {suc n} {suc m} {zero} {suc n₁} p₁ p₂ (p₃ & look₂ ()) p₅
thm55 {suc n} {suc m} {suc m₁} {zero} p₁ p₂ (look₁ () & p₄) p₅
thm55 {suc n} {suc m} {suc m₁} {zero} p₁ p₂ (look₂ () & p₄) p₅
thm55 {suc n} {suc m} {suc m₁} {suc n₁} (look₁ p₁) (look₁ p₂) (look₁ p₃ & look₁ p₄) refl = or₂ (thm25 (thm25 (thm25 (thm56 {m₁ + n₁} {n + (n + n)} p₂))) & thm25 (thm10 (thm10 (thm10 (thm30 {n} {suc (suc (suc (suc (suc (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁)))))))} p₁)))))
thm55 {suc n} {suc m} {suc m₁} {suc n₁} (look₁ p₁) (look₁ p₂) (look₁ p₃ & look₂ p₄) refl = or₂ (thm25 (thm25 (thm25 (thm56 {m₁ + n₁} {n + (n + n)} p₂))) & thm25 (thm10 (thm10 (thm10 (thm30 {n} {suc (suc (suc (suc (suc (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁)))))))} p₁)))))
thm55 {suc n} {suc m} {suc m₁} {suc n₁} (look₁ p₁) (look₁ p₂) (look₂ p₃ & look₁ p₄) refl = or₂ (thm25 (thm25 (thm25 (thm56 {m₁ + n₁} {n + (n + n)} p₂))) & thm25 (thm10 (thm10 (thm10 (thm30 {n} {suc (suc (suc (suc (suc (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁)))))))} p₁)))))
thm55 {suc n} {suc m} {suc m₁} {suc n₁} (look₁ p₁) (look₁ p₂) (look₂ p₃ & look₂ p₄) refl = or₂ (thm25 (thm25 (thm25 (thm56 {m₁ + n₁} {n + (n + n)} p₂))) & thm25 (thm10 (thm10 (thm10 (thm30 {n} {suc (suc (suc (suc (suc (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁)))))))} p₁)))))
thm55 {suc n} {suc m} {suc m₁} {suc n₁} (look₁ p₁) (look₂ p₂) (p₃ & p₄) refl = {!   !}
thm55 {suc n} {suc m} {suc m₁} {suc n₁} (look₂ p₁) (look₁ p₂) (look₁ p₃ & look₁ p₄) refl = or₂ (thm25 (thm25 (thm25 (thm56 {m₁ + n₁} {n + (n + n)} p₂))) & thm25 (thm10 (thm10 (thm10 (thm57 {n} {suc (suc (suc (suc (suc (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁)))))))} p₁)))))
thm55 {suc n} {suc m} {suc m₁} {suc n₁} (look₂ p₁) (look₁ p₂) (look₁ p₃ & look₂ p₄) refl = or₂ (thm25 (thm25 (thm25 (thm56 {m₁ + n₁} {n + (n + n)} p₂))) & thm25 (thm10 (thm10 (thm10 (thm57 {n} {suc (suc (suc (suc (suc (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁)))))))} p₁)))))
thm55 {suc n} {suc m} {suc m₁} {suc n₁} (look₂ p₁) (look₁ p₂) (look₂ p₃ & look₁ p₄) refl = or₂ (thm25 (thm25 (thm25 (thm56 {m₁ + n₁} {n + (n + n)} p₂))) & thm25 (thm10 (thm10 (thm10 (thm57 {n} {suc (suc (suc (suc (suc (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁)))))))} p₁)))))
thm55 {suc n} {suc m} {suc m₁} {suc n₁} (look₂ p₁) (look₁ p₂) (look₂ p₃ & look₂ p₄) refl = or₂ (thm25 (thm25 (thm25 (thm56 {m₁ + n₁} {n + (n + n)} p₂))) & thm25 (thm10 (thm10 (thm10 (thm57 {n} {suc (suc (suc (suc (suc (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁)))))))} p₁)))))
thm55 {suc (suc n)} {suc m} {suc zero} {suc (suc n₁)} (look₂ p₁) (look₂ p₂) (p₃ & p₄) refl with thm58 p₄
thm55 {suc (suc n)} {suc .2} {suc zero} {suc (suc zero)} (look₂ p₁) (look₂ ()) (p₃ & p₄) refl | or₁ p₄'
thm55 {suc (suc n)} {suc .(suc (suc (suc n₁)))} {suc zero} {suc (suc (suc n₁))} (look₂ p₁) (look₂ p₂) (p₃ & p₄) refl | or₁ ()
thm55 {suc (suc n)} {suc .3} {suc zero} {suc (suc (suc zero))} (look₂ p₁) (look₂ ()) (p₃ & p₄) refl | or₂ p₄'
thm55 {suc (suc n)} {suc .(suc (suc (suc (suc n₁))))} {suc zero} {suc (suc (suc (suc n₁)))} (look₂ p₁) (look₂ p₂) (p₃ & p₄) refl | or₂ ()
thm55 {suc (suc n)} {suc m} {suc (suc m₁)} {suc zero} (look₂ p₁) (look₂ p₂) (p₃ & p₄) refl with thm58 p₃
thm55 {suc (suc n)} {suc .2} {suc (suc zero)} {suc zero} (look₂ p₁) (look₂ ()) (p₃ & p₄) refl | or₁ p₃'
thm55 {suc (suc n)} {suc .(suc (suc (suc m₁)))} {suc (suc (suc m₁))} {suc zero} (look₂ p₁) (look₂ p₂) (p₃ & p₄) refl | or₁ ()
thm55 {suc (suc n)} {suc .3} {suc (suc (suc zero))} {suc zero} (look₂ p₁) (look₂ ()) (p₃ & p₄) refl | or₂ p₃'
thm55 {suc (suc n)} {suc .(suc (suc (suc (suc m₁))))} {suc (suc (suc (suc m₁)))} {suc zero} (look₂ p₁) (look₂ p₂) (look₁ () & p₄) refl | or₂ p₃'
thm55 {suc (suc n)} {suc .(suc (suc (suc (suc m₁))))} {suc (suc (suc (suc m₁)))} {suc zero} (look₂ p₁) (look₂ p₂) (look₂ () & p₄) refl | or₂ p₃'
thm55 {suc (suc n)} {suc m} {suc (suc m₁)} {suc (suc n₁)} (look₂ p₁) (look₂ p₂) (p₃ & p₄) refl = or₂ ({!   !} & {!   !}) 