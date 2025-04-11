module BalancedMap.Map where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Bool
open import Agda.Primitive

private variable
  ℓa ℓb : Level
  ℓA : Set ℓa
  K A B : Set
  m n p m₁ n₁ : Nat

data ⊥ : Set where

cong : (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

+zero : n + zero ≡ n
+zero {zero} = refl
+zero {suc n} = cong suc +zero

+zero-2 : n + zero + m ≡ n + m
+zero-2 {zero} {zero} = refl
+zero-2 {zero} {suc m} = refl
+zero-2 {suc n} {zero} = cong suc (+zero-2 {n} {zero})
+zero-2 {suc n} {suc m} = cong suc (+zero-2 {n} {suc m})

transport
  : A ≡ B
  → A → B
transport refl a = a

_∵_
  : A
  → A ≡ B
  →     B
a ∵ pf = transport pf a

sym : {x y : ℓA} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {p q r : ℓA} → p ≡ q → q ≡ r → p ≡ r
trans refl y=z = y=z

_≡⟨_⟩_ : ∀ p {q r : ℓA} → p ≡ q → q ≡ r → p ≡ r
x ≡⟨ x=y ⟩ y=z = trans x=y y=z

data Pair A B : Set where
  _,_ : A → B → Pair A B

data Ord : Set where
  eq : Ord
  lt : Ord
  gt : Ord

record Comparable (A : Set) : Set where
  field
    compare : A → A → Ord

    eq⇒eq : ∀ k k' → compare k k' ≡ eq → k ≡ k'

open Comparable {{...}} public

instance
  NatCmp : Comparable Nat
  compare {{ NatCmp }} zero zero = eq
  compare {{ NatCmp }} zero (suc _) = lt
  compare {{ NatCmp }} (suc _) zero = gt
  compare {{ NatCmp }} (suc x) (suc y) = compare x y

  eq⇒eq ⦃ NatCmp ⦄ zero zero p = refl
  eq⇒eq ⦃ NatCmp ⦄ (suc k) (suc k') p = cong suc (eq⇒eq k k' p)

data _≤_ {{_ : Comparable K}} (k : K) (k' : K) : Set where
  look₁ : compare k k' ≡ lt → k ≤ k'
  look₂ : compare k k' ≡ eq → k ≤ k'


δ : Nat
δ = 3

ratio : Nat
ratio = 2

data _∨_ A B : Set where
  or₁ : A → A ∨ B
  or₂ : B → A ∨ B

data _∧_ A B : Set where
  _&_ : A → B → A ∧ B

thm1 : (m + n) ≤ zero → (m ≡ zero) ∧ (n ≡ zero)
thm1 {zero} {zero} prf = refl & refl
thm1 {zero} {suc n} (look₁ ())
thm1 {zero} {suc n} (look₂ ())
thm1 {suc m} {zero} (look₁ ())
thm1 {suc m} {zero} (look₂ ())
thm1 {suc m} {suc n} (look₁ ())
thm1 {suc m} {suc n} (look₂ ())

thm3 : (m + (suc n)) ≡ 0 → ⊥
thm3 {zero} {zero} ()
thm3 {zero} {suc n} ()
thm3 {suc m} {zero} ()
thm3 {suc m} {suc n} ()

thm4 : suc m ≤ 0 → ⊥
thm4 {zero} (look₁ ())
thm4 {zero} (look₂ ())
thm4 {suc m} (look₁ ())
thm4 {suc m} (look₂ ())

thm5 : compare (m + (suc n)) 0 ≡ lt → ⊥
thm5 {zero} ()

thm6 : compare (m + (suc n)) 0 ≡ eq → ⊥
thm6 {zero} ()

thm2 : (m + n) ≤ 1 → (m ≡ zero) ∨ (n ≡ zero)
thm2 {zero} {zero} (look₁ x) = or₁ refl
thm2 {zero} {suc n} (look₁ x) = or₁ refl
thm2 {zero} {suc n} (look₂ x) = or₁ refl
thm2 {suc m} {zero} (look₁ x) = or₂ refl
thm2 {suc m} {zero} (look₂ x) = or₂ refl
thm2 {suc m} {suc n} (look₁ ())
thm2 {suc m} {suc n} (look₂ ())

thm13 : suc n ≤ suc m → n ≤ m
thm13 {zero} {zero} (look₂ prf) = look₂ refl
thm13 {zero} {suc m} (look₁ prf) = look₁ refl
thm13 {suc n} {suc m} (look₁ prf) = look₁ prf
thm13 {suc n} {suc m} (look₂ prf) = look₂ prf

thm15 : {r : Ord} → compare (suc n) (suc m) ≡ r → compare n m ≡ r
thm15 {zero} {zero} {eq} prf = refl
thm15 {zero} {suc n} {lt} prf = refl
thm15 {suc m} {zero} {gt} prf = refl
thm15 {suc m} {suc n} {eq} prf = prf
thm15 {suc m} {suc n} {lt} prf = prf
thm15 {suc m} {suc n} {gt} prf = prf

thm20 : compare n m ≡ lt → (n < m) ≡ true
thm20 {zero} {suc m} prf = refl
thm20 {suc n} {suc m} prf = thm20 {n} {m} prf

thm21 : compare n m ≡ lt → compare m p ≡ lt → compare n p ≡ lt
thm21 {zero} {suc m} {suc p} prf₁ prf₂ = refl
thm21 {suc n} {suc m} {suc p} prf₁ prf₂ = thm21 {n} {m} {p} prf₁ prf₂

thm22 : compare n m ≡ lt → compare m p ≡ eq → compare n p ≡ lt
thm22 {zero} {suc m} {suc p} prf₁ prf₂ = refl
thm22 {suc n} {suc m} {suc p} prf₁ prf₂ = thm22 {n} {m} {p} prf₁ prf₂

thm23 : compare n m ≡ eq → compare m p ≡ lt → compare n p ≡ lt
thm23 {zero} {zero} {suc p} prf₁ prf₂ = refl
thm23 {suc n} {suc m} {suc p} prf₁ prf₂ = thm23 {n} {m} {p} prf₁ prf₂

thm24 : compare n m ≡ eq → compare m p ≡ eq → compare n p ≡ eq
thm24 {zero} {zero} {zero} prf₁ prf₂ = refl
thm24 {suc n} {suc m} {suc p} prf₁ prf₂ = thm24 {n} {m} {p} prf₁ prf₂

extend : n ≤ m → m ≤ p → n ≤ p
extend {zero} {zero} {zero} prf₁ prf₂ = look₂ refl
extend {zero} {zero} {suc p} prf₁ prf₂ = look₁ refl
extend {zero} {suc m} {zero} prf₁ prf₂ = look₂ refl
extend {zero} {suc m} {suc p} prf₁ prf₂ = look₁ refl
extend {suc n} {zero} {zero} (look₁ ()) (look₁ prf₂)
extend {suc n} {zero} {zero} (look₁ ()) (look₂ prf₂)
extend {suc n} {zero} {zero} (look₂ ()) (look₁ prf₂)
extend {suc n} {zero} {zero} (look₂ ()) (look₂ prf₂)
extend {suc n} {zero} {suc p} (look₁ ()) prf
extend {suc n} {zero} {suc p} (look₂ ()) prf
extend {suc n} {suc m} {zero} (look₁ prf₁) (look₁ ())
extend {suc n} {suc m} {zero} (look₁ prf₁) (look₂ ())
extend {suc n} {suc m} {zero} (look₂ prf₁) (look₁ ())
extend {suc n} {suc m} {zero} (look₂ prf₁) (look₂ ())
extend {suc n} {suc m} {suc p} (look₁ prf₁) (look₁ prf₂) = look₁ (thm21 {n} {m} {p} prf₁ prf₂)
extend {suc n} {suc m} {suc p} (look₁ prf₁) (look₂ prf₂) = look₁ (thm22 {n} {m} {p} prf₁ prf₂)
extend {suc n} {suc m} {suc p} (look₂ prf₁) (look₁ prf₂) = look₁ (thm23 {n} {m} {p} prf₁ prf₂)
extend {suc n} {suc m} {suc p} (look₂ prf₁) (look₂ prf₂) = look₂ (thm24 {n} {m} {p} prf₁ prf₂)

_≤⟨_⟩_ : ∀ n → n ≤ m → m ≤ p → n ≤ p
n ≤⟨ p₁ ⟩ p₂ = extend p₁ p₂

thm7 : 1 ≤ (suc n)
thm7 {zero} = look₂ refl
thm7 {suc n} = look₁ refl

thm9 : compare n 0 ≡ eq → n ≡ 0
thm9 {zero} prf = refl

thm16 : {r : Ord} → compare n m ≡ r → compare (suc n) (suc m) ≡ r
thm16 {zero} {zero} {eq} prf = refl
thm16 {zero} {suc m} {lt} prf = refl
thm16 {suc n} {zero} {gt} prf = refl
thm16 {suc n} {suc m} {eq} prf = prf
thm16 {suc n} {suc m} {lt} prf = prf
thm16 {suc n} {suc m} {gt} prf = prf

thm14 : compare n m ≡ eq → n ≡ m
thm14 {zero} {zero} prf = refl
thm14 {suc n} {suc m} prf = cong suc (thm14 {n} {m} prf)

thm8 : suc n ≤ 1 → n ≡ zero
thm8 {zero} prf = refl
thm8 {suc n} (look₁ ())
thm8 {suc n} (look₂ ())

thm12 : (n < m) ≡ true → compare n m ≡ lt
thm12 {zero} {suc m} prf = refl
thm12 {suc n} {suc m} prf = thm12 {n} {m} prf

thm17 : (n < m) ≡ true → (suc n < suc m) ≡ true
thm17 {zero} {suc m} prf = refl
thm17 {suc n} {suc m} prf = prf

thm11 : (n < m) ≡ true → n ≤ m
thm11 {zero} {suc m} prf = look₁ refl
thm11 {suc n} {suc m} prf = look₁ (thm12 {n} {m} prf)

thm18 : compare n m ≡ lt → compare n (suc m) ≡ lt
thm18 {zero} {suc m} prf = refl
thm18 {suc n} {suc m} prf = thm18 {n} {m} prf

thm19 : compare n m ≡ eq → compare n (suc m) ≡ lt
thm19 {zero} {zero} prf = refl
thm19 {suc n} {suc m} prf = thm19 {n} {m} prf

thm10 : n ≤ m → n ≤ suc m
thm10 {zero} {zero} (look₂ refl) = look₁ refl
thm10 {zero} {suc m} (look₁ refl) = look₁ refl
thm10 {suc n} {suc m} (look₁ prf) = look₁ (thm18 {n} {m} prf)
thm10 {suc n} {suc m} (look₂ prf) = look₁ (thm19 {n} {m} prf)

thm25 : n ≤ m → suc n ≤ suc m
thm25 {zero} {zero} prf = look₂ refl
thm25 {zero} {suc m} prf = look₁ refl
thm25 {suc n} {zero} (look₁ ())
thm25 {suc n} {zero} (look₂ ())
thm25 {suc n} {suc m} (look₁ prf) = look₁ prf
thm25 {suc n} {suc m} (look₂ prf) = look₂ prf

≤suc : m ≤ suc m
≤suc {zero} = look₁ refl
≤suc {suc m} = thm25 (≤suc {m})

thm26 : m + suc n ≡ suc (m + n)
thm26 {zero} {zero} = refl
thm26 {zero} {suc n} = refl
thm26 {suc m} {zero} = cong suc thm26
thm26 {suc m} {suc n} = cong suc thm26

-- {-# REWRITE thm26 #-}

thm27 : compare m n ≡ lt → (suc m) ≤ n
thm27 {zero} {suc n} prf = thm7
thm27 {suc m} {suc n} prf = thm25 (thm27 prf)

thm28 : compare (m + n) 1 ≡ lt → suc (m + n) ≤ 1
thm28 prf = thm27 prf

thm37 : compare n 1 ≡ lt → n ≤ 1
thm37 {n} prf = thm13 (thm10 (thm27 {n} {1} prf))

thm29 : ∀{p} → (m + n) ≤ 1 → (m + n) ≤ suc p
thm29 {zero} {zero} {zero} prf = look₁ refl
thm29 {zero} {zero} {suc p} prf = look₁ refl
thm29 {zero} {suc n} {zero} prf = prf
thm29 {zero} {suc n} {suc p} prf = suc n ≤⟨ prf ⟩ thm7
thm29 {suc m} {zero} {zero} prf = prf
thm29 {suc m} {zero} {suc p} prf = _ ≤⟨ prf ⟩ (look₁ refl)
thm29 {suc m} {suc n} {zero} prf = prf
thm29 {suc m} {suc n} {suc p} prf = _ ≤⟨ prf ⟩ look₁ refl

thm30 : compare m n ≡ lt → m ≤ n
thm30 {zero} {suc n} prf = look₁ refl
thm30 {suc m} {suc n} prf = thm11 (thm20 {m} {n} prf)

thm30-2 : compare m n ≡ lt → suc m ≤ n
thm30-2 {zero} {suc n} p = thm7
thm30-2 {suc m} {suc n} p = thm25 (thm30-2 {m} {n} p)

thm31 : compare (m + n + p) 1 ≡ eq → ((m ≡ zero) ∧ (n ≡ zero)) → p ≡ 1
thm31 {zero} {zero} {suc p} prf₁ prf₂ = cong suc (thm9 prf₁)
thm31 {zero} {suc n} {zero} _ (_ & ())
thm31 {suc m} {zero} {zero} _ (() & _)

thm32 : p ≡ 1 → ((m ≡ zero) ∧ (n ≡ zero)) → suc (m + n) ≤ (p + (p + p))
thm32 {suc m} {zero} {zero} prf₁ prf₂ = thm7
thm32 {suc m} {zero} {suc p} _ (_ & ())
thm32 {suc m} {suc n} {zero} _ (() & _)
thm32 {suc m} {suc n} {suc p} _ (() & _)

thm34 : suc m ≡ suc n → m ≡ n
thm34 {zero} {n} refl = refl
thm34 {suc m} {n} refl = refl

_⟨⟨_≤≡_⟩⟩ : ∀ m → n ≤ m → m ≡ m₁ → n ≤ m₁
_⟨⟨_≤≡_⟩⟩ {zero} {zero} zero p₁ p₂ = look₂ refl
_⟨⟨_≤≡_⟩⟩ {zero} {suc m₁} (suc m) p₁ p₂ = look₁ refl
_⟨⟨_≤≡_⟩⟩ {suc n} {zero} zero (look₁ ()) p₂
_⟨⟨_≤≡_⟩⟩ {suc n} {zero} zero (look₂ ()) p₂
_⟨⟨_≤≡_⟩⟩ {suc n} {suc m₁} (suc m) p₁ p₂ = thm25 (_⟨⟨_≤≡_⟩⟩ {n} {m₁} m (thm13 p₁) (thm34 p₂))
-- ⟨⟨_≤≡_⟩⟩ : n ≤ m → m ≡ m₁ → n ≤ m₁
-- ⟨⟨_≤≡_⟩⟩ {zero} {zero} {zero} p₁ p₂ = look₂ refl
-- ⟨⟨_≤≡_⟩⟩ {zero} {suc m} {suc m₁} p₁ p₂ = look₁ refl
-- ⟨⟨_≤≡_⟩⟩ {suc n} {zero} {zero} (look₁ ()) p₂
-- ⟨⟨_≤≡_⟩⟩ {suc n} {zero} {zero} (look₂ ()) p₂
-- ⟨⟨_≤≡_⟩⟩ {suc n} {suc m} {suc m₁} p₁ p₂ = thm25 (⟨⟨_≤≡_⟩⟩ {n} {m} {m₁} (thm13 p₁) (thm34 p₂))

_⟪_≡≤_⟫ : ∀ n → n ≡ n₁ → n ≤ m → n₁ ≤ m
_⟪_≡≤_⟫ {zero} {zero} zero p₁ p₂ = look₂ refl
_⟪_≡≤_⟫ {suc n₁} {zero} (suc n) p₁ (look₁ ())
_⟪_≡≤_⟫ {suc n₁} {zero} (suc n) p₁ (look₂ ())
_⟪_≡≤_⟫ {zero} {suc m} zero p₁ p₂ = p₂
_⟪_≡≤_⟫ {suc n₁} {suc m} (suc n) p₁ p₂ = thm25 (_⟪_≡≤_⟫ {n₁} {m} n (thm34 p₁) (thm13 p₂))

_⟪_≡≤≡_⟫ : n ≤ m → n ≡ n₁ → m ≡ m₁ → n₁ ≤ m₁
_⟪_≡≤≡_⟫ {zero} {zero} {zero} {zero} p₁ p₂ p₃ = look₂ refl
_⟪_≡≤≡_⟫ {zero} {zero} {zero} {suc m₁} p₁ p₂ p₃ = look₁ refl
_⟪_≡≤≡_⟫ {zero} {suc m} {zero} {zero} p₁ p₂ p₃ = look₂ refl
_⟪_≡≤≡_⟫ {zero} {suc m} {zero} {suc m₁} p₁ p₂ p₃ = look₁ refl
_⟪_≡≤≡_⟫ {suc n} {zero} {suc n₁} {zero} (look₁ ()) p₂ p₃
_⟪_≡≤≡_⟫ {suc n} {zero} {suc n₁} {zero} (look₂ ()) p₂ p₃
_⟪_≡≤≡_⟫ {suc n} {zero} {suc n₁} {suc m₁} p₁ p₂ ()
_⟪_≡≤≡_⟫ {suc n} {suc m} {suc n₁} {zero} p₁ p₂ ()
_⟪_≡≤≡_⟫ {suc n} {suc m} {suc n₁} {suc m₁} p₁ p₂ p₃ = thm25 (thm13 p₁ ⟪ thm34 p₂ ≡≤≡ thm34 p₃ ⟫)

+-is-suc : suc m ≡ m + 1
+-is-suc {zero} = refl
+-is-suc {suc m} = cong suc (+-is-suc {m})

+-swap-suc : n + suc m ≡ m + suc n
+-swap-suc {zero} {zero} = refl
+-swap-suc {zero} {suc m} = cong suc +-is-suc
+-swap-suc {suc n} {zero} = cong suc (sym +-is-suc)
+-swap-suc {suc n} {suc m} = cong suc (_ ≡⟨ thm26 ⟩ (sym (_ ≡⟨ thm26 ⟩ (cong suc +-swap-suc))))

+-swap-suc-3 : m + n + suc n₁ ≡ suc (m + n + n₁)
+-swap-suc-3 {zero} {zero} {zero} = refl
+-swap-suc-3 {zero} {zero} {suc n₁} = refl
+-swap-suc-3 {zero} {suc n} {zero} = cong suc (sym (trans +-is-suc (_ ≡⟨ +zero-2 {n} {1} ⟩ refl)))
+-swap-suc-3 {zero} {suc n} {suc n₁} = cong suc (sym (trans +-is-suc (_ ≡⟨ +-swap-suc ⟩ (sym (_ ≡⟨ +-swap-suc ⟩ cong suc +-swap-suc)))))
+-swap-suc-3 {suc m} {zero} {zero} = cong suc (sym (_ ≡⟨ +-is-suc ⟩ (_ ≡⟨ +zero-2 {m + zero} {1} ⟩ sym (refl))))
+-swap-suc-3 {suc m} {zero} {suc n₁} = cong suc (_ ≡⟨ +zero-2 {m} {suc (suc n₁)} ⟩ (_ ≡⟨ +-swap-suc {m} {suc n₁} ⟩ cong suc (sym (_ ≡⟨ +zero-2 {m} {suc n₁} ⟩ +-swap-suc))))
+-swap-suc-3 {suc m} {suc n} {zero} = cong suc (+-swap-suc-3 {m} {suc n} {zero})
+-swap-suc-3 {suc m} {suc n} {suc n₁} = cong suc (+-swap-suc-3 {m} {suc n} {suc n₁})

+-swap-suc-3-2 : m + (suc n) + n₁ ≡ suc (m + n + n₁)
+-swap-suc-3-2 {zero} {zero} {zero} = refl
+-swap-suc-3-2 {zero} {zero} {suc n₁} = refl
+-swap-suc-3-2 {zero} {suc n} {zero} = refl
+-swap-suc-3-2 {zero} {suc n} {suc n₁} = cong suc (cong suc refl)
+-swap-suc-3-2 {suc m} {zero} {zero} = cong suc (+-swap-suc-3-2 {m} {zero} {zero})
+-swap-suc-3-2 {suc m} {zero} {suc n₁} = cong suc (+-swap-suc-3-2 {m} {zero} {suc n₁})
+-swap-suc-3-2 {suc m} {suc n} {zero} = cong suc (+-swap-suc-3-2 {m} {suc n} {zero})
+-swap-suc-3-2 {suc m} {suc n} {suc n₁} = cong suc (+-swap-suc-3-2 {m} {suc n} {suc n₁})

+-sym : n + m ≡ m + n
+-sym {zero} {zero} = refl
+-sym {zero} {suc m} = cong suc (sym (+zero {m}))
+-sym {suc n} {zero} = cong suc +zero
+-sym {suc n} {suc m} = cong suc +-swap-suc

≤-double : n ≤ m → (n + n) ≤ (m + m)
≤-double {zero} {zero} p = look₂ refl
≤-double {suc n} {zero} (look₁ ())
≤-double {suc n} {zero} (look₂ ())
≤-double {zero} {suc m} (look₁ p) = look₁ refl
≤-double {suc n} {suc m} p = thm25 (thm25 (≤-double {n} {m} (thm13 p)) ⟪ sym (thm26 {n} {n}) ≡≤≡ sym (thm26 {m} {m}) ⟫)

thm35 : m ≡ n → m ≤ p → n ≤ p
thm35 {zero} {zero} {zero} prf₁ prf₂ = look₂ refl
thm35 {zero} {zero} {suc p} prf₁ prf₂ = look₁ refl
thm35 {suc m} {suc n} {zero} prf₁ (look₁ ())
thm35 {suc m} {suc n} {zero} prf₁ (look₂ ())
thm35 {suc m} {suc n} {suc p} prf₁ prf₂ = thm25 (thm35 {m} {n} {p} (thm34 prf₁) (thm13 prf₂))

-- thm36 : compare (m + n + p) 1 ≡ eq → n ≤ (m + (m + m)) → m ≤ (n + (n + n)) → (m ≡ 0) ∧ (n ≡ 0)
-- thm36 {zero} {zero} {suc p} prf₁ prf₂ prf₃ = refl & refl
-- thm36 {zero} {suc n} {zero} _ (look₁ ()) _
-- thm36 {zero} {suc n} {zero} _ (look₂ ()) _
-- thm36 {suc m} {zero} {zero} _ _ (look₁ ())
-- thm36 {suc m} {zero} {zero} _ _ (look₂ ())

thm40 : m ≡ n → suc m ≤ suc n
thm40 {zero} {zero} prf = look₂ refl
thm40 {suc m} {suc n} prf = thm25 (thm40 (thm34 prf))

thm39 : compare (m + n) 1 ≡ eq → suc (m + n) ≤ 2
thm39 {m} {n} prf = thm40 (thm14 {m + n} {1} prf)

thm41 : {m₁ n₁ : Nat} → compare (m₁ + n₁) 1 ≡ eq → compare (m₁ + n₁) (n + (n + n)) ≡ lt → 2 ≤ (n + (n + n))
thm41 {suc n} {zero} {suc n₁} prf₁ prf₂ = thm25 (suc (n + (n + suc n)) ⟨⟨ thm7 ≤≡ sym (thm26 {n} {n + suc n}) ⟩⟩)
-- thm41 {suc n} {zero} {suc n₁} prf₁ prf₂ = thm25 {!   !}
-- thm41 {suc n} {suc m₁} {zero} prf₁ prf₂ = {! thm25 thm7 !}
thm41 {suc n} {suc m₁} {zero} prf₁ prf₂ = thm25 (suc (n + (n + suc n)) ⟨⟨ thm7 ≤≡ sym (thm26 {n} {n + suc n}) ⟩⟩)
thm41 {suc n} {suc m₁} {suc n₁} prf₁ prf₂ = thm25 (suc (n + (n + suc n)) ⟨⟨ thm7 ≤≡ sym (thm26 {n} {n + suc n}) ⟩⟩)

thm46 : compare m 0 ≡ lt → ⊥
thm46 {zero} ()
thm46 {suc m} ()

thm43 : {m₁ : Nat} → m₁ ≡ 1 → compare n (m₁ + (m₁ + m₁)) ≡ lt → n ≤ 3
thm43 {zero} {suc m₁} prf₁ prf₂ = look₁ refl
thm43 {suc zero} {suc zero} prf₁ prf₂ = look₁ refl
thm43 {suc (suc zero)} {suc zero} prf₁ prf₂ = look₁ refl
thm43 {suc (suc (suc zero))} {suc zero} prf₁ prf₂ = look₂ refl
thm43 {suc (suc (suc (suc n)))} {suc zero} prf₁ ()

thm42 : {m₁ n₁ : Nat} → compare (m₁ + n₁) 1 ≡ eq → compare n (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁))) ≡ lt → n ≤ 3
thm42 {n} {m₁} {n₁} prf₁ prf₂ = thm43 (thm14 {m₁ + n₁} {1} prf₁) prf₂

thm47 : m ≡ 0 → compare (suc m) 1 ≡ eq
thm47 {zero} prf = refl


thm48 : compare (m₁ + n₁) 1 ≡ lt → (m₁ + n₁) ≡ 0
thm48 {zero} {zero} prf = refl
thm48 {zero} {suc zero} ()
thm48 {zero} {suc (suc n₁)} ()
thm48 {suc zero} {zero} ()
thm48 {suc (suc m₁)} {zero} ()

thm49 : (m₁ + n₁) ≡ 0 → compare (m₁ + n₁) (n + (n + n)) ≡ eq → n ≡ 0
thm49 {zero} {zero} {zero} prf₁ prf₂ = refl

thm50 : (m₁ + n₁) ≡ 0 → n ≡ 0 → suc (m₁ + n₁ + n) ≤ 1
thm50 {zero} {zero} {zero} prf₁ prf₂ = look₂ refl

thm51 : compare (m + n) 1 ≡ lt → suc (m + n) ≤ 2
thm51 {m} {n} prf = thm25 (thm37 {m + n} prf)

thm52 : compare (m₁ + n₁) 1 ≡ lt → compare (m₁ + n₁) (n + (n + n)) ≡ lt → 2 ≤ (n + (n + n))
-- thm52 {zero} {zero} {suc n} prf₁ prf₂ = {! thm25 thm7 !}
thm52 {zero} {zero} {suc n} prf₁ prf₂ = thm25 (suc (n + (n + suc n)) ⟨⟨ thm7 ≤≡ sym (thm26 {n} {n + suc n}) ⟩⟩)
-- thm52 {zero} {suc n₁} {suc n} prf₁ prf₂ = {! thm25 thm7 !}
thm52 {zero} {suc n₁} {suc n} prf₁ prf₂ = thm25 (suc (n + (n + suc n)) ⟨⟨ thm7 ≤≡ sym (thm26 {n} {n + suc n}) ⟩⟩)
-- thm52 {suc m₁} {zero} {suc n} prf₁ prf₂ = {! thm25 thm7 !}
thm52 {suc m₁} {zero} {suc n} prf₁ prf₂ = thm25 (suc (n + (n + suc n)) ⟨⟨ thm7 ≤≡ sym (thm26 {n} {n + suc n}) ⟩⟩)
thm52 {suc m₁} {suc n₁} {suc n} prf₁ prf₂ = thm25 (suc (n + (n + suc n)) ⟨⟨ thm7 ≤≡ sym (thm26 {n} {n + suc n}) ⟩⟩)

thm53 : {m₁ n₁ : Nat} → compare (m₁ + n₁) 1 ≡ lt → compare n (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁))) ≡ eq → n ≤ 3
thm53 {zero} {zero} {zero} prf₁ prf₂ = look₁ refl
thm53 {suc zero} {zero} {suc zero} prf₁ prf₂ = look₁ refl
thm53 {suc zero} {zero} {suc (suc n₁)} prf₁ prf₂ = look₁ refl
thm53 {suc (suc n)} {zero} {suc zero} () prf₂
thm53 {suc (suc n)} {zero} {suc (suc n₁)} () prf₂
thm53 {suc zero} {suc zero} {zero} prf₁ prf₂ = look₁ refl
thm53 {suc zero} {suc (suc m₁)} {zero} prf₁ prf₂ = look₁ refl
thm53 {suc (suc n)} {suc zero} {zero} () prf₂
thm53 {suc (suc n)} {suc (suc m₁)} {zero} () prf₂

thm54 : compare (m₁ + n₁) 1 ≡ eq → compare n (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁))) ≡ eq → n ≤ 3
thm54 {zero} {suc zero} {suc (suc (suc zero))} prf₁ prf₂ = look₂ refl
thm54 {suc zero} {zero} {suc (suc (suc zero))} prf₁ prf₂ = look₂ refl

thm38 : {m₁ n₁ : Nat} → n ≤ (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁))) → (m₁ + n₁) ≤ (n + (n + n)) → ((m₁ + n₁) ≤ 1) → (m ≡ (m₁ + n₁)) → ((suc (m₁ + n₁ + n)) ≤ 1) ∨ ((suc (m₁ + n₁) ≤ (n + (n + n))) ∧ (n ≤ suc (suc (suc (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁)))))))
thm38 {n} {m} {m₁} {n₁} (look₁ p₁) (look₁ p₂) (look₂ p₃) refl = or₂ ((_ ≤⟨ thm39 {m₁} {n₁} p₃ ⟩ thm41 {n} {m₁} {n₁} p₃ p₂) & (_ ≤⟨ thm42 {n} {m₁} {n₁} p₃ p₁ ⟩ thm25 (thm25 thm7)))
thm38 {n} {m} {m₁} {n₁} (look₁ p₁) (look₂ p₂) (look₁ p₃) refl = or₁ (thm50 {m₁} {n₁} {n} (thm48 {m₁} {n₁} p₃) (thm49 {m₁} {n₁} {n} (thm48 {m₁} {n₁} p₃) p₂))
thm38 {suc zero} {m} {zero} {suc zero} (look₁ p₁) (look₂ ()) (look₂ p₃) refl
thm38 {suc zero} {m} {zero} {suc (suc n₁)} (look₁ p₁) (look₂ p₂) (look₂ ()) refl
thm38 {suc (suc n)} {m} {zero} {suc zero} (look₁ p₁) (look₂ ()) (look₂ p₃) refl
thm38 {suc (suc n)} {m} {zero} {suc (suc n₁)} (look₁ p₁) (look₂ p₂) (look₂ ()) refl
thm38 {suc zero} {m} {suc zero} {zero} (look₁ p₁) (look₂ ()) (look₂ p₃) refl
thm38 {suc zero} {m} {suc (suc m₁)} {zero} (look₁ p₁) (look₂ p₂) (look₂ ()) refl
thm38 {suc (suc n)} {m} {suc zero} {zero} (look₁ p₁) (look₂ ()) (look₂ p₃) refl
thm38 {suc (suc n)} {m} {suc (suc m₁)} {zero} (look₁ p₁) (look₂ p₂) (look₂ ()) refl
thm38 {n} {m} {m₁} {n₁} (look₂ p₁) (look₁ p₂) (look₁ p₃) refl = or₂ ((_ ≤⟨ thm51 {m₁} {n₁} p₃ ⟩ thm52 {m₁} {n₁} {n} p₃ p₂) & (_ ≤⟨ thm53 {n} {m₁} {n₁} p₃ p₁ ⟩ thm25 (thm25 thm7)))
thm38 {n} {m} {m₁} {n₁} (look₂ p₁) (look₁ p₂) (look₂ p₃) refl = or₂ ((_ ≤⟨ thm39 {m₁} {n₁} p₃ ⟩ thm41 {n} {m₁} {n₁} p₃ p₂) & (_ ≤⟨ thm54 {m₁} {n₁} {n} p₃ p₁ ⟩ thm25 (thm25 thm7)))
thm38 {n} {m} {m₁} {n₁} (look₂ p₁) (look₂ p₂) (look₁ p₃) refl = or₁ (thm50 {m₁} {n₁} {n} (thm48 {m₁} {n₁} p₃) (thm49 {m₁} {n₁} {n} (thm48 {m₁} {n₁} p₃) p₂))
thm38 {suc zero} {m} {zero} {suc zero} (look₂ p₁) (look₂ ()) (look₂ p₃) refl
thm38 {suc zero} {m} {zero} {suc (suc n₁)} (look₂ p₁) (look₂ p₂) (look₂ ()) refl
thm38 {suc (suc n)} {m} {zero} {suc zero} (look₂ p₁) (look₂ ()) (look₂ p₃) refl
thm38 {suc (suc n)} {m} {zero} {suc (suc n₁)} (look₂ p₁) (look₂ p₂) (look₂ ()) refl
thm38 {suc zero} {m} {suc zero} {zero} (look₂ p₁) (look₂ ()) (look₂ p₃) refl
thm38 {suc zero} {m} {suc (suc m₁)} {zero} (look₂ p₁) (look₂ p₂) (look₂ ()) refl
thm38 {suc (suc n)} {m} {suc zero} {zero} (look₂ p₁) (look₂ ()) (look₂ p₃) refl
thm38 {suc (suc n)} {m} {suc (suc m₁)} {zero} (look₂ p₁) (look₂ p₂) (look₂ ()) refl   
thm38 {zero} {zero} {zero} {n₁} (look₁ p₁) (look₁ p₂) (look₁ p₃) refl = or₁ (look₂ refl)
thm38 {suc n} {zero} {zero} {n₁} (look₁ ()) (look₁ p₂) (look₁ p₃) refl
thm38 {n} {suc zero} {zero} {n₁} (look₁ p₁) (look₁ p₂) (look₁ ()) refl
thm38 {n} {suc (suc m)} {zero} {n₁} (look₁ p₁) (look₁ p₂) (look₁ ()) refl
thm38 {n} {m} {suc zero} {zero} (look₁ p₁) (look₁ p₂) (look₁ ()) refl
thm38 {n} {m} {suc zero} {suc n₁} (look₁ p₁) (look₁ p₂) (look₁ ()) refl

data Map (K : Set) (A : Set) : Nat → Set where
  tip : Map K A zero
  node : K → A → Map K A m → Map K A n → Map K A (suc (m + n))

data BalancedMap (K : Set) (A : Set) : Nat → Set where
  tip : BalancedMap K A zero
  node : K → A → (BalancedMap K A m) → (BalancedMap K A n) → {((m + n) ≤ 1) ∨ ((m ≤ (δ * n)) ∧ (n ≤ (δ * m)))} → BalancedMap K A (suc (m + n))

data SemiBalancedMap (K : Set) (A : Set) : Nat → Set where
  tip : SemiBalancedMap K A zero
  tipNode : K → A → SemiBalancedMap K A 1
  nodeLB : K → A → BalancedMap K A m → SemiBalancedMap K A n → SemiBalancedMap K A (suc (m + n))
  nodeRB : K → A → SemiBalancedMap K A n → BalancedMap K A m → SemiBalancedMap K A (suc (m + n))

data Balance : Set where
  LB : Nat → Balance
  RB : Nat → Balance
  EB : Balance

-- α : BalancedMap K A n → Balance
-- α tip = {!   !}
-- α (node {m = zero} {n = zero} _ _ _ _) = EB
-- α (node {m = zero} {n = suc zero} _ _ _ _) = EB
-- α (node {m = suc zero} {n = zero} _ _ _ _) = EB
-- α (node {m = zero} {n = suc (suc n)} _ _ _ _) = {!   !}
-- α (node {m = suc (suc m)} {n = zero} _ _ _ _) = {!   !}
-- α (node {m = suc m} {n = suc n} _ _ _ _) = {!   !}


size : BalancedMap K A n → Nat
size {n = n} _ = n

balancedMap2Map : BalancedMap K A n → Map K A n
balancedMap2Map tip = tip
balancedMap2Map (node k a l r) = node k a (balancedMap2Map l) (balancedMap2Map r)

data _∈_ {K : Set} (a : A) : BalancedMap K A (suc n) → Set where
  here : ∀{k m n}{l : BalancedMap K A m}{r : BalancedMap K A n}{p : ((m + n) ≤ 1) ∨ ((m ≤ (δ * n)) ∧ (n ≤ (δ * m)))} → a ∈ node k a l r {p}
  thereL : ∀{k n a'}{l : BalancedMap K A (suc m)}{r : BalancedMap K A n}{p : (((suc m) + n) ≤ 1) ∨ (((suc m) ≤ (δ * n)) ∧ (n ≤ (δ * (suc m))))} → a ∈ l → a ∈ (node k a' l r {p})
  thereR : ∀{k m a'}{l : BalancedMap K A m}{r : BalancedMap K A (suc n)}{p : ((m + (suc n)) ≤ 1) ∨ ((m ≤ (δ * (suc n))) ∧ ((suc n) ≤ (δ * m)))} → a ∈ r → a ∈ (node k a' l r {p})

data _∈k_ {A : Set} (k : K) : BalancedMap K A (suc n) → Set where
  here : ∀{a m n}{l : BalancedMap K A m}{r : BalancedMap K A n}{p : ((m + n) ≤ 1) ∨ ((m ≤ (δ * n)) ∧ (n ≤ (δ * m)))} → k ∈k node k a l r {p}
  thereL : ∀{k' n a}{l : BalancedMap K A (suc m)}{r : BalancedMap K A n}{p : (((suc m) + n) ≤ 1) ∨ (((suc m) ≤ (δ * n)) ∧ (n ≤ (δ * (suc m))))} → k ∈k l → k ∈k (node k' a l r {p})
  thereR : ∀{k' m a}{l : BalancedMap K A m}{r : BalancedMap K A (suc n)}{p : ((m + (suc n)) ≤ 1) ∨ ((m ≤ (δ * (suc n))) ∧ ((suc n) ≤ (δ * m)))} → k ∈k r → k ∈k (node k' a l r {p})

data _∉k_ {A : Set} (k : K) : BalancedMap K A n → Set where

-- thm64 : ∀{a l r k k'} → compare k k' ≡ eq → k' ∈k node k a l r
-- thm64 = ?

thm : ∀{p} → ∀{k k' : K}{a : A} → {l : BalancedMap K A (suc m)} → {r : BalancedMap K A n} → k' ∈k l → k' ∈k node k a l r {p}
thm here = thereL here
thm (thereL p) = thereL (thereL p)
thm (thereR p) = thereL (thereR p)

thm' : ∀{p} → ∀{k k' : K}{a : A} → {l : BalancedMap K A m} → {r : BalancedMap K A (suc n)} → k' ∈k r → k' ∈k node k a l r {p}
thm' here = thereR here
thm' (thereL p) = thereR (thereL p)
thm' (thereR p) = thereR (thereR p)

∈k-flowsL : ∀{p} → ∀{k' : K}{a : A} → {k : K} → {l : BalancedMap K A (suc m)} → {r : BalancedMap K A n} → (k' ∈k node k a l r {p} → ⊥) → k' ∈k l → ⊥
∈k-flowsL {K} {A} {m} {n} {p} {k'} {a} {k} {l} {r} p₁ p₂ with thm {_} {_} {_} {_} {p} {k} {_} {a} {_} {r} p₂
∈k-flowsL {K} {A} {m} {n} {p} {k'} {a} {k} {l} {r} p₁ p₂ | p₃ = p₁ p₃

∈k-flowsR : ∀{p} → ∀{k' : K}{a : A} → {k : K} → {l : BalancedMap K A m} → {r : BalancedMap K A (suc n)} → (k' ∈k node k a l r {p} → ⊥) → k' ∈k r → ⊥
∈k-flowsR {K} {A} {m} {n} {p} {k'} {a} {k} {l} {r} p₁ p₂ with thm' {_} {_} {_} {_} {p} {k} {_} {a} {l} p₂
∈k-flowsR {K} {A} {m} {n} {p} {k'} {a} {k} {l} {r} p₁ p₂ | p₃ = p₁ p₃

+-associative : n₁ + (m + n) ≡ m + n + n₁
+-associative {zero} {zero} {zero} = refl
+-associative {zero} {zero} {suc n} = sym (cong suc +zero)
+-associative {zero} {suc m} {zero} = sym (cong suc +zero)
+-associative {zero} {suc m} {suc n} = sym (cong suc +zero)
+-associative {suc n₁} {zero} {zero} = cong suc +zero
+-associative {suc n₁} {zero} {suc n} = cong suc +-swap-suc
+-associative {suc n₁} {suc m} {zero} = cong suc (sym +-swap-suc)
+-associative {suc n₁} {suc m} {suc n} = cong suc +-swap-suc  

+-associative-2 : m + n + n₁ ≡ m + n₁ + n
+-associative-2 {zero} {zero} {zero} = refl
+-associative-2 {zero} {zero} {suc n₁} = cong suc (sym +zero)
+-associative-2 {zero} {suc n} {zero} = cong suc +zero
+-associative-2 {zero} {suc n} {suc n₁} = cong suc +-swap-suc
+-associative-2 {suc m} {zero} {zero} = cong suc refl
+-associative-2 {suc m} {zero} {suc n₁} = cong suc (+-associative-2 {m} {zero} {suc n₁})
+-associative-2 {suc m} {suc n} {zero} = cong suc (+-associative-2 {m} {suc n} {zero})
+-associative-2 {suc m} {suc n} {suc n₁} = cong suc (+-associative-2 {m} {suc n} {suc n₁})

≤-associative : (m + n + n₁) ≤ (m + n + m₁) → n₁ ≤ m₁
≤-associative {zero} {zero} {n₁} {m₁} p = p
≤-associative {zero} {suc n} {n₁} {m₁} p = ≤-associative {zero} {n} (thm13 p)
≤-associative {suc m} {zero} {n₁} {m₁} p = ≤-associative {m} {zero} (thm13 p)
≤-associative {suc m} {suc n} {n₁} {m₁} p = ≤-associative {m} {n} {n₁} {m₁} (thm13 (thm13 (p ⟪ cong suc (+-swap-suc-3-2 {m} {n} {n₁}) ≡≤≡ cong suc (+-swap-suc-3-2 {m} {n} {m₁}) ⟫)))