module BalancedMap.Insert where

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
  m n m₁ n₁ : Nat

thm64 : ∀{p} → {l : BalancedMap K A m} → {r : BalancedMap K A n} → {a : A} → {k k' : K} → k ≡ k' → k' ∈k node {_} {_} {m} {n} k a l r {p}
thm64 {k = k} {k' = k'} refl = here

+-commutative : ∀ m n → m + n ≡ n + m
+-commutative zero zero = refl
+-commutative zero (suc n) = cong suc (sym +zero)
+-commutative (suc m) zero = cong suc +zero
+-commutative (suc m) (suc n) = cong suc (_ ≡⟨ thm26 ⟩ sym (_ ≡⟨ thm26 ⟩ cong suc (sym (+-commutative m n))))

thm66 : m ≡ n → SemiBalancedMap K A m → SemiBalancedMap K A n
thm66 {m} {n} refl map = map

thm72 : m ≡ n → BalancedMap K A m → BalancedMap K A n
thm72 {m} {n} refl map = map

thm65 : suc (m + 1) ≡ suc (suc (m + zero))
thm65 {zero} = refl
thm65 {suc m} = cong suc (cong suc (sym (_ ≡⟨ +-is-suc {m + zero} ⟩ (_ ≡⟨ +-swap-suc-3 {m} {zero} {zero} ⟩ (_ ≡⟨ +-is-suc {m + zero + zero} ⟩ (_ ≡⟨ +zero-2 {m + zero} {1} ⟩ +zero-2 {m} {1}))))))

thm67 : m + suc (suc (m₁ + n)) ≡ suc (m + suc (m₁ + n))
thm67 {m} {m₁} {n} = _ ≡⟨ +-swap-suc ⟩ cong suc (_ ≡⟨ +-swap-suc-3 {m₁} {n} {m} ⟩ sym (_ ≡⟨ +-swap-suc {m} {m₁ + n} ⟩ +-swap-suc-3 {m₁} {n} {m}))

thm68 : (suc (m₁ + n₁ + n) ≤ 1) ∨ ((suc (m₁ + n₁) ≤ (n + (n + n))) ∧ (n ≤ suc (suc (suc (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁))))))) → (suc (m₁ + n₁ + n) ≤ 1) ∨ ((suc (m₁ + n₁) ≤ (n + (n + (n + zero)))) ∧ (n ≤ suc (m₁ + n₁ + suc (m₁ + n₁ + suc (m₁ + n₁ + zero)))))
thm68 {m₁} {n₁} {n} (or₁ p) = or₁ p
thm68 {m₁} {n₁} {n} (or₂ (p₁ & p₂)) = or₂ ((_ ⟨⟨ p₁ ≤≡ cong (λ x → n + (n + x)) (sym +zero) ⟩⟩) & (_ ⟨⟨ p₂ ≤≡ cong suc {!   !} ⟩⟩))

thm69 : n ≤ (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁ + 0))) → n ≤ (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁)))
thm69 {n} {m₁} {n₁} p = _ ⟨⟨ p ≤≡ cong (λ x → m₁ + n₁ + (m₁ + n₁ + x)) (+zero {m₁ + n₁}) ⟩⟩

thm70 : (m₁ + n₁) ≤ (n + (n + (n + 0))) → (m₁ + n₁) ≤ (n + (n + n))
thm70 {m₁} {n₁} {n} p = _ ⟨⟨ p ≤≡ cong (n +_) (cong (n +_) +zero) ⟩⟩

thm73 : m₁ + n₁ + suc (suc (m + n)) ≡ suc (m₁ + n₁ + suc (m + n))
thm73 {m₁} {n₁} {m} {n} = +-swap-suc-3 {m₁} {n₁} {suc (m + n)}

thm75 : (m + n + suc (m + n + suc (m + n + 0))) ≤ (m + n + suc (suc (m + n + suc (suc (m + n + 0)))))
thm75 {m} {n} = {!   !}

thm74 : suc (m₁ + n₁) ≤ suc (m + n + suc (m + n + suc (m + n + 0))) → (m₁ + n₁) ≤ suc (m + n + suc (suc (m + n + suc (suc (m + n + 0)))))
thm74 {m₁} {n₁} {m} {n} p = _ ≤⟨ thm13 p ⟩ thm10 {!   !}

thm77 : n ≤ (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁ + 0))) → (n + (n + (n + 0))) ≤ ((m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁ + 0))) + ((m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁ + 0))) + ((m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁ + 0))) + 0)))
thm77 {zero} {zero} {zero} p = look₂ refl
thm77 {zero} {zero} {suc n₁} p = look₁ refl
thm77 {zero} {suc m₁} {zero} p = look₁ refl
thm77 {zero} {suc m₁} {suc n₁} p = look₁ refl
thm77 {suc n} {zero} {zero} (look₁ ())
thm77 {suc n} {zero} {zero} (look₂ ())
thm77 {suc n} {zero} {suc n₁} p = {!   !}
thm77 {suc n} {suc m₁} {zero} p = thm25 {!   !}
thm77 {suc n} {suc m₁} {suc n₁} p = {!   !}

thm78 : (m + n + suc (m₁ + n₁)) ≤ zero → ⊥
thm78 {m} {n} {m₁} {n₁} p with _ ⟪ (+-swap-suc-3 {m}) ≡≤ p ⟫
thm78 {m} {n} {m₁} {n₁} p | look₁ ()
thm78 {m} {n} {m₁} {n₁} p | look₂ ()

-- thm76 : (m₁ + n₁) ≤ (n + (n + (n + 0))) → n ≤ (m₁ + n₁ + (m₁ + n₁ + (m₁ + n₁ + 0))) → (m₁ ≤ (n₁ + (n₁ + (n₁ + 0)))) ∧ (n₁ ≤ (m₁ + (m₁ + (m₁ + 0)))) → suc (m₁ + n₁) ≤ (n + (n + (n + 0)))
-- thm76 {m₁} {n₁} {n} (look₁ x) p₂ (p₃ & p₄) = thm30-2 {m₁ + n₁} {n + (n + (n + 0))} x
-- thm76 {zero} {zero} {zero} (look₂ x) p₂ (p₃ & p₄) = {!   !}
-- thm76 {zero} {suc n₁} {suc n} (look₂ x) p₂ (p₃ & p₄) = {!   !}
-- thm76 {suc m₁} {zero} {suc n} (look₂ x) p₂ (p₃ & p₄) = {!   !}
-- thm76 {suc m₁} {suc n₁} {suc n} (look₂ x) p₂ (p₃ & p₄) = {!   !}

insertDirty : {{Comparable K}} → (k' : K) → (a' : A) → (map : BalancedMap K A (suc n)) → {p : k' ∈k map → ⊥} → SemiBalancedMap K A (suc (suc n))
insertDirty k' a' (node k a l r {p}) {p₁} with compare k' k
insertDirty k' a' (node k a l r {p}) {p₁} | eq with p₁ (thm64 (eq⇒eq k k' {!   !}))
insertDirty k' a' (node k a l r {p}) {p₁} | eq | ()
insertDirty k' a' (node k a tip r {p}) {p₁} | lt = thm66 (sym +-is-suc) (nodeRB k a (tipNode k' a') r)
insertDirty {n = n} k' a' (node k a l@(node lk la ll lr) r {p}) {p₁} | lt = thm66 (cong suc (_ ≡⟨ +-swap-suc {size r} {_} ⟩ cong suc (+-swap-suc-3 {size ll} {size lr} {size r}))) (nodeRB k a (insertDirty k' a' l {∈k-flowsL p₁}) r)
insertDirty k' a' (node k a l tip {p}) {p₁} | gt = thm66 thm65 (nodeLB k a l (tipNode k' a'))
insertDirty k' a' (node k a l r@(node rk ra rl rr) {p}) {p₁} | gt = thm66 (cong suc (thm67 {size l} {size rl} {size rr})) (nodeLB k a l (insertDirty k' a' r {∈k-flowsR {_} {_} {_} {_} {p} {k'} {a} {k} {l} p₁}))

insert : {{Comparable K}} → K → A → BalancedMap K A n → BalancedMap K A (suc n) ∨ BalancedMap K A n
insert k' a' tip = or₁ (node k' a' tip tip {or₁ (look₁ refl)})
insert k' a' (node k a l r {or₁ p}) with compare k' k
insert k' a' (node k a l r {or₁ p}) | eq = or₂ (node k a' l r {or₁ p})
insert k' a' (node k a tip tip {or₁ p}) | lt = or₁ (node k a (node k' a' tip tip {or₁ (look₁ refl)}) tip {or₁ (look₂ refl)})
insert k' a' (node k a tip (node rk ra tip tip) {or₁ p}) | lt = or₁ (node k a (node k' a' tip tip {or₁ (look₁ refl)}) (node rk ra tip tip {or₁ (look₁ refl)}) {or₂ (look₁ refl & look₁ refl)})
insert k' a' (node k a tip (node rk ra tip (node x x₁ rr rr₁)) {or₁ (look₁ ())}) | lt
insert k' a' (node k a tip (node rk ra tip (node x x₁ rr rr₁)) {or₁ (look₂ ())}) | lt
insert k' a' (node k a tip (node rk ra (node x x₁ rl rl₁) tip) {or₁ (look₁ ())}) | lt
insert k' a' (node k a tip (node rk ra (node x x₁ rl rl₁) tip) {or₁ (look₂ ())}) | lt
insert k' a' (node k a tip (node rk ra (node x x₁ rl rl₁) (node x₂ x₃ rr rr₁)) {or₁ (look₁ ())}) | lt
insert k' a' (node k a tip (node rk ra (node x x₁ rl rl₁) (node x₂ x₃ rr rr₁)) {or₁ (look₂ ())}) | lt
insert k' a' (node k a (node lk la tip tip) tip {or₁ p}) | lt with compare k' lk
insert k' a' (node k a (node lk la tip tip) tip {or₁ p}) | lt | eq = or₂ (node k a (node lk a' tip tip {or₁ (look₁ refl)}) tip {or₁ (look₂ refl)})
insert k' a' (node k a (node lk la tip tip) tip {or₁ p}) | lt | lt = or₁ (node lk la (node k' a' tip tip {or₁ (look₁ refl)}) (node k a tip tip {or₁ (look₁ refl)}) {or₂ (look₁ refl & look₁ refl)})
insert k' a' (node k a (node lk la tip tip) tip {or₁ p}) | lt | gt = or₁ (node k' a' (node lk la tip tip {or₁ (look₁ refl)}) (node k a tip tip {or₁ (look₁ refl)}) {or₂ (look₁ refl & look₁ refl)})
insert k' a' (node k a (node _ _ _ _) (node _ _ _ _) {or₁ (look₁ ())}) | lt
insert k' a' (node k a (node _ _ _ _) (node _ _ _ _) {or₁ (look₂ ())}) | lt

insert k' a' (node k a tip tip {or₁ p}) | gt = or₁ (node k a tip (node k' a' tip tip {or₁ (look₁ refl)}) {or₁ (look₂ refl)})
insert k' a' (node k a (node lk la tip tip) tip {or₁ p}) | gt = or₁ (node k a (node lk la tip tip {or₁ (look₁ refl)}) (node k' a' tip tip {or₁ (look₁ refl)}) {or₂ (look₁ refl & look₁ refl)})
insert k' a' (node k a (node lk la tip (node x x₁ lr lr₁)) tip {or₁ (look₁ ())}) | gt
insert k' a' (node k a (node lk la tip (node x x₁ lr lr₁)) tip {or₁ (look₂ ())}) | gt
insert k' a' (node k a (node lk la (node x x₁ ll ll₁) tip) tip {or₁ (look₁ ())}) | gt
insert k' a' (node k a (node lk la (node x x₁ ll ll₁) tip) tip {or₁ (look₂ ())}) | gt
insert k' a' (node k a (node lk la (node x x₁ ll ll₁) (node x₂ x₃ lr lr₁)) tip {or₁ (look₁ ())}) | gt
insert k' a' (node k a (node lk la (node x x₁ ll ll₁) (node x₂ x₃ lr lr₁)) tip {or₁ (look₂ ())}) | gt
insert k' a' (node k a tip (node rk ra tip tip) {or₁ p}) | gt with compare k' rk
insert k' a' (node k a tip (node rk ra tip tip) {or₁ p}) | gt | eq = or₂ (node k a tip (node rk a' tip tip {or₁ (look₁ refl)}) {or₁ (look₂ refl)})
insert k' a' (node k a tip (node rk ra tip tip) {or₁ p}) | gt | lt = or₁ (node k' a' (node k a tip tip {or₁ (look₁ refl)}) (node rk ra tip tip {or₁ (look₁ refl)}) {or₂ (look₁ refl & look₁ refl)})
insert k' a' (node k a tip (node rk ra tip tip) {or₁ p}) | gt | gt = or₁ (node rk ra (node k a tip tip {or₁ (look₁ refl)}) (node k' a' tip tip {or₁ (look₁ refl)}) {or₂ (look₁ refl & look₁ refl)})
insert k' a' (node k a tip (node rk ra tip (node x x₁ rr rr₁)) {or₁ (look₁ ())}) | gt
insert k' a' (node k a tip (node rk ra tip (node x x₁ rr rr₁)) {or₁ (look₂ ())}) | gt
insert k' a' (node k a tip (node rk ra (node x x₁ rl rl₁) tip) {or₁ (look₁ ())}) | gt
insert k' a' (node k a tip (node rk ra (node x x₁ rl rl₁) tip) {or₁ (look₂ ())}) | gt
insert k' a' (node k a tip (node rk ra (node x x₁ rl rl₁) (node x₂ x₃ rr rr₁)) {or₁ (look₁ ())}) | gt
insert k' a' (node k a tip (node rk ra (node x x₁ rl rl₁) (node x₂ x₃ rr rr₁)) {or₁ (look₂ ())}) | gt
insert k' a' (node k a (node lk la ll lr) (node rk ra rl rr) {or₁ p}) | gt with thm78 {size ll} {size lr} {size rl} {size rr} (thm13 p)
insert k' a' (node k a (node lk la ll lr) (node rk ra rl rr) {or₁ p}) | gt | ()

insert k' a' (node {m = m} {n = n} k a l r {or₂ p}) with compare k' k
insert k' a' (node {m = m} {n = n} k a l r {or₂ p}) | eq = or₂ (node k a' l r {or₂ p})
insert k' a' (node {m = m} {n = n} k a l r {or₂ p}) | lt with insert k' a' l
insert k' a' (node {m = m} {n = n} k a l r {or₂ p}) | lt | or₁ l' with (compare (suc m) (3 * n) , compare n (3 * (suc m)))
insert k' a' (node {m = m} {n = n} k a l r {or₂ p}) | lt | or₁ l' | (gt , _) = {!   !}
insert k' a' (node {m = m} {n = n} k a l r {or₂ p}) | lt | or₁ l' | (_ , gt) = {!   !}
insert k' a' (node {m = m} {n = n} k a l r {or₂ (p₁ & p₂)}) | lt | or₁ l'@(node _ _ ll' lr' {or₁ lp'}) | _ = or₁ (node k a l' r {thm68 {size ll'} {size lr'} {n} (thm38 {n} {m} {size ll'} {size lr'} (thm69 {n} {size ll'} p₂) (thm70 {size ll'} {size lr'} {n} p₁) lp' refl)})
insert k' a' (node {m = m} {n = n} k a l r {or₂ (p₁ & p₂)}) | lt | or₁ l'@(node _ _ ll' lr' {or₂ lp'}) | _ = {!   !}
insert k' a' (node {m = m} {n = n} k a l r {or₂ p}) | lt | or₂ l' = or₂ (node k a l' r {or₂ p})
insert k' a' (node {m = m} {n = n} k a tip tip {or₂ p}) | gt = or₁ (node k a tip (node k' a' tip tip {or₁ (look₁ refl)}) {or₁ (look₂ refl)})
insert k' a' (node {m = m} {n = n} k a tip (node _ _ _ _) {or₂ (x & look₁ ())}) | gt
insert k' a' (node {m = m} {n = n} k a tip (node _ _ _ _) {or₂ (x & look₂ ())}) | gt
insert k' a' (node {m = m} {n = n} k a l@(node _ _ tip tip) tip {or₂ p}) | gt = or₁ (node k a l (node k' a' tip tip {or₁ (look₁ refl)}) {or₂ (look₁ refl & look₁ refl)})
insert k' a' (node {m = m} {n = n} k a (node _ _ tip lr@(node _ _ _ _)) tip {or₂ (look₁ () & x₁)}) | gt
insert k' a' (node {m = m} {n = n} k a (node _ _ tip lr@(node _ _ _ _)) tip {or₂ (look₂ () & x₁)}) | gt
insert k' a' (node {m = m} {n = n} k a (node _ _ ll@(node _ _ _ _) tip) tip {or₂ (look₁ () & x₁)}) | gt
insert k' a' (node {m = m} {n = n} k a (node _ _ ll@(node _ _ _ _) tip) tip {or₂ (look₂ () & x₁)}) | gt
insert k' a' (node {m = m} {n = n} k a (node _ _ (node _ _ _ _) (node _ _ _ _)) tip {or₂ (look₁ () & x₁)}) | gt
insert k' a' (node {m = m} {n = n} k a (node _ _ (node _ _ _ _) (node _ _ _ _)) tip {or₂ (look₂ () & x₁)}) | gt
insert k' a' (node {m = m} {n = n} k a l@(node _ _ _ _) r@(node _ _ _ _) {or₂ p}) | gt with insert k' a' r
insert k' a' (node {m = m} {n = n} k a l@(node _ _ _ _) r@(node _ _ _ _) {or₂ p}) | gt | or₁ r' with (compare m (3 * (suc n)) , compare (suc n) (3 * m))
insert k' a' (node {m = m} {n = n} k a l@(node _ _ _ _) r@(node _ _ _ _) {or₂ p}) | gt | or₁ r' | (gt , _) = {!   !}
insert k' a' (node {m = m} {n = n} k a l@(node _ _ _ _) r@(node _ _ _ _) {or₂ p}) | gt | or₁ r' | (_ , gt) = {!   !}
insert k' a' (node {m = m} {n = n} k a l@(node _ _ ll lr) r@(node _ _ rl rr) {or₂ (p₁ & p₂)}) | gt | or₁ r' | _ = or₁ (thm72 (cong suc (cong suc (thm73 {size ll} {size lr} {size rl} {size rr}))) (node k a l r' {or₂ (thm25 {!   !} & {!   !})}))
insert k' a' (node {m = m} {n = n} k a l@(node _ _ _ _) r@(node _ _ _ _) {or₂ p}) | gt | or₂ r' = or₂ (node k a l r' {or₂ p})









-- insert k' a' tip = or₁ (node k' a' tip tip {or₁ (look₁ refl)})
-- insert k' a' (node k a l r {or₁ prf}) with compare k' k
-- insert k' a' (node k a l r {or₁ prf}) | eq = or₂ (node k a' l r {or₁ prf})

-- insert k' a' (node k a tip tip {or₁ prf}) | gt = or₁ (node k a tip (node k' a' tip tip {or₁ (look₁ refl)}) {or₁ (look₂ refl)})
-- insert k' a' (node k a tip (node rk ra tip tip) {or₁ prf}) | gt with compare k' rk
-- insert k' a' (node k a tip (node rk ra tip tip) {or₁ prf}) | gt | lt = or₁ (node k' a' (node k a tip tip {or₁ (look₁ refl)}) (node rk ra tip tip {or₁ (look₁ refl)}) {or₂ (look₁ refl & look₁ refl)})
-- insert k' a' (node k a tip (node rk ra tip tip) {or₁ prf}) | gt | gt = or₁ (node rk ra (node k a tip tip {or₁ (look₁ refl)}) (node k' a' tip tip {or₁ (look₁ refl)}) {or₂ (look₁ refl & look₁ refl)})
-- insert k' a' (node k a tip (node rk ra tip tip) {or₁ prf}) | gt | eq = or₂ (node k a tip (node rk a' tip tip {or₁ (look₁ refl)}) {or₁ prf})
-- insert k' a' (node k a tip (node rk ra tip (node _ _ _ _)) {or₁ (look₁ ())}) | gt
-- insert k' a' (node k a tip (node rk ra tip (node _ _ _ _)) {or₁ (look₂ ())}) | gt
-- insert k' a' (node k a tip (node rk ra (node _ _ _ _) tip) {or₁ (look₁ ())}) | gt
-- insert k' a' (node k a tip (node rk ra (node _ _ _ _) tip) {or₁ (look₂ ())}) | gt
-- insert k' a' (node k a tip (node rk ra (node x x₁ rl rl₁) (node x₂ x₃ rr rr₁)) {or₁ (look₁ ())}) | gt
-- insert k' a' (node k a tip (node rk ra (node x x₁ rl rl₁) (node x₂ x₃ rr rr₁)) {or₁ (look₂ ())}) | gt
-- insert k' a' (node k a l@(node _ _ _ _) tip {or₁ prf}) | gt = or₁ (node k a l (node k' a' tip tip {or₁ (look₁ refl)}) {or₂ (thm10 (thm10 prf) & thm7)})
-- insert k' a' (node k a (node lk la ll lr {or₁ lp}) (node rk ra rl rr {or₁ rp}) {or₁ prf}) | gt with compare k' rk
-- insert k' a' (node k a (node lk la ll lr {or₁ lp}) (node rk ra rl rr {or₁ rp}) {or₁ prf}) | gt | lt with insert k' a' rl
-- insert k' a' (node k a l@(node lk la ll lr {or₁ lp}) (node rk ra rl rr {or₁ (look₁ rp)}) {or₁ prf}) | gt | lt | or₁ rl' = or₁ ((node k a l (node rk ra rl' rr {or₁ (thm28 {size rl} {size rr} rp)}) {or₂ (thm25 (extend lp thm7) & thm25 (thm25 (extend (thm30 rp) thm7)))}))
-- insert k' a' (node k a (node lk la ll lr {or₁ lp}) (node rk ra rl rr {or₁ (look₂ rp)}) {or₁ (look₁ ())}) | gt | lt | or₁ rl'
-- insert k' a' (node k a (node lk la ll lr {or₁ lp}) (node rk ra rl rr {or₁ (look₂ rp)}) {or₁ (look₂ ())}) | gt | lt | or₁ rl'
-- insert k' a' (node k a l@(node lk la ll lr {or₁ lp}) (node rk ra rl rr {or₁ rp}) {or₁ prf}) | gt | lt | or₂ rl' = or₂ (node k a l (node rk ra rl' rr {or₁ rp}) {or₁ prf})
-- insert k' a' (node k a (node lk la ll lr {or₁ lp}) (node rk ra rl rr {or₁ rp}) {or₁ prf}) | gt | gt with insert k' a' rr
-- -- insert k' a' (node k a l@(node lk la ll lr {or₁ lp}) (node rk ra rl rr {or₁ (look₁ rp)}) {or₁ prf}) | gt | gt | or₁ rr' = or₁ (node k a l (node rk ra rl rr' {or₁ (thm28 {size rl} {size rr} rp)}) {or₂ ({!   !} & {!   !})})
-- insert k' a' (node k a (node lk la ll lr {or₁ lp}) (node rk ra rl rr {or₁ (look₁ rp)}) {or₁ (look₁ ())}) | gt | gt | or₁ rr'
-- insert k' a' (node k a (node lk la ll lr {or₁ lp}) (node rk ra rl rr {or₁ (look₁ rp)}) {or₁ (look₂ ())}) | gt | gt | or₁ rr'
-- insert k' a' (node k a (node lk la ll lr {or₁ lp}) (node rk ra rl rr {or₁ (look₂ rp)}) {or₁ (look₁ ())}) | gt | gt | or₁ rr'
-- insert k' a' (node k a (node lk la ll lr {or₁ lp}) (node rk ra rl rr {or₁ (look₂ rp)}) {or₁ (look₂ ())}) | gt | gt | or₁ rr'
-- insert k' a' (node k a (node lk la ll lr {or₁ lp}) (node rk ra rl rr {or₁ rp}) {or₁ (look₁ ())}) | gt | gt | or₂ rr'
-- insert k' a' (node k a (node lk la ll lr {or₁ lp}) (node rk ra rl rr {or₁ rp}) {or₁ (look₂ ())}) | gt | gt | or₂ rr'
-- insert k' a' (node k a l@(node lk la ll lr {or₁ lp}) (node rk ra rl rr {or₁ rp}) {or₁ prf}) | gt | eq = or₂ (node k a l (node rk a' rl rr {or₁ rp}) {or₁ prf})
-- insert k' a' (node k a (node lk la ll lr {or₁ lp}) (node rk ra rl rr {or₂ rp}) {or₁ (look₁ ())}) | gt
-- insert k' a' (node k a (node lk la ll lr {or₁ lp}) (node rk ra rl rr {or₂ rp}) {or₁ (look₂ ())}) | gt
-- insert k' a' (node k a (node lk la ll lr {or₂ lp}) (node rk ra rl rr {or₁ rp}) {or₁ (look₁ ())}) | gt
-- insert k' a' (node k a (node lk la ll lr {or₂ lp}) (node rk ra rl rr {or₁ rp}) {or₁ (look₂ ())}) | gt
-- insert k' a' (node k a (node lk la ll lr {or₂ lp}) (node rk ra rl rr {or₂ rp}) {or₁ (look₁ ())}) | gt
-- insert k' a' (node k a (node lk la ll lr {or₂ lp}) (node rk ra rl rr {or₂ rp}) {or₁ (look₂ ())}) | gt

-- insert k' a' (node k a l r {or₁ prf}) | lt with insert k' a' l
-- insert k' a' (node k a l r {or₁ (look₁ prf)}) | lt | or₁ l' = or₁ (node k a l' r {or₁ (thm28 {size l} {size r} prf)})
-- insert k' a' (node k a l r {or₁ (look₂ prf)}) | lt | or₁ l'@(node lk' la' ll' lr' {or₁ (look₁ lp')}) = or₁ (node k a l' r {or₂ (thm32 {size r} {size ll'} {size lr'} (thm31 {size ll'} {size lr'} {size r} prf (thm1 (thm13 (thm27 lp')))) (thm1 (thm13 (thm27 lp'))) & thm35 {1} {_} {_} (sym (thm31 {size ll'} {size lr'} {size r} prf (thm1 (thm13 (thm28 {size ll'} {size lr'} lp'))))) thm7)})
-- insert k' a' (node k a l tip {or₁ (look₂ ())}) | lt | or₁ l'@(node _ _ tip tip {or₁ (look₂ lp')})
-- insert k' a' (node k a l tip {or₁ (look₂ prf)}) | lt | or₁ l'@(node _ _ tip lr'@(node _ _ tip tip) {or₁ (look₂ lp')}) = {!   !}
-- insert k' a' (node k a l tip {or₁ (look₂ prf)}) | lt | or₁ l'@(node _ _ tip lr'@(node _ _ (node _ _ _ _) _) {or₁ (look₂ ())})
-- insert k' a' (node k a l tip {or₁ (look₂ ())}) | lt | or₁ l'@(node _ _ tip lr'@(node _ _ _ (node _ _ _ _)) {or₁ (look₂ lp')})
-- insert k' a' (node k a l tip {or₁ (look₂ prf)}) | lt | or₁ l'@(node _ _ ll'@(node _ _ _ _) tip {or₁ (look₂ lp')}) = {!   !}
-- insert k' a' (node k a l tip {or₁ (look₂ ())}) | lt | or₁ l'@(node _ _ ll'@(node _ _ _ _) lr'@(node _ _ _ _) {or₁ (look₂ lp')})
-- insert k' a' (node k a l (node _ _ _ _) {or₁ (look₂ prf)}) | lt | or₁ l'@(node _ _ tip tip {or₁ (look₂ ())})
-- insert k' a' (node k a l (node _ _ _ _) {or₁ (look₂ ())}) | lt | or₁ l'@(node _ _ ll'@(node _ _ _ _) tip {or₁ (look₂ lp')})
-- insert k' a' (node k a l (node _ _ _ _) {or₁ (look₂ ())}) | lt | or₁ l'@(node _ _ tip lr'@(node _ _ _ _) {or₁ (look₂ lp')})
-- insert k' a' (node k a l (node _ _ _ _) {or₁ (look₂ ())}) | lt | or₁ l'@(node _ _ ll'@(node _ _ _ _) lr'@(node _ _ _ _) {or₁ (look₂ lp')})
-- insert k' a' (node k a l r {or₁ (look₂ prf)}) | lt | or₁ l'@(node _ _ ll' lr' {or₂ (lp₁' & lp₂')}) = or₁ (node k a l' r {or₂ (thm32 {size r} {size ll'} {size lr'} (thm31 {size ll'} {size lr'} {_} prf (thm36 {size ll'} {size lr'} {size r} prf lp₂' lp₁')) (thm36 {size ll'} {size lr'} {size r} prf lp₂' lp₁') & thm35 {1} {_} {_} (sym (thm31 {size ll'} {size lr'} {size r} prf (thm36 {_} {_} {size r} prf lp₂' lp₁'))) thm7)})
-- insert k' a' (node k a l r {or₁ prf}) | lt | or₂ l' = or₂ (node k a l' r {or₁ prf})
-- insert k' a' (node k a l r {or₂ prf}) with compare k' k
-- insert k' a' (node k a l r {or₂ prf}) | eq = or₂ (node k a' l r {or₂ prf})
-- insert k' a' (node k a l r {or₂ prf}) | gt with insert k' a' r
-- insert k' a' (node k a l r {or₂ (prf₁ & prf₂)}) | gt | or₁ r'@(node _ _ tip tip {or₁ pr'}) = or₁ (node k a l r' {or₁ (thm25 prf₁)})
-- insert k' a' (node k a tip r {or₂ (prf₁ & look₁ ())}) | gt | or₁ r'@(node _ _ rl'@(node _ _ _ _) tip {or₁ pr'})
-- insert k' a' (node k a tip r {or₂ (prf₁ & look₂ ())}) | gt | or₁ r'@(node _ _ rl'@(node _ _ _ _) tip {or₁ pr'})
-- insert k' a' (node k a l@(node _ _ _ _) r {or₂ (prf₁ & prf₂)}) | gt | or₁ r'@(node _ _ rl'@(node _ _ rll' rlr') tip {or₁ pr'}) = or₁ (node k a l r' {or₂ (thm10 (thm10 (thm10 prf₁)) & extend (thm25 pr') (thm25 thm7))})
-- insert k' a' (node k a tip r {or₂ (prf₁ & look₁ ())}) | gt | or₁ r'@(node _ _ tip rr'@(node _ _ _ _) {or₁ pr'})
-- insert k' a' (node k a tip r {or₂ (prf₁ & look₂ ())}) | gt | or₁ r'@(node _ _ tip rr'@(node _ _ _ _) {or₁ pr'})
-- insert k' a' (node k a l@(node _ _ _ _) r {or₂ (prf₁ & prf₂)}) | gt | or₁ r'@(node _ _ tip rr'@(node _ _ _ _) {or₁ pr'}) = or₁ (node k a l r' {or₂ (thm10 (thm10 (thm10 prf₁)) & extend (thm25 pr') (thm25 thm7))})
-- insert k' a' (node k a tip r {or₂ (prf₁ & look₁ ())}) | gt | or₁ r'@(node _ _ rl'@(node _ _ _ _) rr'@(node _ _ _ _) {or₁ pr'})
-- insert k' a' (node k a tip r {or₂ (prf₁ & look₂ ())}) | gt | or₁ r'@(node _ _ rl'@(node _ _ _ _) rr'@(node _ _ _ _) {or₁ pr'})
-- insert k' a' (node k a l@(node _ _ _ _) r {or₂ (prf₁ & prf₂)}) | gt | or₁ r'@(node _ _ rl'@(node _ _ _ _) rr'@(node _ _ _ _) {or₁ pr'}) = or₁ (node k a l r' {or₂ (thm10 (thm10 (thm10 prf₁)) & extend (thm25 pr') (thm25 thm7))})
-- insert k' a' (node k a tip r {or₂ (prf₁ & prf₂)}) | gt | or₁ r'@(node _ _ tip tip {or₂ pr'}) = or₁ (node k a tip r' {or₁ (look₂ refl)})
-- insert k' a' (node k a tip r {or₂ (prf₁ & look₁ ())}) | gt | or₁ r'@(node _ _ tip rr'@(node _ _ _ _) {or₂ pr'})
-- insert k' a' (node k a tip r {or₂ (prf₁ & look₂ ())}) | gt | or₁ r'@(node _ _ tip rr'@(node _ _ _ _) {or₂ pr'})
-- insert k' a' (node k a tip r {or₂ (prf₁ & look₁ ())}) | gt | or₁ r'@(node _ _ rl'@(node _ _ _ _) tip {or₂ pr'})
-- insert k' a' (node k a tip r {or₂ (prf₁ & look₂ ())}) | gt | or₁ r'@(node _ _ rl'@(node _ _ _ _) tip {or₂ pr'})
-- insert k' a' (node k a tip r {or₂ (prf₁ & look₁ ())}) | gt | or₁ r'@(node _ _ rl'@(node _ _ _ _) rr'@(node _ _ _ _) {or₂ pr'})
-- insert k' a' (node k a tip r {or₂ (prf₁ & look₂ ())}) | gt | or₁ r'@(node _ _ rl'@(node _ _ _ _) rr'@(node _ _ _ _) {or₂ pr'})
-- insert k' a' (node k a l@(node _ _ _ _) r {or₂ (prf₁ & prf₂)}) | gt | or₁ r'@(node _ _ tip tip {or₂ pr'}) = or₁ (node k a l r' {or₂ (thm10 (thm10 (thm10 prf₁)) & thm7)})
-- insert k' a' (node k a (node _ _ ll lr) r {or₂ (prf₁ & prf₂)}) | gt | or₁ r'@(node _ _ tip rr'@(node _ _ _ _) {or₂ (x & look₁ ())})
-- insert k' a' (node k a (node _ _ ll lr) r {or₂ (prf₁ & prf₂)}) | gt | or₁ r'@(node _ _ tip rr'@(node _ _ _ _) {or₂ (x & look₂ ())})
-- insert k' a' (node k a (node _ _ _ _) r {or₂ (prf₁ & prf₂)}) | gt | or₁ r'@(node _ _ rl'@(node _ _ _ _) tip {or₂ (look₁ () & x₁)})
-- insert k' a' (node k a (node _ _ _ _) r {or₂ (prf₁ & prf₂)}) | gt | or₁ r'@(node _ _ rl'@(node _ _ _ _) tip {or₂ (look₂ () & x₁)})
-- insert k' a' (node k a l@(node _ _ _ _) r {or₂ (prf₁ & prf₂)}) | gt | or₁ r'@(node _ _ rl'@(node _ _ _ _) rr'@(node _ _ _ _) {or₂ pr'}) = or₁ (node k a l r' {or₂ (thm10 (thm10 (thm10 prf₁)) & thm25 {!   !})})
-- insert k' a' (node k a l r {or₂ prf}) | gt | or₂ r'@(node _ _ _ _) = or₂ (node k a l r' {or₂ prf})
-- insert k' a' (node k a l r {or₂ (x & x₁)}) | gt | or₂ tip = or₂ (node k a l tip {or₁ (thm10 x)})

-- insert k' a' (node k a l r {or₂ prf}) | lt with insert k' a' l
-- insert k' a' (node k a l tip {or₂ prf}) | lt | or₁ l'@(node _ _ ll' lr' {or₁ (look₁ lp')}) = or₁ (node k a l' tip {or₁ (thm28 {size ll'} {size lr'} lp')})
-- insert k' a' (node k a l r@(node _ _ _ _) {or₂ (prf₁ & prf₂)}) | lt | or₁ l'@(node _ _ ll' lr' {or₁ (look₁ lp')}) = or₁ (node k a l' r {or₂ (extend (thm25 (thm37 lp')) (thm25 thm7) & thm10 (thm10 (thm10 prf₂)))})
-- insert k' a' (node k a l tip {or₂ (look₁ () & prf₂)}) | lt | or₁ l'@(node _ _ tip (node x x₁ lr' lr'') {or₁ (look₂ lp')})
-- insert k' a' (node k a l tip {or₂ (look₂ () & prf₂)}) | lt | or₁ l'@(node _ _ tip (node x x₁ lr' lr'') {or₁ (look₂ lp')})
-- insert k' a' (node k a l tip {or₂ (look₁ () & prf₂)}) | lt | or₁ l'@(node _ _ (node x x₁ ll' ll'') tip {or₁ (look₂ lp')})
-- insert k' a' (node k a l tip {or₂ (look₂ () & prf₂)}) | lt | or₁ l'@(node _ _ (node x x₁ ll' ll'') tip {or₁ (look₂ lp')})
-- insert k' a' (node k a l r@(node _ _ _ _) {or₂ (prf₁ & prf₂)}) | lt | or₁ l'@(node _ _ _ _ {or₁ (look₂ lp')}) = {!   !}
-- insert k' a' (node k a l tip {or₂ (prf₁ & prf₂)}) | lt | or₁ l'@(node _ _ tip tip {or₂ (lp₁' & lp₂')}) = or₁ (node k a l' tip {or₁ (look₂ refl)})
-- insert k' a' (node k a l tip {or₂ ((look₁ ()) & prf₂)}) | lt | or₁ l'@(node _ _ _ (node _ _ _ _) {or₂ (lp₁' & lp₂')})
-- insert k' a' (node k a l tip {or₂ ((look₂ ()) & prf₂)}) | lt | or₁ l'@(node _ _ _ (node _ _ _ _) {or₂ (lp₁' & lp₂')})
-- insert k' a' (node k a l tip {or₂ ((look₁ ()) & prf₂)}) | lt | or₁ l'@(node _ _ (node _ _ _ _) _ {or₂ (lp₁' & lp₂')})
-- insert k' a' (node k a l tip {or₂ ((look₂ ()) & prf₂)}) | lt | or₁ l'@(node _ _ (node _ _ _ _) _ {or₂ (lp₁' & lp₂')})
-- insert k' a' (node k a l r@(node _ _ _ _) {or₂ (prf₁ & prf₂)}) | lt | or₁ l'@(node _ _ _ _ {or₂ (lp₁' & lp₂')}) = {!   !}
-- insert k' a' (node k a l r {or₂ (prf₁ & prf₂)}) | lt | or₂ tip = or₂ (node k a tip r {or₁ (thm10 prf₂)})
-- insert k' a' (node k a l r {or₂ (prf₁ & prf₂)}) | lt | or₂ l'@(node _ _ _ _ {lp'}) = or₂ (node k a l' r {or₂ (prf₁ & prf₂)})