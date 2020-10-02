module PiFrac.Invariants where
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Sum
open import Data.Product
open import Relation.Binary.Core
open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Maybe
open import PiFrac.Syntax
open import PiFrac.Opsem
open import PiFrac.NoRepeat

-- Get the type of the deepest context
get𝕌 : ∀ {A B} → Context {A} {B} → 𝕌 × 𝕌
get𝕌 {A} {B} ☐ = A , B
get𝕌 (☐⨾ c₂ • κ) = get𝕌 κ
get𝕌 (c₁ ⨾☐• κ) = get𝕌 κ
get𝕌 (☐⊕ c₂ • κ) = get𝕌 κ
get𝕌 (c₁ ⊕☐• κ) = get𝕌 κ
get𝕌 (☐⊗[ c₂ , x ]• κ) = get𝕌 κ
get𝕌 ([ c₁ , x ]⊗☐• κ) = get𝕌 κ

get𝕌State : (st : State) → st ≢ ⊠ → 𝕌 × 𝕌
get𝕌State ⟨ c ∣ v ∣ κ ⟩ _ = get𝕌 κ
get𝕌State ［ c ∣ v ∣ κ ］ _ = get𝕌 κ
get𝕌State ⊠ nf = ⊥-elim (nf refl)

-- Append a context to another context
appendκ : ∀ {A B} → (ctx : Context {A} {B}) → let (C , D) = get𝕌  ctx
                                              in  Context {C} {D} → Context {A} {B}
appendκ ☐ ctx = ctx
appendκ (☐⨾ c₂ • κ) ctx = ☐⨾ c₂ • appendκ κ ctx
appendκ (c₁ ⨾☐• κ) ctx = c₁ ⨾☐• appendκ κ ctx
appendκ (☐⊕ c₂ • κ) ctx = ☐⊕ c₂ • appendκ κ ctx
appendκ (c₁ ⊕☐• κ) ctx = c₁ ⊕☐• appendκ κ ctx
appendκ (☐⊗[ c₂ , x ]• κ) ctx = ☐⊗[ c₂ , x ]• appendκ κ ctx
appendκ ([ c₁ , x ]⊗☐• κ) ctx = [ c₁ , x ]⊗☐• appendκ κ ctx

appendκState : ∀ st → (nf : st ≢ ⊠)
             → let (A , B) = get𝕌State st nf
               in  Context {A} {B} → State
appendκState ⟨ c ∣ v ∣ κ ⟩ _ ctx = ⟨ c ∣ v ∣ appendκ κ ctx ⟩
appendκState ［ c ∣ v ∣ κ ］ _ ctx = ［ c ∣ v ∣ appendκ κ ctx ］
appendκState ⊠ nf = ⊥-elim (nf refl)

-- The type of context does not change during execution
𝕌Invariant : ∀ {st st'} → st ↦ st' → (nf : st ≢ ⊠) → (nf' : st' ≢ ⊠) → get𝕌State st nf ≡ get𝕌State st' nf'
𝕌Invariant ↦₁ nf nf' = refl
𝕌Invariant ↦₂ nf nf' = refl
𝕌Invariant ↦₃ nf nf' = refl
𝕌Invariant ↦₄ nf nf' = refl
𝕌Invariant ↦₅ nf nf' = refl
𝕌Invariant ↦₆ nf nf' = refl
𝕌Invariant ↦₇ nf nf' = refl
𝕌Invariant ↦₈ nf nf' = refl
𝕌Invariant ↦₉ nf nf' = refl
𝕌Invariant ↦₁₀ nf nf' = refl
𝕌Invariant ↦₁₁ nf nf' = refl
𝕌Invariant ↦₁₂ nf nf' = refl
𝕌Invariant ↦η nf nf' = refl
𝕌Invariant ↦ε₁ nf nf' = refl
𝕌Invariant ↦ε₂ nf nf' = ⊥-elim (nf' refl)

𝕌Invariant* : ∀ {st st'} → st ↦* st' → (nf : st ≢ ⊠) → (nf' : st' ≢ ⊠) → get𝕌State st nf ≡  get𝕌State st' nf'
𝕌Invariant* {⟨ _ ∣ _ ∣ _ ⟩} ◾ nf nf' = refl
𝕌Invariant* {［ _ ∣ _ ∣ _ ］} ◾ nf nf' = refl
𝕌Invariant* {⊠} nf nf' = ⊥-elim (nf' refl)
𝕌Invariant* (r ∷ ◾) nf nf' = 𝕌Invariant r nf nf'
𝕌Invariant* (r ∷ (r' ∷ rs)) nf nf' = trans (𝕌Invariant r nf nf'') (𝕌Invariant* (r' ∷ rs) nf'' nf')
  where
  nf'' = λ eq → ⊠-is-stuck eq (_ , r')

appendκ↦ : ∀ {st st'} → (r : st ↦ st') (nf : st ≢ ⊠) (nf' : st' ≢ ⊠) (eq : get𝕌State st nf ≡  get𝕌State st' nf')
         → (κ : Context {proj₁ (get𝕌State st nf)} {proj₂ (get𝕌State st nf)})
         → appendκState st nf κ ↦ appendκState st' nf' (subst (λ {(A , B) → Context {A} {B}}) eq κ)
appendκ↦ ↦₁ nf nf' refl ctx = ↦₁
appendκ↦ ↦₂ nf nf' refl ctx = ↦₂
appendκ↦ ↦₃ nf nf' refl ctx = ↦₃
appendκ↦ ↦₄ nf nf' refl ctx = ↦₄
appendκ↦ ↦₅ nf nf' refl ctx = ↦₅
appendκ↦ ↦₆ nf nf' refl ctx = ↦₆
appendκ↦ ↦₇ nf nf' refl ctx = ↦₇
appendκ↦ ↦₈ nf nf' refl ctx = ↦₈
appendκ↦ ↦₉ nf nf' refl ctx = ↦₉
appendκ↦ ↦₁₀ nf nf' refl ctx = ↦₁₀
appendκ↦ ↦₁₁ nf nf' refl ctx = ↦₁₁
appendκ↦ ↦₁₂ nf nf' refl ctx = ↦₁₂
appendκ↦ ↦η nf nf' refl ctx = ↦η
appendκ↦ (↦ε₁ {eq = eq}) nf nf' refl ctx = ↦ε₁ {eq = eq}
appendκ↦ ↦ε₂ nf nf' eq ctx = ⊥-elim (nf' refl)

appendκ↦* : ∀ {st st'} → (r : st ↦* st') (nf : st ≢ ⊠) (nf' : st' ≢ ⊠) (eq : get𝕌State st nf ≡  get𝕌State st' nf')
          → (κ : Context {proj₁ (get𝕌State st nf)} {proj₂ (get𝕌State st nf)})
          → appendκState st nf κ ↦* appendκState st' nf' (subst (λ {(A , B) → Context {A} {B}}) eq κ)
appendκ↦* {⟨ _ ∣ _ ∣ _ ⟩} ◾ nf nf' refl ctx = ◾
appendκ↦* {［ _ ∣ _ ∣ _ ］} ◾ nf nf' refl ctx = ◾
appendκ↦* {⊠} ◾ nf nf' eq ctx = ⊥-elim (nf' refl)
appendκ↦* (↦₁ {κ = κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦₁ {κ = κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦₂ ∷ rs) nf nf' eq ctx = appendκ↦ ↦₂ nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦₃ ∷ rs) nf nf' eq ctx = appendκ↦ ↦₃ nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦₄ ∷ rs) nf nf' eq ctx = appendκ↦ ↦₄ nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦₅ ∷ rs) nf nf' eq ctx = appendκ↦ ↦₅ nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦₆ ∷ rs) nf nf' eq ctx = appendκ↦ ↦₆ nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦₇ ∷ rs) nf nf' eq ctx = appendκ↦ ↦₇ nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦₈ ∷ rs) nf nf' eq ctx = appendκ↦ ↦₈ nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦₉ ∷ rs) nf nf' eq ctx = appendκ↦ ↦₉ nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦₁₀ ∷ rs) nf nf' eq ctx = appendκ↦ ↦₁₀ nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦₁₁ ∷ rs) nf nf' eq ctx = appendκ↦ ↦₁₁ nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦₁₂ ∷ rs) nf nf' eq ctx = appendκ↦ ↦₁₂ nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦η ∷ rs) nf nf' eq ctx = appendκ↦ ↦η nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦ε₁ {eq = eq'} ∷ rs) nf nf' eq ctx = appendκ↦ (↦ε₁ {eq = eq'}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦ε₂ ∷ ◾) nf nf' eq ctx = ⊥-elim (nf' refl)
appendκ↦* (↦ε₂ ∷ (r ∷ rs)) nf nf' eq ctx = ⊥-elim (⊠-is-stuck refl (_ , r))

appendκ↦⊠ : ∀ {st} → (r : st ↦ ⊠) (nf : st ≢ ⊠)
          → (κ : Context {proj₁ (get𝕌State st nf)} {proj₂ (get𝕌State st nf)})
          → appendκState st nf κ ↦ ⊠
appendκ↦⊠ (↦ε₂ {neq = neq}) nf ctx = ↦ε₂ {neq = neq}

appendκ↦*⊠ : ∀ {st} → (r : st ↦* ⊠) (nf : st ≢ ⊠)
           → (κ : Context {proj₁ (get𝕌State st nf)} {proj₂ (get𝕌State st nf)})
           → appendκState st nf κ ↦* ⊠
appendκ↦*⊠ ◾ nf ctx = ⊥-elim (nf refl)
appendκ↦*⊠ (r ∷ ◾) nf ctx = appendκ↦⊠ r nf ctx ∷ ◾
appendκ↦*⊠ (↦₁ ∷ (r' ∷ rs)) nf ctx = ↦₁ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦₂ ∷ (r' ∷ rs)) nf ctx = ↦₂ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦₃ ∷ (r' ∷ rs)) nf ctx = ↦₃ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦₄ ∷ (r' ∷ rs)) nf ctx = ↦₄ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦₅ ∷ (r' ∷ rs)) nf ctx = ↦₅ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦₆ ∷ (r' ∷ rs)) nf ctx = ↦₆ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦₇ ∷ (r' ∷ rs)) nf ctx = ↦₇ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦₈ ∷ (r' ∷ rs)) nf ctx = ↦₈ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦₉ ∷ (r' ∷ rs)) nf ctx = ↦₉ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦₁₀ ∷ (r' ∷ rs)) nf ctx = ↦₁₀ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦₁₁ ∷ (r' ∷ rs)) nf ctx = ↦₁₁ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦₁₂ ∷ (r' ∷ rs)) nf ctx = ↦₁₂ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦η ∷ (r' ∷ rs)) nf ctx = ↦η ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦ε₁ {eq = eq} ∷ (r' ∷ rs)) nf ctx = ↦ε₁ {eq = eq} ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
