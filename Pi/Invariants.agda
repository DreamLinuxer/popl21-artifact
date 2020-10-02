module Pi.Invariants where
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.List as L hiding (_∷_)
open import Relation.Binary.PropositionalEquality
open import Pi.Syntax
open import Pi.Opsem
open import Pi.NoRepeat

-- Get the type of the deepest context
get𝕌 : ∀ {A B} → Context {A} {B} → 𝕌 × 𝕌
get𝕌 {A} {B} ☐ = A , B
get𝕌 (☐⨾ c₂ • κ) = get𝕌 κ
get𝕌 (c₁ ⨾☐• κ) = get𝕌 κ
get𝕌 (☐⊕ c₂ • κ) = get𝕌 κ
get𝕌 (c₁ ⊕☐• κ) = get𝕌 κ
get𝕌 (☐⊗[ c₂ , x ]• κ) = get𝕌 κ
get𝕌 ([ c₁ , x ]⊗☐• κ) = get𝕌 κ

get𝕌State : (st : State) → 𝕌 × 𝕌
get𝕌State ⟨ c ∣ v ∣ κ ⟩ = get𝕌 κ
get𝕌State ［ c ∣ v ∣ κ ］ = get𝕌 κ

-- Reconstruct the whole combinator from context
getℂκ : ∀ {A B} → A ↔ B → Context {A} {B} → ∃[ C ] ∃[ D ] (C ↔ D)
getℂκ c ☐ = _ , _ , c
getℂκ c (☐⨾ c₂ • κ) = getℂκ (c ⨾ c₂) κ
getℂκ c (c₁ ⨾☐• κ) = getℂκ (c₁ ⨾ c) κ
getℂκ c (☐⊕ c₂ • κ) = getℂκ (c ⊕ c₂) κ
getℂκ c (c₁ ⊕☐• κ) = getℂκ (c₁ ⊕ c) κ
getℂκ c (☐⊗[ c₂ , x ]• κ) = getℂκ (c ⊗ c₂) κ
getℂκ c ([ c₁ , x ]⊗☐• κ) = getℂκ (c₁ ⊗ c) κ

getℂ : State → ∃[ A ] ∃[ B ] (A ↔ B)
getℂ ⟨ c ∣ _ ∣ κ ⟩ = getℂκ c κ
getℂ ［ c ∣ _ ∣ κ ］ = getℂκ c κ

-- The reconstructed combinator stays the same
ℂInvariant : ∀ {st st'} → st ↦ st' → getℂ st ≡  getℂ st'
ℂInvariant ↦₁ = refl
ℂInvariant ↦₂ = refl
ℂInvariant ↦₃ = refl
ℂInvariant ↦₄ = refl
ℂInvariant ↦₅ = refl
ℂInvariant ↦₆ = refl
ℂInvariant ↦₇ = refl
ℂInvariant ↦₈ = refl
ℂInvariant ↦₉ = refl
ℂInvariant ↦₁₀ = refl
ℂInvariant ↦₁₁ = refl
ℂInvariant ↦₁₂ = refl

ℂInvariant* : ∀ {st st'} → st ↦* st' → getℂ st ≡  getℂ st'
ℂInvariant* ◾ = refl
ℂInvariant* (r ∷ rs) = trans (ℂInvariant r) (ℂInvariant* rs)

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

appendκState : ∀ st → let (A , B) = get𝕌State st
                      in  Context {A} {B} → State
appendκState ⟨ c ∣ v ∣ κ ⟩ ctx = ⟨ c ∣ v ∣ appendκ κ ctx ⟩
appendκState ［ c ∣ v ∣ κ ］ ctx = ［ c ∣ v ∣ appendκ κ ctx ］

-- The type of context does not change during execution
𝕌Invariant : ∀ {st st'} → st ↦ st' → get𝕌State st ≡ get𝕌State st'
𝕌Invariant ↦₁  = refl
𝕌Invariant ↦₂  = refl
𝕌Invariant ↦₃  = refl
𝕌Invariant ↦₄  = refl
𝕌Invariant ↦₅  = refl
𝕌Invariant ↦₆  = refl
𝕌Invariant ↦₇  = refl
𝕌Invariant ↦₈  = refl
𝕌Invariant ↦₉  = refl
𝕌Invariant ↦₁₀ = refl
𝕌Invariant ↦₁₁ = refl
𝕌Invariant ↦₁₂ = refl

𝕌Invariant* : ∀ {st st'} → st ↦* st' → get𝕌State st ≡ get𝕌State st'
𝕌Invariant* ◾ = refl
𝕌Invariant* (r ∷ rs) = trans (𝕌Invariant r) (𝕌Invariant* rs)

-- Appending context does not affect reductions
appendκ↦ : ∀ {st st'} → (r : st ↦ st') (eq : get𝕌State st ≡  get𝕌State st')
         → (κ : Context {proj₁ (get𝕌State st)} {proj₂ (get𝕌State st)})
         → appendκState st κ ↦ appendκState st' (subst (λ {(A , B) → Context {A} {B}}) eq κ)
appendκ↦ ↦₁ refl κ = ↦₁
appendκ↦ ↦₂ refl κ = ↦₂
appendκ↦ ↦₃ refl κ = ↦₃
appendκ↦ ↦₄ refl κ = ↦₄
appendκ↦ ↦₅ refl κ = ↦₅
appendκ↦ ↦₆ refl κ = ↦₆
appendκ↦ ↦₇ refl κ = ↦₇
appendκ↦ ↦₈ refl κ = ↦₈
appendκ↦ ↦₉ refl κ = ↦₉
appendκ↦ ↦₁₀ refl κ = ↦₁₀
appendκ↦ ↦₁₁ refl κ = ↦₁₁
appendκ↦ ↦₁₂ refl κ = ↦₁₂

appendκ↦* : ∀ {st st'} → (rs : st ↦* st') (eq : get𝕌State st ≡  get𝕌State st')
          → (κ : Context {proj₁ (get𝕌State st)} {proj₂ (get𝕌State st)})
          → appendκState st κ ↦* appendκState st' (subst (λ {(A , B) → Context {A} {B}}) eq κ)
appendκ↦* ◾ refl ctx = ◾
appendκ↦* (↦₁ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦₁ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦₂ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦₂ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦₃ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦₃ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦₄ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦₄ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦₅ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦₅ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦₆ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦₆ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦₇ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦₇ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦₈ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦₈ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦₉ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦₉ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦₁₀{κ = κ} ∷ rs) eq ctx = appendκ↦ (↦₁₀ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦₁₁{κ = κ} ∷ rs) eq ctx = appendκ↦ (↦₁₁ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦₁₂{κ = κ} ∷ rs) eq ctx = appendκ↦ (↦₁₂ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
