module PiQ.Invariants where
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.Core
open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties
open import Function using (_∘_)
open import PiQ.Syntax
open import PiQ.Opsem
open import PiQ.NoRepeat

-- Reconstruct the whole combinator from context
getℂκ : ∀ {A B} → A ↔ B → Context {A} {B} → ∃[ C ] ∃[ D ] (C ↔ D)
getℂκ c ☐ = _ , _ , c
getℂκ c (☐⨾ c₂ • κ) = getℂκ (c ⨾ c₂) κ
getℂκ c (c₁ ⨾☐• κ) = getℂκ (c₁ ⨾ c) κ
getℂκ c (☐⊕ c₂ • κ) = getℂκ (c ⊕ c₂) κ
getℂκ c (c₁ ⊕☐• κ) = getℂκ (c₁ ⊕ c) κ
getℂκ c (☐⊗[ c₂ , x ]• κ) = getℂκ (c ⊗ c₂) κ
getℂκ c ([ c₁ , x ]⊗☐• κ) = getℂκ (c₁ ⊗ c) κ

getℂ : (st : State) → st ≢ ⊠ → ∃[ A ] ∃[ B ] (A ↔ B)
getℂ ⟨ c ∣ _ ∣ κ ⟩▷  _ = getℂκ c κ
getℂ ［ c ∣ _ ∣ κ ］▷ _ = getℂκ c κ
getℂ ⟨ c ∣ _ ∣ κ ⟩◁ _ = getℂκ c κ
getℂ ［ c ∣ _ ∣ κ ］◁ _ = getℂκ c κ
getℂ ⊠ st≢⊠ = ⊥-elim (st≢⊠ refl)

-- The reconstructed combinator stays the same
ℂInvariant : ∀ {st st'} → st ↦ st' → (¬fail : st ≢ ⊠) → (¬fail' : st' ≢ ⊠) → getℂ st ¬fail ≡ getℂ st' ¬fail'
ℂInvariant ↦⃗₁ _ _ = refl
ℂInvariant ↦⃗₂ _ _ = refl
ℂInvariant ↦⃗₃ _ _ = refl
ℂInvariant ↦⃗₄ _ _ = refl
ℂInvariant ↦⃗₅ _ _ = refl
ℂInvariant ↦⃗₆ _ _ = refl
ℂInvariant ↦⃗₇ _ _ = refl
ℂInvariant ↦⃗₈ _ _ = refl
ℂInvariant ↦⃗₉ _ _ = refl
ℂInvariant ↦⃗₁₀ _ _ = refl
ℂInvariant ↦⃗₁₁ _ _ = refl
ℂInvariant ↦⃗₁₂ _ _ = refl
ℂInvariant ↦⃖₁ _ _ = refl
ℂInvariant ↦⃖₂ _ _ = refl
ℂInvariant ↦⃖₃ _ _ = refl
ℂInvariant ↦⃖₄ _ _ = refl
ℂInvariant ↦⃖₅ _ _ = refl
ℂInvariant ↦⃖₆ _ _ = refl
ℂInvariant ↦⃖₇ _ _ = refl
ℂInvariant ↦⃖₈ _ _ = refl
ℂInvariant ↦⃖₉ _ _ = refl
ℂInvariant ↦⃖₁₀ _ _ = refl
ℂInvariant ↦⃖₁₁ _ _ = refl
ℂInvariant ↦⃖₁₂ _ _ = refl
ℂInvariant ↦η₊₁ _ _ = refl
ℂInvariant ↦η₊₂ _ _ = refl
ℂInvariant ↦ε₊₁ _ _ = refl
ℂInvariant ↦ε₊₂ _ _ = refl
ℂInvariant ↦⃗ηₓ _ _ = refl
ℂInvariant ↦⃖ηₓ₁ _ _ = refl
ℂInvariant ↦⃖ηₓ₂ _ ¬fail' = ⊥-elim (¬fail' refl)
ℂInvariant ↦⃗εₓ₁ _ _ = refl
ℂInvariant ↦⃗εₓ₂ _ ¬fail' = ⊥-elim (¬fail' refl)
ℂInvariant ↦⃖εₓ _ _ = refl

ℂInvariant* : ∀ {st st'} → st ↦* st' → (¬fail : st ≢ ⊠) → (¬fail' : st' ≢ ⊠) → getℂ st ¬fail ≡ getℂ st' ¬fail'
ℂInvariant* {⟨ _ ∣ _ ∣ _ ⟩▷} ◾ _ _ = refl
ℂInvariant* {［ _ ∣ _ ∣ _ ］▷} ◾ _ _ = refl
ℂInvariant* {⟨ _ ∣ _ ∣ _ ⟩◁} ◾ _ _ = refl
ℂInvariant* {［ _ ∣ _ ∣ _ ］◁} ◾ _ _ = refl
ℂInvariant* {⊠} ◾ ¬fail _ = ⊥-elim (¬fail refl)
ℂInvariant* (r ∷ ◾) ¬fail ¬fail' = ℂInvariant r ¬fail ¬fail'
ℂInvariant* (r ∷ (r' ∷ rs)) ¬fail ¬fail' = trans (ℂInvariant r ¬fail λ {refl → ⊠-is-stuck refl (_ , r')})
                                                 (ℂInvariant* (r' ∷ rs) _ ¬fail')

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
get𝕌State ⟨ c ∣ v ∣ κ ⟩▷ _ = get𝕌 κ
get𝕌State ［ c ∣ v ∣ κ ］▷ _ = get𝕌 κ
get𝕌State ⟨ c ∣ v ∣ κ ⟩◁ _ = get𝕌 κ
get𝕌State ［ c ∣ v ∣ κ ］◁ _ = get𝕌 κ
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
appendκState ⟨ c ∣ v ∣ κ ⟩▷ _ ctx = ⟨ c ∣ v ∣ appendκ κ ctx ⟩▷
appendκState ［ c ∣ v ∣ κ ］▷ _ ctx = ［ c ∣ v ∣ appendκ κ ctx ］▷
appendκState ⟨ c ∣ v ∣ κ ⟩◁ _ ctx = ⟨ c ∣ v ∣ appendκ κ ctx ⟩◁
appendκState ［ c ∣ v ∣ κ ］◁ _ ctx = ［ c ∣ v ∣ appendκ κ ctx ］◁
appendκState ⊠ nf = ⊥-elim (nf refl)

-- The type of context does not change during execution
𝕌Invariant : ∀ {st st'} → st ↦ st' → (nf : st ≢ ⊠) → (nf' : st' ≢ ⊠) → get𝕌State st nf ≡ get𝕌State st' nf'
𝕌Invariant ↦⃗₁ nf nf' = refl
𝕌Invariant ↦⃗₂ nf nf' = refl
𝕌Invariant ↦⃗₃ nf nf' = refl
𝕌Invariant ↦⃗₄ nf nf' = refl
𝕌Invariant ↦⃗₅ nf nf' = refl
𝕌Invariant ↦⃗₆ nf nf' = refl
𝕌Invariant ↦⃗₇ nf nf' = refl
𝕌Invariant ↦⃗₈ nf nf' = refl
𝕌Invariant ↦⃗₉ nf nf' = refl
𝕌Invariant ↦⃗₁₀ nf nf' = refl
𝕌Invariant ↦⃗₁₁ nf nf' = refl
𝕌Invariant ↦⃗₁₂ nf nf' = refl
𝕌Invariant ↦⃖₁ nf nf' = refl
𝕌Invariant ↦⃖₂ nf nf' = refl
𝕌Invariant ↦⃖₃ nf nf' = refl
𝕌Invariant ↦⃖₄ nf nf' = refl
𝕌Invariant ↦⃖₅ nf nf' = refl
𝕌Invariant ↦⃖₆ nf nf' = refl
𝕌Invariant ↦⃖₇ nf nf' = refl
𝕌Invariant ↦⃖₈ nf nf' = refl
𝕌Invariant ↦⃖₉ nf nf' = refl
𝕌Invariant ↦⃖₁₀ nf nf' = refl
𝕌Invariant ↦⃖₁₁ nf nf' = refl
𝕌Invariant ↦⃖₁₂ nf nf' = refl
𝕌Invariant ↦η₊₁ nf nf' = refl
𝕌Invariant ↦η₊₂ nf nf' = refl
𝕌Invariant ↦ε₊₁ nf nf' = refl
𝕌Invariant ↦ε₊₂ nf nf' = refl
𝕌Invariant ↦⃗ηₓ nf nf' = refl
𝕌Invariant ↦⃖ηₓ₁ nf nf' = refl
𝕌Invariant ↦⃖ηₓ₂ nf nf' = ⊥-elim (nf' refl)
𝕌Invariant ↦⃗εₓ₁ nf nf' = refl
𝕌Invariant ↦⃗εₓ₂ nf nf' = ⊥-elim (nf' refl)
𝕌Invariant ↦⃖εₓ nf nf' = refl

𝕌Invariant* : ∀ {st st'} → st ↦* st' → (nf : st ≢ ⊠) → (nf' : st' ≢ ⊠) → get𝕌State st nf ≡  get𝕌State st' nf'
𝕌Invariant* {⟨ _ ∣ _ ∣ _ ⟩▷} ◾ nf nf' = refl
𝕌Invariant* {［ _ ∣ _ ∣ _ ］▷} ◾ nf nf' = refl
𝕌Invariant* {⟨ _ ∣ _ ∣ _ ⟩◁} ◾ nf nf' = refl
𝕌Invariant* {［ _ ∣ _ ∣ _ ］◁} ◾ nf nf' = refl
𝕌Invariant* {⊠} ◾ nf nf' = ⊥-elim (nf' refl)
𝕌Invariant* (r ∷ ◾) nf nf' = 𝕌Invariant r nf nf'
𝕌Invariant* (r ∷ (r' ∷ rs)) nf nf' = trans (𝕌Invariant r nf nf'') (𝕌Invariant* (r' ∷ rs) nf'' nf')
  where
  nf'' = λ eq → ⊠-is-stuck eq (_ , r')

-- Appending context does not affect reductions
appendκ↦ : ∀ {st st'} → (r : st ↦ st') (nf : st ≢ ⊠) (nf' : st' ≢ ⊠) (eq : get𝕌State st nf ≡  get𝕌State st' nf')
         → (κ : Context {proj₁ (get𝕌State st nf)} {proj₂ (get𝕌State st nf)})
         → appendκState st nf κ ↦ appendκState st' nf' (subst (λ {(A , B) → Context {A} {B}}) eq κ)
appendκ↦ ↦⃗₁ nf nf' refl ctx = ↦⃗₁
appendκ↦ ↦⃗₂ nf nf' refl ctx = ↦⃗₂
appendκ↦ ↦⃗₃ nf nf' refl ctx = ↦⃗₃
appendκ↦ ↦⃗₄ nf nf' refl ctx = ↦⃗₄
appendκ↦ ↦⃗₅ nf nf' refl ctx = ↦⃗₅
appendκ↦ ↦⃗₆ nf nf' refl ctx = ↦⃗₆
appendκ↦ ↦⃗₇ nf nf' refl ctx = ↦⃗₇
appendκ↦ ↦⃗₈ nf nf' refl ctx = ↦⃗₈
appendκ↦ ↦⃗₉ nf nf' refl ctx = ↦⃗₉
appendκ↦ ↦⃗₁₀ nf nf' refl ctx = ↦⃗₁₀
appendκ↦ ↦⃗₁₁ nf nf' refl ctx = ↦⃗₁₁
appendκ↦ ↦⃗₁₂ nf nf' refl ctx = ↦⃗₁₂
appendκ↦ ↦⃖₁ nf nf' refl ctx = ↦⃖₁
appendκ↦ ↦⃖₂ nf nf' refl ctx = ↦⃖₂
appendκ↦ ↦⃖₃ nf nf' refl ctx = ↦⃖₃
appendκ↦ ↦⃖₄ nf nf' refl ctx = ↦⃖₄
appendκ↦ ↦⃖₅ nf nf' refl ctx = ↦⃖₅
appendκ↦ ↦⃖₆ nf nf' refl ctx = ↦⃖₆
appendκ↦ ↦⃖₇ nf nf' refl ctx = ↦⃖₇
appendκ↦ ↦⃖₈ nf nf' refl ctx = ↦⃖₈
appendκ↦ ↦⃖₉ nf nf' refl ctx = ↦⃖₉
appendκ↦ ↦⃖₁₀ nf nf' refl ctx = ↦⃖₁₀
appendκ↦ ↦⃖₁₁ nf nf' refl ctx = ↦⃖₁₁
appendκ↦ ↦⃖₁₂ nf nf' refl ctx = ↦⃖₁₂
appendκ↦ ↦η₊₁ nf nf' refl ctx = ↦η₊₁
appendκ↦ ↦η₊₂ nf nf' refl ctx = ↦η₊₂
appendκ↦ ↦ε₊₁ nf nf' refl ctx = ↦ε₊₁
appendκ↦ ↦ε₊₂ nf nf' refl ctx = ↦ε₊₂
appendκ↦ ↦⃗ηₓ nf nf' refl ctx = ↦⃗ηₓ
appendκ↦ (↦⃖ηₓ₁ {eq = eq}) nf nf' refl ctx = ↦⃖ηₓ₁ {eq = eq}
appendκ↦ ↦⃖ηₓ₂ nf nf' eq ctx = ⊥-elim (nf' refl)
appendκ↦ (↦⃗εₓ₁ {eq = eq}) nf nf' refl ctx = ↦⃗εₓ₁ {eq = eq}
appendκ↦ ↦⃗εₓ₂ nf nf' eq ctx = ⊥-elim (nf' refl)
appendκ↦ ↦⃖εₓ nf nf' refl ctx = ↦⃖εₓ

appendκ↦* : ∀ {st st'} → (r : st ↦* st') (nf : st ≢ ⊠) (nf' : st' ≢ ⊠) (eq : get𝕌State st nf ≡  get𝕌State st' nf')
          → (κ : Context {proj₁ (get𝕌State st nf)} {proj₂ (get𝕌State st nf)})
          → appendκState st nf κ ↦* appendκState st' nf' (subst (λ {(A , B) → Context {A} {B}}) eq κ)
appendκ↦* {⟨ _ ∣ _ ∣ _ ⟩▷} ◾ nf nf' refl ctx = ◾
appendκ↦* {［ _ ∣ _ ∣ _ ］▷} ◾ nf nf' refl ctx = ◾
appendκ↦* {⟨ _ ∣ _ ∣ _ ⟩◁} ◾ nf nf' refl ctx = ◾
appendκ↦* {［ _ ∣ _ ∣ _ ］◁} ◾ nf nf' refl ctx = ◾
appendκ↦* {⊠} ◾ nf nf' eq ctx = ⊥-elim (nf' refl)
appendκ↦* (↦⃗₁ {b = b} {v} {κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃗₁ {b = b} {v} {κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃗₂ {v = v} {κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃗₂ {v = v} {κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃗₃ {v = v} {κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃗₃ {v = v} {κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃗₄ {x = x} {κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃗₄ {x = x} {κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃗₅ {y = y} {κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃗₅ {y = y} {κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃗₆ {κ = κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃗₆ {κ = κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃗₇ {κ = κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃗₇ {κ = κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃗₈ {κ = κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃗₈ {κ = κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃗₉ {κ = κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃗₉ {κ = κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃗₁₀ {κ = κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃗₁₀ {κ = κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃗₁₁ {κ = κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃗₁₁ {κ = κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃗₁₂ {κ = κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃗₁₂ {κ = κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃖₁ {b = b} {v} {κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃖₁ {b = b} {v} {κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃖₂ {v = v} {κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃖₂ {v = v} {κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃖₃ {v = v} {κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃖₃ {v = v} {κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃖₄ {x = x} {κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃖₄ {x = x} {κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃖₅ {y = y} {κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃖₅ {y = y} {κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃖₆ {κ = κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃖₆ {κ = κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃖₇ {κ = κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃖₇ {κ = κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃖₈ {κ = κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃖₈ {κ = κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃖₉ {κ = κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃖₉ {κ = κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃖₁₀ {κ = κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃖₁₀ {κ = κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃖₁₁ {κ = κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃖₁₁ {κ = κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃖₁₂ {κ = κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃖₁₂ {κ = κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦η₊₁ {κ = κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦η₊₁ {κ = κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦η₊₂ {κ = κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦η₊₂ {κ = κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦ε₊₁ {κ = κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦ε₊₁ {κ = κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦ε₊₂ {κ = κ} ∷ rs) nf nf' eq ctx = appendκ↦ (↦ε₊₂ {κ = κ}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃗ηₓ ∷ rs) nf nf' eq ctx = appendκ↦ ↦⃗ηₓ nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃖ηₓ₁ {eq = eq'} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃖ηₓ₁ {eq = eq'}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃖ηₓ₂ ∷ ◾) nf nf' eq ctx = ⊥-elim (nf' refl)
appendκ↦* (↦⃗εₓ₁ {eq = eq'} ∷ rs) nf nf' eq ctx = appendκ↦ (↦⃗εₓ₁ {eq = eq'}) nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx
appendκ↦* (↦⃗εₓ₂ ∷ ◾) nf nf' eq ctx = ⊥-elim (nf' refl)
appendκ↦* (↦⃖εₓ ∷ rs) nf nf' eq ctx = appendκ↦ ↦⃖εₓ nf (λ ()) refl ctx ∷ appendκ↦* rs (λ ()) nf' eq ctx

appendκ↦⊠ : ∀ {st} → (r : st ↦ ⊠) (nf : st ≢ ⊠)
          → (κ : Context {proj₁ (get𝕌State st nf)} {proj₂ (get𝕌State st nf)})
          → appendκState st nf κ ↦ ⊠
appendκ↦⊠ (↦⃖ηₓ₂ {neq = neq}) nf ctx = ↦⃖ηₓ₂ {neq = neq}
appendκ↦⊠ (↦⃗εₓ₂ {neq = neq}) nf ctx = ↦⃗εₓ₂ {neq = neq}

appendκ↦*⊠ : ∀ {st} → (r : st ↦* ⊠) (nf : st ≢ ⊠)
           → (κ : Context {proj₁ (get𝕌State st nf)} {proj₂ (get𝕌State st nf)})
           → appendκState st nf κ ↦* ⊠
appendκ↦*⊠ ◾ nf ctx = ⊥-elim (nf refl)
appendκ↦*⊠ (r ∷ ◾) nf ctx = appendκ↦⊠ r nf ctx ∷ ◾
appendκ↦*⊠ (↦⃗₁ ∷ (r' ∷ rs)) nf ctx = ↦⃗₁ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃗₂ ∷ (r' ∷ rs)) nf ctx = ↦⃗₂ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃗₃ ∷ (r' ∷ rs)) nf ctx = ↦⃗₃ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃗₄ ∷ (r' ∷ rs)) nf ctx = ↦⃗₄ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃗₅ ∷ (r' ∷ rs)) nf ctx = ↦⃗₅ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃗₆ ∷ (r' ∷ rs)) nf ctx = ↦⃗₆ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃗₇ ∷ (r' ∷ rs)) nf ctx = ↦⃗₇ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃗₈ ∷ (r' ∷ rs)) nf ctx = ↦⃗₈ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃗₉ ∷ (r' ∷ rs)) nf ctx = ↦⃗₉ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃗₁₀ ∷ (r' ∷ rs)) nf ctx = ↦⃗₁₀ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃗₁₁ ∷ (r' ∷ rs)) nf ctx = ↦⃗₁₁ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃗₁₂ ∷ (r' ∷ rs)) nf ctx = ↦⃗₁₂ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃖₁ ∷ (r' ∷ rs)) nf ctx = ↦⃖₁ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃖₂ ∷ (r' ∷ rs)) nf ctx = ↦⃖₂ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃖₃ ∷ (r' ∷ rs)) nf ctx = ↦⃖₃ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃖₄ ∷ (r' ∷ rs)) nf ctx = ↦⃖₄ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃖₅ ∷ (r' ∷ rs)) nf ctx = ↦⃖₅ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃖₆ ∷ (r' ∷ rs)) nf ctx = ↦⃖₆ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃖₇ ∷ (r' ∷ rs)) nf ctx = ↦⃖₇ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃖₈ ∷ (r' ∷ rs)) nf ctx = ↦⃖₈ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃖₉ ∷ (r' ∷ rs)) nf ctx = ↦⃖₉ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃖₁₀ ∷ (r' ∷ rs)) nf ctx = ↦⃖₁₀ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃖₁₁ ∷ (r' ∷ rs)) nf ctx = ↦⃖₁₁ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃖₁₂ ∷ (r' ∷ rs)) nf ctx = ↦⃖₁₂ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦η₊₁ ∷ (r' ∷ rs)) nf ctx = ↦η₊₁ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦η₊₂ ∷ (r' ∷ rs)) nf ctx = ↦η₊₂ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦ε₊₁ ∷ (r' ∷ rs)) nf ctx = ↦ε₊₁ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦ε₊₂ ∷ (r' ∷ rs)) nf ctx = ↦ε₊₂ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃗ηₓ ∷ (r' ∷ rs)) nf ctx = ↦⃗ηₓ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃖ηₓ₁ {eq = eq} ∷ (r' ∷ rs)) nf ctx = ↦⃖ηₓ₁ {eq = eq} ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃗εₓ₁ {eq = eq} ∷ (r' ∷ rs)) nf ctx = ↦⃗εₓ₁ {eq = eq} ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
appendκ↦*⊠ (↦⃖εₓ ∷ (r' ∷ rs)) nf ctx = ↦⃖εₓ ∷ appendκ↦*⊠ (r' ∷ rs) (λ ()) ctx
