module Pi-.Invariants where
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
open import Pi-.Syntax
open import Pi-.Opsem
open import Pi-.NoRepeat
open import Pi-.Dir

-- Direction of values
dir𝕍 : ∀ {t} → ⟦ t ⟧ → Dir
dir𝕍 {𝟘} ()
dir𝕍 {𝟙} v = ▷
dir𝕍 {_ +ᵤ _} (inj₁ x) = dir𝕍 x
dir𝕍 {_ +ᵤ _} (inj₂ y) = dir𝕍 y
dir𝕍 {_ ×ᵤ _} (x , y) = dir𝕍 x ×ᵈⁱʳ dir𝕍 y
dir𝕍 { - _} (- v) = -ᵈⁱʳ (dir𝕍 v)

-- Execution direction of states
dirState : State → Dir
dirState ⟨ _ ∣ _ ∣ _ ⟩▷ = ▷
dirState ［ _ ∣ _ ∣ _ ］▷ = ▷
dirState ⟨ _ ∣ _ ∣ _ ⟩◁ = ◁
dirState ［ _ ∣ _ ∣ _ ］◁ = ◁

dirCtx : ∀ {A B} → Context {A} {B} → Dir
dirCtx ☐ = ▷
dirCtx (☐⨾ c₂ • κ) = dirCtx κ
dirCtx (c₁ ⨾☐• κ) = dirCtx κ
dirCtx (☐⊕ c₂ • κ) = dirCtx κ
dirCtx (c₁ ⊕☐• κ) = dirCtx κ
dirCtx (☐⊗[ c₂ , x ]• κ) = dir𝕍 x ×ᵈⁱʳ dirCtx κ
dirCtx ([ c₁ , x ]⊗☐• κ) = dir𝕍 x ×ᵈⁱʳ dirCtx κ

dirState𝕍 : State → Dir
dirState𝕍 ⟨ _ ∣ v ∣ κ ⟩▷ = dir𝕍 v  ×ᵈⁱʳ dirCtx κ
dirState𝕍 ［ _ ∣ v ∣ κ ］▷ = dir𝕍 v  ×ᵈⁱʳ dirCtx κ
dirState𝕍 ⟨ _ ∣ v ∣ κ ⟩◁ = dir𝕍 v  ×ᵈⁱʳ dirCtx κ
dirState𝕍 ［ _ ∣ v ∣ κ ］◁ = dir𝕍 v  ×ᵈⁱʳ dirCtx κ

δdir : ∀ {A B} (c : A ↔ B) {b : base c} → (v : ⟦ A ⟧) → dir𝕍 v ≡ dir𝕍 (δ c {b} v)
δdir unite₊l (inj₂ v) = refl
δdir uniti₊l v = refl
δdir swap₊ (inj₁ x) = refl
δdir swap₊ (inj₂ y) = refl
δdir assocl₊ (inj₁ v) = refl
δdir assocl₊ (inj₂ (inj₁ v)) = refl
δdir assocl₊ (inj₂ (inj₂ v)) = refl
δdir assocr₊ (inj₁ (inj₁ v)) = refl
δdir assocr₊ (inj₁ (inj₂ v)) = refl
δdir assocr₊ (inj₂ v) = refl
δdir unite⋆l (tt , v) = identˡᵈⁱʳ (dir𝕍 v)
δdir uniti⋆l v = sym (identˡᵈⁱʳ (dir𝕍 v))
δdir swap⋆ (x , y) = commᵈⁱʳ _ _
δdir assocl⋆ (v₁ , (v₂ , v₃)) = assoclᵈⁱʳ _ _ _
δdir assocr⋆ ((v₁ , v₂) , v₃) = sym (assoclᵈⁱʳ _ _ _)
δdir dist (inj₁ v₁ , v₃) = refl
δdir dist (inj₂ v₂ , v₃) = refl
δdir factor (inj₁ (v₁ , v₃)) = refl
δdir factor (inj₂ (v₂ , v₃)) = refl

-- Invariant of directions
dirInvariant : ∀ {st st'} → st ↦ st' → dirState st ×ᵈⁱʳ dirState𝕍 st ≡ dirState st' ×ᵈⁱʳ dirState𝕍 st'
dirInvariant {⟨ c ∣ v ∣ κ ⟩▷} (↦⃗₁ {b = b}) rewrite δdir c {b} v = refl
dirInvariant ↦⃗₂ = refl
dirInvariant ↦⃗₃ = refl
dirInvariant ↦⃗₄ = refl
dirInvariant ↦⃗₅ = refl
dirInvariant {⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ κ ⟩▷} ↦⃗₆ rewrite assoclᵈⁱʳ (dir𝕍 x) (dir𝕍 y) (dirCtx κ) = refl
dirInvariant ↦⃗₇ = refl
dirInvariant {［ c₁ ∣ x ∣ ☐⊗[ c₂ , y ]• κ ］▷} ↦⃗₈ rewrite assoc-commᵈⁱʳ (dir𝕍 x) (dir𝕍 y) (dirCtx κ) = refl
dirInvariant {［ c₂ ∣ y ∣ [ c₁ , x ]⊗☐• κ ］▷} ↦⃗₉ rewrite assocl-commᵈⁱʳ (dir𝕍 y) (dir𝕍 x) (dirCtx κ) = refl
dirInvariant ↦⃗₁₀ = refl
dirInvariant ↦⃗₁₁ = refl
dirInvariant ↦⃗₁₂ = refl
dirInvariant {_} {⟨ c ∣ v ∣ κ ⟩◁} (↦⃖₁ {b = b}) rewrite δdir c {b} v = refl
dirInvariant ↦⃖₂ = refl
dirInvariant ↦⃖₃ = refl
dirInvariant ↦⃖₄ = refl
dirInvariant ↦⃖₅ = refl
dirInvariant {⟨ c₁ ∣ x ∣ ☐⊗[ c₂ , y ]• κ ⟩◁} ↦⃖₆ rewrite assoclᵈⁱʳ (dir𝕍 x) (dir𝕍 y) (dirCtx κ) = refl
dirInvariant ↦⃖₇ = refl
dirInvariant {⟨ c₂ ∣ y ∣ [ c₁ , x ]⊗☐• κ ⟩◁} ↦⃖₈ rewrite assoc-commᵈⁱʳ (dir𝕍 y) (dir𝕍 x) (dirCtx κ) = refl
dirInvariant {［ c₁ ⊗ c₂ ∣ (x , y) ∣ κ ］◁ } ↦⃖₉ rewrite assoclᵈⁱʳ (dir𝕍 y) (dir𝕍 x) (dirCtx κ) | commᵈⁱʳ (dir𝕍 y) (dir𝕍 x) = refl
dirInvariant ↦⃖₁₀ = refl
dirInvariant ↦⃖₁₁ = refl
dirInvariant ↦⃖₁₂ = refl
dirInvariant {［ η₊ ∣ inj₁ v ∣ κ ］◁} ↦η₁ with dir𝕍 v
... | ◁ with dirCtx κ
... | ◁ = refl
... | ▷ = refl
dirInvariant {［ η₊ ∣ inj₁ v ∣ κ ］◁} ↦η₁ | ▷ with dirCtx κ
... | ◁ = refl
... | ▷ = refl
dirInvariant {［ η₊ ∣ inj₂ (- v) ∣ κ ］◁} ↦η₂ with dir𝕍 v
... | ◁ with dirCtx κ
... | ◁ = refl
... | ▷ = refl
dirInvariant {［ η₊ ∣ inj₂ (- v) ∣ κ ］◁} ↦η₂ | ▷ with dirCtx κ
... | ◁ = refl
... | ▷ = refl
dirInvariant {⟨ ε₊ ∣ inj₁ v ∣ κ ⟩▷} ↦ε₁ with dir𝕍 v
... | ◁ with dirCtx κ
... | ◁ = refl
... | ▷ = refl
dirInvariant {⟨ ε₊ ∣ inj₁ v ∣ κ ⟩▷} ↦ε₁ | ▷ with dirCtx κ
... | ◁ = refl
... | ▷ = refl
dirInvariant {⟨ ε₊ ∣ inj₂ (- v) ∣ κ ⟩▷} ↦ε₂ with dir𝕍 v
... | ◁ with dirCtx κ
... | ◁ = refl
... | ▷ = refl
dirInvariant {⟨ ε₊ ∣ inj₂ (- v) ∣ κ ⟩▷} ↦ε₂ | ▷ with dirCtx κ
... | ◁ = refl
... | ▷ = refl

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
getℂ ⟨ c ∣ _ ∣ κ ⟩▷ = getℂκ c κ
getℂ ［ c ∣ _ ∣ κ ］▷ = getℂκ c κ
getℂ ⟨ c ∣ _ ∣ κ ⟩◁ = getℂκ c κ
getℂ ［ c ∣ _ ∣ κ ］◁ = getℂκ c κ

-- The reconstructed combinator stays the same
ℂInvariant : ∀ {st st'} → st ↦ st' → getℂ st ≡  getℂ st'
ℂInvariant ↦⃗₁ = refl
ℂInvariant ↦⃗₂ = refl
ℂInvariant ↦⃗₃ = refl
ℂInvariant ↦⃗₄ = refl
ℂInvariant ↦⃗₅ = refl
ℂInvariant ↦⃗₆ = refl
ℂInvariant ↦⃗₇ = refl
ℂInvariant ↦⃗₈ = refl
ℂInvariant ↦⃗₉ = refl
ℂInvariant ↦⃗₁₀ = refl
ℂInvariant ↦⃗₁₁ = refl
ℂInvariant ↦⃗₁₂ = refl
ℂInvariant ↦⃖₁ = refl
ℂInvariant ↦⃖₂ = refl
ℂInvariant ↦⃖₃ = refl
ℂInvariant ↦⃖₄ = refl
ℂInvariant ↦⃖₅ = refl
ℂInvariant ↦⃖₆ = refl
ℂInvariant ↦⃖₇ = refl
ℂInvariant ↦⃖₈ = refl
ℂInvariant ↦⃖₉ = refl
ℂInvariant ↦⃖₁₀ = refl
ℂInvariant ↦⃖₁₁ = refl
ℂInvariant ↦⃖₁₂ = refl
ℂInvariant ↦η₁ = refl
ℂInvariant ↦η₂ = refl
ℂInvariant ↦ε₁ = refl
ℂInvariant ↦ε₂ = refl

ℂInvariant* : ∀ {st st'} → st ↦* st' → getℂ st ≡  getℂ st'
ℂInvariant* ◾ = refl
ℂInvariant* (r ∷ rs) = trans (ℂInvariant r) (ℂInvariant* rs)

-- Get the type of the deepest context
get𝕌 : ∀ {A B} → Context {A} {B} → 𝕌 × 𝕌
get𝕌 {A} {B} ☐ = A , B
get𝕌 (☐⨾ c₂ • κ) = get𝕌 κ
get𝕌 (c₁ ⨾☐• κ) = get𝕌 κ
get𝕌 (☐⊕ c₂ • κ) = get𝕌 κ
get𝕌 (c₁ ⊕☐• κ) = get𝕌 κ
get𝕌 (☐⊗[ c₂ , x ]• κ) = get𝕌 κ
get𝕌 ([ c₁ , x ]⊗☐• κ) = get𝕌 κ

get𝕌State : State → 𝕌 × 𝕌
get𝕌State ⟨ c ∣ v ∣ κ ⟩▷ = get𝕌 κ
get𝕌State ［ c ∣ v ∣ κ ］▷ = get𝕌 κ
get𝕌State ⟨ c ∣ v ∣ κ ⟩◁ = get𝕌 κ
get𝕌State ［ c ∣ v ∣ κ ］◁ = get𝕌 κ

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
appendκState ⟨ c ∣ v ∣ κ ⟩▷ ctx = ⟨ c ∣ v ∣ appendκ κ ctx ⟩▷
appendκState ［ c ∣ v ∣ κ ］▷ ctx = ［ c ∣ v ∣ appendκ κ ctx ］▷
appendκState ⟨ c ∣ v ∣ κ ⟩◁ ctx = ⟨ c ∣ v ∣ appendκ κ ctx ⟩◁
appendκState ［ c ∣ v ∣ κ ］◁ ctx = ［ c ∣ v ∣ appendκ κ ctx ］◁

-- The type of context does not change during execution
𝕌Invariant : ∀ {st st'} → st ↦ st' → get𝕌State st ≡ get𝕌State st'
𝕌Invariant ↦⃗₁ = refl
𝕌Invariant ↦⃗₂ = refl
𝕌Invariant ↦⃗₃ = refl
𝕌Invariant ↦⃗₄ = refl
𝕌Invariant ↦⃗₅ = refl
𝕌Invariant ↦⃗₆ = refl
𝕌Invariant ↦⃗₇ = refl
𝕌Invariant ↦⃗₈ = refl
𝕌Invariant ↦⃗₉ = refl
𝕌Invariant ↦⃗₁₀ = refl
𝕌Invariant ↦⃗₁₁ = refl
𝕌Invariant ↦⃗₁₂ = refl
𝕌Invariant ↦⃖₁ = refl
𝕌Invariant ↦⃖₂ = refl
𝕌Invariant ↦⃖₃ = refl
𝕌Invariant ↦⃖₄ = refl
𝕌Invariant ↦⃖₅ = refl
𝕌Invariant ↦⃖₆ = refl
𝕌Invariant ↦⃖₇ = refl
𝕌Invariant ↦⃖₈ = refl
𝕌Invariant ↦⃖₉ = refl
𝕌Invariant ↦⃖₁₀ = refl
𝕌Invariant ↦⃖₁₁ = refl
𝕌Invariant ↦⃖₁₂ = refl
𝕌Invariant ↦η₁ = refl
𝕌Invariant ↦η₂ = refl
𝕌Invariant ↦ε₁ = refl
𝕌Invariant ↦ε₂ = refl

𝕌Invariant* : ∀ {st st'} → st ↦* st' → get𝕌State st ≡  get𝕌State st'
𝕌Invariant* ◾ = refl
𝕌Invariant* (r ∷ rs) = trans (𝕌Invariant r) (𝕌Invariant* rs)

-- Appending context does not affect reductions
appendκ↦ : ∀ {st st'} → (r : st ↦ st') (eq : get𝕌State st ≡  get𝕌State st')
         → (κ : Context {proj₁ (get𝕌State st)} {proj₂ (get𝕌State st)})
         → appendκState st κ ↦ appendκState st' (subst (λ {(A , B) → Context {A} {B}}) eq κ)
appendκ↦ ↦⃗₁ refl ctx = ↦⃗₁
appendκ↦ ↦⃗₂ refl ctx = ↦⃗₂
appendκ↦ ↦⃗₃ refl ctx = ↦⃗₃
appendκ↦ ↦⃗₄ refl ctx = ↦⃗₄
appendκ↦ ↦⃗₅ refl ctx = ↦⃗₅
appendκ↦ ↦⃗₆ refl ctx = ↦⃗₆
appendκ↦ ↦⃗₇ refl ctx = ↦⃗₇
appendκ↦ ↦⃗₈ refl ctx = ↦⃗₈
appendκ↦ ↦⃗₉ refl ctx = ↦⃗₉
appendκ↦ ↦⃗₁₀ refl ctx = ↦⃗₁₀
appendκ↦ ↦⃗₁₁ refl ctx = ↦⃗₁₁
appendκ↦ ↦⃗₁₂ refl ctx = ↦⃗₁₂
appendκ↦ ↦⃖₁ refl ctx = ↦⃖₁
appendκ↦ ↦⃖₂ refl ctx = ↦⃖₂
appendκ↦ ↦⃖₃ refl ctx = ↦⃖₃
appendκ↦ ↦⃖₄ refl ctx = ↦⃖₄
appendκ↦ ↦⃖₅ refl ctx = ↦⃖₅
appendκ↦ ↦⃖₆ refl ctx = ↦⃖₆
appendκ↦ ↦⃖₇ refl ctx = ↦⃖₇
appendκ↦ ↦⃖₈ refl ctx = ↦⃖₈
appendκ↦ ↦⃖₉ refl ctx = ↦⃖₉
appendκ↦ ↦⃖₁₀ refl ctx = ↦⃖₁₀
appendκ↦ ↦⃖₁₁ refl ctx = ↦⃖₁₁
appendκ↦ ↦⃖₁₂ refl ctx = ↦⃖₁₂
appendκ↦ ↦η₁ refl ctx = ↦η₁
appendκ↦ ↦η₂ refl ctx = ↦η₂
appendκ↦ ↦ε₁ refl ctx = ↦ε₁
appendκ↦ ↦ε₂ refl ctx = ↦ε₂

appendκ↦* : ∀ {st st'} → (r : st ↦* st') (eq : get𝕌State st ≡  get𝕌State st')
          → (κ : Context {proj₁ (get𝕌State st)} {proj₂ (get𝕌State st)})
          → appendκState st κ ↦* appendκState st' (subst (λ {(A , B) → Context {A} {B}}) eq κ)
appendκ↦* ◾ refl ctx = ◾
appendκ↦* (↦⃗₁ {b = b} {v} {κ} ∷ rs) eq ctx = appendκ↦ (↦⃗₁ {b = b} {v} {κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃗₂ {v = v} {κ} ∷ rs) eq ctx = appendκ↦ (↦⃗₂ {v = v} {κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃗₃ {v = v} {κ} ∷ rs) eq ctx = appendκ↦ (↦⃗₃ {v = v} {κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃗₄ {x = x} {κ} ∷ rs) eq ctx = appendκ↦ (↦⃗₄ {x = x} {κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃗₅ {y = y} {κ} ∷ rs) eq ctx = appendκ↦ (↦⃗₅ {y = y} {κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃗₆ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦⃗₆ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃗₇ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦⃗₇ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃗₈ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦⃗₈ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃗₉ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦⃗₉ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃗₁₀ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦⃗₁₀ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃗₁₁ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦⃗₁₁ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃗₁₂ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦⃗₁₂ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃖₁ {b = b} {v} {κ} ∷ rs) eq ctx = appendκ↦ (↦⃖₁ {b = b} {v} {κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃖₂ {v = v} {κ} ∷ rs) eq ctx = appendκ↦ (↦⃖₂ {v = v} {κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃖₃ {v = v} {κ} ∷ rs) eq ctx = appendκ↦ (↦⃖₃ {v = v} {κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃖₄ {x = x} {κ} ∷ rs) eq ctx = appendκ↦ (↦⃖₄ {x = x} {κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃖₅ {y = y} {κ} ∷ rs) eq ctx = appendκ↦ (↦⃖₅ {y = y} {κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃖₆ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦⃖₆ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃖₇ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦⃖₇ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃖₈ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦⃖₈ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃖₉ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦⃖₉ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃖₁₀ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦⃖₁₀ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃖₁₁ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦⃖₁₁ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦⃖₁₂ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦⃖₁₂ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦η₁ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦η₁ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦η₂ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦η₂ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦ε₁ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦ε₁ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
appendκ↦* (↦ε₂ {κ = κ} ∷ rs) eq ctx = appendκ↦ (↦ε₂ {κ = κ}) refl ctx ∷ appendκ↦* rs eq ctx
