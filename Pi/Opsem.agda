module Pi.Opsem where
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Base
open import Pi.Syntax

infix  1  _↦_

-- Base combinators
base : ∀ {A B} (c : A ↔ B) → Set
base unite₊l = ⊤
base uniti₊l = ⊤
base swap₊ = ⊤
base assocl₊ = ⊤
base assocr₊ = ⊤
base unite⋆l = ⊤
base uniti⋆l = ⊤
base swap⋆ = ⊤
base assocl⋆ = ⊤
base assocr⋆ = ⊤
base absorbr = ⊤
base factorzl = ⊤
base dist = ⊤
base factor = ⊤
base _ = ⊥

base-is-prop : ∀ {A B} (c : A ↔ B) → is-prop (base c)
base-is-prop unite₊l tt tt = refl
base-is-prop uniti₊l tt tt = refl
base-is-prop swap₊ tt tt = refl
base-is-prop assocl₊ tt tt = refl
base-is-prop assocr₊ tt tt = refl
base-is-prop unite⋆l tt tt = refl
base-is-prop uniti⋆l tt tt = refl
base-is-prop swap⋆ tt tt = refl
base-is-prop assocl⋆ tt tt = refl
base-is-prop assocr⋆ tt tt = refl
base-is-prop absorbr tt tt = refl
base-is-prop factorzl tt tt = refl
base-is-prop dist tt tt = refl
base-is-prop factor tt tt = refl

-- Evaluator for base combinators
δ : ∀ {A B} (c : A ↔ B) {_ : base c} → ⟦ A ⟧ → ⟦ B ⟧
δ unite₊l (inj₂ v) = v
δ uniti₊l v = inj₂ v
δ swap₊ (inj₁ x) = inj₂ x
δ swap₊ (inj₂ y) = inj₁ y
δ assocl₊ (inj₁ v) = inj₁ (inj₁ v)
δ assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
δ assocl₊ (inj₂ (inj₂ v)) = inj₂ v
δ assocr₊ (inj₁ (inj₁ v)) = inj₁ v
δ assocr₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
δ assocr₊ (inj₂ v) = inj₂ (inj₂ v)
δ unite⋆l (tt , v) = v
δ uniti⋆l v = (tt , v)
δ swap⋆ (x , y) = (y , x)
δ assocl⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
δ assocr⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
δ absorbr ()
δ factorzl ()
δ dist (inj₁ v₁ , v₃) = inj₁ (v₁ , v₃)
δ dist (inj₂ v₂ , v₃) = inj₂ (v₂ , v₃)
δ factor (inj₁ (v₁ , v₃)) = (inj₁ v₁ , v₃)
δ factor (inj₂ (v₂ , v₃)) = (inj₂ v₂ , v₃)

-- Context
data Context : {A B : 𝕌} → Set where
  ☐ : ∀ {A B} → Context {A} {B}
  ☐⨾_•_ : ∀ {A B C} → (c₂ : B ↔ C) → Context {A} {C} → Context {A} {B}
  _⨾☐•_ : ∀ {A B C} → (c₁ : A ↔ B) → Context {A} {C} → Context {B} {C}
  ☐⊕_•_ : ∀ {A B C D} → (c₂ : C ↔ D) → Context {A +ᵤ C} {B +ᵤ D} → Context {A} {B}
  _⊕☐•_ : ∀ {A B C D} → (c₁ : A ↔ B) → Context {A +ᵤ C} {B +ᵤ D} → Context {C} {D}
  ☐⊗[_,_]•_ : ∀ {A B C D} → (c₂ : C ↔ D) → ⟦ C ⟧ → Context {A ×ᵤ C} {B ×ᵤ D} → Context {A} {B}
  [_,_]⊗☐•_ : ∀ {A B C D} → (c₁ : A ↔ B) → ⟦ B ⟧ → Context {A ×ᵤ C} {B ×ᵤ D} → Context {C} {D}

-- Machine state
data State : Set where
  ⟨_∣_∣_⟩ : ∀ {A B} → (c : A ↔ B) → ⟦ A ⟧ → Context {A} {B} → State
  ［_∣_∣_］ : ∀ {A B} → (c : A ↔ B) → ⟦ B ⟧ → Context {A} {B} → State

-- Reduction relation
data _↦_ : State → State → Set where
  ↦₁  : ∀ {A B} {c : A ↔ B} {b : base c} {v : ⟦ A ⟧} {κ : Context} → ⟨ c ∣ v ∣ κ ⟩ ↦ ［ c ∣ δ c {b} v ∣ κ ］
  ↦₂  : ∀ {A} {v : ⟦ A ⟧} {κ : Context} → ⟨ id↔ ∣ v ∣ κ ⟩ ↦ ［ id↔ ∣ v ∣ κ ］
  ↦₃  : ∀ {A B C} {c₁ : A ↔ B} {c₂ : B ↔ C} {v : ⟦ A ⟧} {κ : Context}
      → ⟨ c₁ ⨾ c₂ ∣ v ∣ κ ⟩ ↦ ⟨ c₁ ∣ v ∣ ☐⨾ c₂ • κ ⟩
  ↦₄  : ∀ {A B C D} {c₁ : A ↔ B} {c₂ : C ↔ D} {x : ⟦ A ⟧} {κ : Context}
      → ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ κ ⟩ ↦ ⟨ c₁ ∣ x ∣ ☐⊕ c₂ • κ ⟩
  ↦₅  : ∀ {A B C D} {c₁ : A ↔ B} {c₂ : C ↔ D} {y : ⟦ C ⟧} {κ : Context}
      → ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ κ ⟩ ↦ ⟨ c₂ ∣ y ∣ c₁ ⊕☐• κ ⟩
  ↦₆  : ∀ {A B C D} {c₁ : A ↔ B} {c₂ : C ↔ D} {x : ⟦ A ⟧} {y : ⟦ C ⟧} {κ : Context}
      → ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ κ ⟩ ↦ ⟨ c₁ ∣ x ∣ ☐⊗[ c₂ , y ]• κ ⟩
  ↦₇  : ∀ {A B C} {c₁ : A ↔ B} {c₂ : B ↔ C} {v : ⟦ B ⟧} {κ : Context}
      → ［ c₁ ∣ v ∣ ☐⨾ c₂ • κ ］ ↦ ⟨ c₂ ∣ v ∣ (c₁ ⨾☐• κ) ⟩
  ↦₈  : ∀ {A B C D} {c₁ : A ↔ B} {c₂ : C ↔ D} {x : ⟦ B ⟧} {y : ⟦ C ⟧} {κ : Context}
      → ［ c₁ ∣ x ∣ ☐⊗[ c₂ , y ]• κ ］ ↦ ⟨ c₂ ∣ y ∣ [ c₁ , x ]⊗☐• κ ⟩
  ↦₉  : ∀ {A B C D} {c₁ : A ↔ B} {c₂ : C ↔ D} {x : ⟦ B ⟧} {y : ⟦ D ⟧} {κ : Context}
      → ［ c₂ ∣ y ∣ [ c₁ , x ]⊗☐• κ ］ ↦ ［ c₁ ⊗ c₂ ∣ (x , y) ∣ κ ］
  ↦₁₀ : ∀ {A B C} {c₁ : A ↔ B} {c₂ : B ↔ C} {v : ⟦ C ⟧} {κ : Context}
      → ［ c₂ ∣ v ∣ (c₁ ⨾☐• κ) ］ ↦ ［ c₁ ⨾ c₂ ∣ v ∣ κ ］
  ↦₁₁ : ∀ {A B C D} {c₁ : A ↔ B} {c₂ : C ↔ D} {x : ⟦ B ⟧} {κ : Context}
      → ［ c₁ ∣ x ∣ ☐⊕ c₂ • κ ］ ↦ ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ κ ］
  ↦₁₂ : ∀ {A B C D} {c₁ : A ↔ B} {c₂ : C ↔ D} {y : ⟦ D ⟧} {κ : Context}
      → ［ c₂ ∣ y ∣ c₁ ⊕☐• κ ］ ↦ ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ κ ］


