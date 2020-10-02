module PiQ.Opsem where
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Sum
open import Data.Product
open import Data.Maybe
open import Relation.Binary.Core
open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_)
open import Base
open import PiQ.Syntax

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

-- Dual combinators
dual : ∀ {A B} (c : A ↔ B) → Set
dual (ηₓ _) = ⊤
dual (εₓ _) = ⊤
dual η₊ = ⊤
dual ε₊ = ⊤
dual _ = ⊥

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

-- Decidable equality of PiQ values
_≟_ : {t : 𝕌} → Decidable (_≡_ {A = ⟦ t ⟧})
_≟_ {𝟙} tt tt = yes refl
_≟_ {t₁ +ᵤ t₂} (inj₁ x) (inj₁ y) with x ≟ y
... | yes refl = yes refl
... | no  x≠y  = no  (x≠y ∘ λ {refl → refl})
_≟_ {t₁ +ᵤ t₂} (inj₁ x) (inj₂ y) = no (λ ())
_≟_ {t₁ +ᵤ t₂} (inj₂ x) (inj₁ y) = no (λ ())
_≟_ {t₁ +ᵤ t₂} (inj₂ x) (inj₂ y) with x ≟ y
... | yes refl = yes refl
... | no  x≠y  = no  (x≠y ∘ λ {refl → refl})
_≟_ {t₁ ×ᵤ t₂} (x₁ , x₂) (y₁ , y₂) with x₁ ≟ y₁ | x₂ ≟ y₂
... | yes refl | yes refl = yes refl
... | yes refl | no x₂≠y₂ = no  (x₂≠y₂ ∘ cong proj₂)
... | no x₁≠y₁ | yes refl = no  (x₁≠y₁ ∘ cong proj₁)
... | no x₁≠y₁ | no x₂≠y₂ = no  (x₁≠y₁ ∘ cong proj₁)
_≟_ {𝟙/ t} ↻ ↻ = yes refl
_≟_ { - t} (- v₁) (- v₂) with v₁ ≟ v₂
... | yes refl = yes refl
... | no  neq  = no (λ {refl → neq refl})

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
  ⟨_∣_∣_⟩▷ : ∀ {A B} → (c : A ↔ B) → ⟦ A ⟧ → Context {A} {B} → State
  ［_∣_∣_］▷ : ∀ {A B} → (c : A ↔ B) → ⟦ B ⟧ → Context {A} {B} → State
  ⟨_∣_∣_⟩◁ : ∀ {A B} → (c : A ↔ B) → ⟦ A ⟧ → Context {A} {B} → State
  ［_∣_∣_］◁ : ∀ {A B} → (c : A ↔ B) → ⟦ B ⟧ → Context {A} {B} → State
  ⊠ : State

-- Reduction relation
data _↦_ : State → State → Set where
  ↦⃗₁  : ∀ {A B} {c : A ↔ B} {b : base c} {v : ⟦ A ⟧} {κ : Context}
       → ⟨ c ∣ v ∣ κ ⟩▷ ↦ ［ c ∣ δ c {b} v ∣ κ ］▷
  ↦⃗₂  : ∀ {A} {v : ⟦ A ⟧} {κ : Context} → ⟨ id↔ ∣ v ∣ κ ⟩▷ ↦ ［ id↔ ∣ v ∣ κ ］▷
  ↦⃗₃  : ∀ {A B C} {c₁ : A ↔ B} {c₂ : B ↔ C} {v : ⟦ A ⟧} {κ : Context}
       → ⟨ c₁ ⨾ c₂ ∣ v ∣ κ ⟩▷ ↦ ⟨ c₁ ∣ v ∣ ☐⨾ c₂ • κ ⟩▷
  ↦⃗₄  : ∀ {A B C D} {c₁ : A ↔ B} {c₂ : C ↔ D} {x : ⟦ A ⟧} {κ : Context}
       → ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ κ ⟩▷ ↦ ⟨ c₁ ∣ x ∣ ☐⊕ c₂ • κ ⟩▷
  ↦⃗₅  : ∀ {A B C D} {c₁ : A ↔ B} {c₂ : C ↔ D} {y : ⟦ C ⟧} {κ : Context}
       → ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ κ ⟩▷ ↦ ⟨ c₂ ∣ y ∣ c₁ ⊕☐• κ ⟩▷
  ↦⃗₆  : ∀ {A B C D} {c₁ : A ↔ B} {c₂ : C ↔ D} {x : ⟦ A ⟧} {y : ⟦ C ⟧} {κ : Context}
       → ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ κ ⟩▷ ↦ ⟨ c₁ ∣ x ∣ ☐⊗[ c₂ , y ]• κ ⟩▷
  ↦⃗₇  : ∀ {A B C} {c₁ : A ↔ B} {c₂ : B ↔ C} {v : ⟦ B ⟧} {κ : Context}
       → ［ c₁ ∣ v ∣ ☐⨾ c₂ • κ ］▷ ↦ ⟨ c₂ ∣ v ∣ (c₁ ⨾☐• κ) ⟩▷
  ↦⃗₈  : ∀ {A B C D} {c₁ : A ↔ B} {c₂ : C ↔ D} {x : ⟦ B ⟧} {y : ⟦ C ⟧} {κ : Context}
       → ［ c₁ ∣ x ∣ ☐⊗[ c₂ , y ]• κ ］▷ ↦ ⟨ c₂ ∣ y ∣ [ c₁ , x ]⊗☐• κ ⟩▷
  ↦⃗₉  : ∀ {A B C D} {c₁ : A ↔ B} {c₂ : C ↔ D} {x : ⟦ B ⟧} {y : ⟦ D ⟧} {κ : Context}
       → ［ c₂ ∣ y ∣ [ c₁ , x ]⊗☐• κ ］▷ ↦ ［ c₁ ⊗ c₂ ∣ (x , y) ∣ κ ］▷
  ↦⃗₁₀ : ∀ {A B C} {c₁ : A ↔ B} {c₂ : B ↔ C} {v : ⟦ C ⟧} {κ : Context}
       → ［ c₂ ∣ v ∣ (c₁ ⨾☐• κ) ］▷ ↦ ［ c₁ ⨾ c₂ ∣ v ∣ κ ］▷
  ↦⃗₁₁ : ∀ {A B C D} {c₁ : A ↔ B} {c₂ : C ↔ D} {x : ⟦ B ⟧} {κ : Context}
       → ［ c₁ ∣ x ∣ ☐⊕ c₂ • κ ］▷ ↦ ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ κ ］▷
  ↦⃗₁₂ : ∀ {A B C D} {c₁ : A ↔ B} {c₂ : C ↔ D} {y : ⟦ D ⟧} {κ : Context}
       → ［ c₂ ∣ y ∣ c₁ ⊕☐• κ ］▷ ↦ ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ κ ］▷
  ↦⃖₁  : ∀ {A B} {c : A ↔ B} {b : base c} {v : ⟦ A ⟧} {κ : Context}
      → ［ c ∣ δ c {b} v ∣ κ ］◁ ↦ ⟨ c ∣ v ∣ κ ⟩◁
  ↦⃖₂  : ∀ {A} {v : ⟦ A ⟧} {κ : Context} → ［ id↔ ∣ v ∣ κ ］◁ ↦ ⟨ id↔ ∣ v ∣ κ ⟩◁
  ↦⃖₃  : ∀ {A B C} {c₁ : A ↔ B} {c₂ : B ↔ C} {v : ⟦ A ⟧} {κ : Context}
      → ⟨ c₁ ∣ v ∣ ☐⨾ c₂ • κ ⟩◁ ↦ ⟨ c₁ ⨾ c₂ ∣ v ∣ κ ⟩◁
  ↦⃖₄  : ∀ {A B C D} {c₁ : A ↔ B} {c₂ : C ↔ D} {x : ⟦ A ⟧} {κ : Context}
      → ⟨ c₁ ∣ x ∣ ☐⊕ c₂ • κ ⟩◁ ↦ ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ κ ⟩◁
  ↦⃖₅  : ∀ {A B C D} {c₁ : A ↔ B} {c₂ : C ↔ D} {y : ⟦ C ⟧} {κ : Context}
      → ⟨ c₂ ∣ y ∣ c₁ ⊕☐• κ ⟩◁ ↦ ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ κ ⟩◁
  ↦⃖₆  : ∀ {A B C D} {c₁ : A ↔ B} {c₂ : C ↔ D} {x : ⟦ A ⟧} {y : ⟦ C ⟧} {κ : Context}
      → ⟨ c₁ ∣ x ∣ ☐⊗[ c₂ , y ]• κ ⟩◁ ↦ ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ κ ⟩◁
  ↦⃖₇  : ∀ {A B C} {c₁ : A ↔ B} {c₂ : B ↔ C} {v : ⟦ B ⟧} {κ : Context}
      → ⟨ c₂ ∣ v ∣ (c₁ ⨾☐• κ) ⟩◁ ↦ ［ c₁ ∣ v ∣ ☐⨾ c₂ • κ ］◁
  ↦⃖₈  : ∀ {A B C D} {c₁ : A ↔ B} {c₂ : C ↔ D} {x : ⟦ B ⟧} {y : ⟦ C ⟧} {κ : Context}
      → ⟨ c₂ ∣ y ∣ [ c₁ , x ]⊗☐• κ ⟩◁ ↦ ［ c₁ ∣ x ∣ ☐⊗[ c₂ , y ]• κ ］◁
  ↦⃖₉  : ∀ {A B C D} {c₁ : A ↔ B} {c₂ : C ↔ D} {x : ⟦ B ⟧} {y : ⟦ D ⟧} {κ : Context}
      → ［ c₁ ⊗ c₂ ∣ (x , y) ∣ κ ］◁ ↦ ［ c₂ ∣ y ∣ [ c₁ , x ]⊗☐• κ ］◁
  ↦⃖₁₀ : ∀ {A B C} {c₁ : A ↔ B} {c₂ : B ↔ C} {v : ⟦ C ⟧} {κ : Context}
      → ［ c₁ ⨾ c₂ ∣ v ∣ κ ］◁ ↦ ［ c₂ ∣ v ∣ (c₁ ⨾☐• κ) ］◁
  ↦⃖₁₁ : ∀ {A B C D} {c₁ : A ↔ B} {c₂ : C ↔ D} {x : ⟦ B ⟧} {κ : Context}
      → ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ κ ］◁ ↦ ［ c₁ ∣ x ∣ ☐⊕ c₂ • κ ］◁
  ↦⃖₁₂ : ∀ {A B C D} {c₁ : A ↔ B} {c₂ : C ↔ D} {y : ⟦ D ⟧} {κ : Context}
      → ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ κ ］◁ ↦ ［ c₂ ∣ y ∣ c₁ ⊕☐• κ ］◁
  ↦η₊₁ : ∀ {A} {v : ⟦ A ⟧} {κ : Context} → ［ η₊ ∣ inj₁ v ∣ κ ］◁ ↦ ［ η₊ ∣ inj₂ (- v) ∣ κ ］▷
  ↦η₊₂ : ∀ {A} {v : ⟦ A ⟧} {κ : Context} → ［ η₊ ∣ inj₂ (- v) ∣ κ ］◁ ↦ ［ η₊ ∣ inj₁ v ∣ κ ］▷
  ↦ε₊₁ : ∀ {A} {v : ⟦ A ⟧} {κ : Context} → ⟨ ε₊ ∣ inj₁ v ∣ κ ⟩▷ ↦ ⟨ ε₊ ∣ inj₂ (- v) ∣ κ ⟩◁
  ↦ε₊₂ : ∀ {A} {v : ⟦ A ⟧} {κ : Context} → ⟨ ε₊ ∣ inj₂ (- v) ∣ κ ⟩▷ ↦ ⟨ ε₊ ∣ inj₁ v ∣ κ ⟩◁
  ↦⃗ηₓ  : ∀ {A} {v : ⟦ A ⟧} {κ : Context} → ⟨ ηₓ v ∣ tt ∣ κ ⟩▷ ↦ ［ ηₓ v ∣ (v , ↻) ∣ κ ］▷
  ↦⃖ηₓ₁ : ∀ {A} {v v' : ⟦ A ⟧} {κ : Context} {eq  : v ≡ v'} → ［ ηₓ v ∣ (v' , ↻) ∣ κ ］◁ ↦ ⟨ ηₓ v ∣ tt ∣ κ ⟩◁
  ↦⃖ηₓ₂ : ∀ {A} {v v' : ⟦ A ⟧} {κ : Context} {neq : v ≢ v'} → ［ ηₓ v ∣ (v' , ↻) ∣ κ ］◁ ↦ ⊠
  ↦⃗εₓ₁ : ∀ {A} {v v' : ⟦ A ⟧} {κ : Context} {eq  : v ≡ v'} → ⟨ εₓ v ∣ (v' , ↻) ∣ κ ⟩▷ ↦ ［ εₓ v ∣ tt ∣ κ ］▷
  ↦⃗εₓ₂ : ∀ {A} {v v' : ⟦ A ⟧} {κ : Context} {neq : v ≢ v'} → ⟨ εₓ v ∣ (v' , ↻) ∣ κ ⟩▷ ↦ ⊠
  ↦⃖εₓ  : ∀ {A} {v : ⟦ A ⟧} {κ : Context} → ［ εₓ v ∣ tt ∣ κ ］◁ ↦ ⟨ εₓ v ∣ (v , ↻) ∣ κ ⟩◁
