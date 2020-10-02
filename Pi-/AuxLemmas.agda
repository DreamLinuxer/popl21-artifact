module Pi-.AuxLemmas where
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
open import Data.List as L
open import Function using (_∘_)
open import Pi-.Syntax
open import Pi-.Opsem

Lemma₁ : ∀ {A B C D v v' κ κ'} {c : A ↔ B} {c' : C ↔ D}
       → ［ c ∣ v ∣ κ ］◁ ↦ ⟨ c' ∣ v' ∣ κ' ⟩◁
       → A ≡ C × B ≡ D
Lemma₁ ↦⃖₁ = refl , refl
Lemma₁ ↦⃖₂ = refl , refl

Lemma₂ : ∀ {A B v v' κ κ'} {c c' : A ↔ B}
       → ［ c ∣ v ∣ κ ］◁ ↦ ⟨ c' ∣ v' ∣ κ' ⟩◁
       → c ≡ c' × κ ≡ κ'
Lemma₂ ↦⃖₁ = refl , refl
Lemma₂ ↦⃖₂ = refl , refl

Lemma₃ : ∀ {A B v v' κ} {c : A ↔ B}
       → ［ c ∣ v ∣ κ ］◁ ↦ ⟨ c ∣ v' ∣ κ ⟩◁
       → base c ⊎ A ≡ B
Lemma₃ (↦⃖₁ {b = b}) = inj₁ b
Lemma₃ ↦⃖₂ = inj₂ refl

Lemma₄ : ∀ {A v v' κ} {c : A ↔ A}
       → ［ c ∣ v ∣ κ ］◁ ↦ ⟨ c ∣ v' ∣ κ ⟩◁
       → base c ⊎ c ≡ id↔
Lemma₄ (↦⃖₁ {b = b}) = inj₁ b
Lemma₄ ↦⃖₂ = inj₂ refl

Lemma₅ : ∀ {A B C D v v' κ κ'} {c : A ↔ B} {c' : C ↔ D}
       → ［ c ∣ v ∣ κ ］◁ ↦ ［ c' ∣ v' ∣ κ' ］▷
       → A ≡ C × B ≡ D
Lemma₅ ↦η₁ = refl , refl
Lemma₅ ↦η₂ = refl , refl

Lemma₆ : ∀ {A B v v' κ κ'} {c c' : A ↔ B}
       → ［ c ∣ v ∣ κ ］◁ ↦ ［ c' ∣ v' ∣ κ' ］▷
       → c ≡ c' × κ ≡ κ'
Lemma₆ ↦η₁ = refl , refl
Lemma₆ ↦η₂ = refl , refl

Lemma₇ : ∀ {A B v v' κ} {c : A ↔ B}
       → ［ c ∣ v ∣ κ ］◁ ↦ ［ c ∣ v' ∣ κ ］▷
       →  A ≡ 𝟘
Lemma₇ ↦η₁ = refl
Lemma₇ ↦η₂ = refl

Lemma₈ : ∀ {A B C D v v' κ κ'} {c : A ↔ B} {c' : C ↔ D}
           → ⟨ c ∣ v ∣ κ ⟩▷ ↦ ［ c' ∣ v' ∣ κ' ］▷
           → A ≡ C × B ≡ D
Lemma₈ ↦⃗₁ = refl , refl
Lemma₈ ↦⃗₂ = refl , refl

Lemma₉ : ∀ {A B v v' κ κ'} {c c' : A ↔ B}
           → ⟨ c ∣ v ∣ κ ⟩▷ ↦ ［ c' ∣ v' ∣ κ' ］▷
           → c ≡ c' × κ ≡ κ'
Lemma₉ ↦⃗₁ = refl , refl
Lemma₉ ↦⃗₂ = refl , refl

Lemma₁₀ : ∀ {A B v v' κ} {c : A ↔ B}
        → (r : ⟨ c ∣ v ∣ κ ⟩▷ ↦ ［ c ∣ v' ∣ κ ］▷)
        → base c ⊎ A ≡ B
Lemma₁₀ (↦⃗₁ {b = b}) = inj₁ b
Lemma₁₀ ↦⃗₂ = inj₂ refl

Lemma₁₁ : ∀ {A v v' κ} {c : A ↔ A}
       → (r : ⟨ c ∣ v ∣ κ ⟩▷ ↦ ［ c ∣ v' ∣ κ ］▷)
       → base c ⊎ c ≡ id↔
Lemma₁₁ (↦⃗₁ {b = b}) = inj₁ b
Lemma₁₁ ↦⃗₂ = inj₂ refl
