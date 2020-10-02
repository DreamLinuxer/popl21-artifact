module Pi.AuxLemmas where
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Pi.Syntax
open import Pi.Opsem

Lemma₁ : ∀ {A B C D v v' κ κ'} {c : A ↔ B} {c' : C ↔ D}
           → ⟨ c ∣ v ∣ κ ⟩ ↦ ［ c' ∣ v' ∣ κ' ］
           → A ≡ C × B ≡ D
Lemma₁ ↦₁ = refl , refl
Lemma₁ ↦₂ = refl , refl

Lemma₂ : ∀ {A B v v' κ κ'} {c c' : A ↔ B}
           → ⟨ c ∣ v ∣ κ ⟩ ↦ ［ c' ∣ v' ∣ κ' ］
           → c ≡ c' × κ ≡ κ'
Lemma₂ ↦₁ = refl , refl
Lemma₂ ↦₂ = refl , refl

Lemma₃ : ∀ {A B v v' κ} {c : A ↔ B}
           → (r : ⟨ c ∣ v ∣ κ ⟩ ↦ ［ c ∣ v' ∣ κ ］)
           → base c ⊎ A ≡ B
Lemma₃ (↦₁ {b = b}) = inj₁ b
Lemma₃ ↦₂ = inj₂ refl

Lemma₄ : ∀ {A v v' κ} {c : A ↔ A}
           → (r : ⟨ c ∣ v ∣ κ ⟩ ↦ ［ c ∣ v' ∣ κ ］)
           → base c ⊎ c ≡ id↔
Lemma₄ {c = swap₊} ↦₁ = inj₁ tt
Lemma₄ {c = swap⋆} ↦₁ = inj₁ tt
Lemma₄ ↦₂ = inj₂ refl
