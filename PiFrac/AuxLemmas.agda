module PiFrac.AuxLemmas where
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Sum
open import Data.Product
open import Relation.Binary.Core
open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_)
open import PiFrac.Syntax
open import PiFrac.Opsem

Lemma₁ : ∀ {A B C D v v' κ κ'} {c : A ↔ B} {c' : C ↔ D}
       → ⟨ c ∣ v ∣ κ ⟩ ↦ ［ c' ∣ v' ∣ κ' ］
       → (A ≡ C × B ≡ D)
Lemma₁ ↦₁ = refl , refl
Lemma₁ ↦₂ = refl , refl
Lemma₁ ↦η = refl , refl
Lemma₁ ↦ε₁ = refl , refl

Lemma₂ : ∀ {A B v v' κ κ'} {c c' : A ↔ B}
       → ⟨ c ∣ v ∣ κ ⟩ ↦ ［ c' ∣ v' ∣ κ' ］
       → c ≡ c' × κ ≡ κ'
Lemma₂ ↦₁ = refl , refl
Lemma₂ ↦₂ = refl , refl
Lemma₂ ↦η = refl , refl
Lemma₂ ↦ε₁ = refl , refl

Lemma₃ : ∀ {A B v v' κ} {c : A ↔ B}
       → (r : ⟨ c ∣ v ∣ κ ⟩ ↦ ［ c ∣ v' ∣ κ ］)
       → base c ⊎ dual c ⊎ A ≡ B
Lemma₃ (↦₁ {b = b}) = inj₁ b
Lemma₃ ↦₂ = inj₂ (inj₂ refl)
Lemma₃ ↦η = inj₂ (inj₁ tt)
Lemma₃ ↦ε₁ = inj₂ (inj₁ tt)

Lemma₄ : ∀ {A v v' κ} {c : A ↔ A}
       → (r : ⟨ c ∣ v ∣ κ ⟩ ↦ ［ c ∣ v' ∣ κ ］)
       → base c ⊎ c ≡ id↔
Lemma₄ {c = swap₊} ↦₁ = inj₁ tt
Lemma₄ {c = swap⋆} ↦₁ = inj₁ tt
Lemma₄ ↦₂ = inj₂ refl

Lemma₅ : ∀ {A B v v' b κ} {c : A ↔ B ×ᵤ 𝟙/ b}
        → (r : ⟨ c ∣ v ∣ κ ⟩ ↦ ［ c ∣ v' ∣ κ ］)
        → base c ⊎ (b , ↻) ≡ v' ⊎ ¬ (dual c)
Lemma₅ (↦₁ {b = b}) = inj₁ b
Lemma₅ ↦₂ = inj₂ (inj₂ (λ ()))
Lemma₅ ↦η = inj₂ (inj₁ refl)

Lemma₆ : ∀ {A v v' κ} → v ≢ v' → ∄[ st' ] (st' ↦ ［ ηₓ {A} v ∣ v' , ↻ ∣ κ ］)
Lemma₆ neq (⟨ _ ∣ v ∣ _ ⟩ , r) with Lemma₁ r
... | refl , refl with Lemma₂ r
... | refl , refl with Lemma₅ r
... | inj₂ (inj₁ refl) = neq refl
... | inj₂ (inj₂ nd) = nd tt
