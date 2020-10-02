module PiQ.AuxLemmas where
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Sum
open import Data.Product
open import Data.Maybe
open import Relation.Binary.Core
open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import PiQ.Syntax
open import PiQ.Opsem

Lemma₁ : ∀ {A B C D v v' κ κ'} {c : A ↔ B} {c' : C ↔ D}
       → ［ c ∣ v ∣ κ ］◁ ↦ ⟨ c' ∣ v' ∣ κ' ⟩◁
       → A ≡ C × B ≡ D
Lemma₁ ↦⃖₁ = refl , refl
Lemma₁ ↦⃖₂ = refl , refl
Lemma₁ ↦⃖ηₓ₁ = refl , refl
Lemma₁ ↦⃖εₓ = refl , refl

Lemma₂ : ∀ {A B v v' κ κ'} {c c' : A ↔ B}
       → ［ c ∣ v ∣ κ ］◁ ↦ ⟨ c' ∣ v' ∣ κ' ⟩◁
       → c ≡ c' × κ ≡ κ'
Lemma₂ ↦⃖₁ = refl , refl
Lemma₂ ↦⃖₂ = refl , refl
Lemma₂ ↦⃖ηₓ₁ = refl , refl
Lemma₂ ↦⃖εₓ = refl , refl

Lemma₃ : ∀ {A B v v' κ} {c : A ↔ B}
       → ［ c ∣ v ∣ κ ］◁ ↦ ⟨ c ∣ v' ∣ κ ⟩◁
       → base c ⊎ dual c ⊎ A ≡ B
Lemma₃ (↦⃖₁ {b = b}) = inj₁ b
Lemma₃ ↦⃖₂ = inj₂ (inj₂ refl)
Lemma₃ ↦⃖ηₓ₁ = inj₂ (inj₁ tt)
Lemma₃ ↦⃖εₓ = inj₂ (inj₁ tt)

Lemma₄ : ∀ {A v v' κ} {c : A ↔ A}
       → ［ c ∣ v ∣ κ ］◁ ↦ ⟨ c ∣ v' ∣ κ ⟩◁
       → base c ⊎ c ≡ id↔
Lemma₄ (↦⃖₁ {b = b}) = inj₁ b
Lemma₄ ↦⃖₂ = inj₂ refl

Lemma₅ : ∀ {A B C D v v' κ κ'} {c : A ↔ B} {c' : C ↔ D}
       → ［ c ∣ v ∣ κ ］◁ ↦ ［ c' ∣ v' ∣ κ' ］▷
       → A ≡ C × B ≡ D
Lemma₅ ↦η₊₁ = refl , refl
Lemma₅ ↦η₊₂ = refl , refl

Lemma₆ : ∀ {A B v v' κ κ'} {c c' : A ↔ B}
       → ［ c ∣ v ∣ κ ］◁ ↦ ［ c' ∣ v' ∣ κ' ］▷
       → c ≡ c' × κ ≡ κ'
Lemma₆ ↦η₊₁ = refl , refl
Lemma₆ ↦η₊₂ = refl , refl

Lemma₇ : ∀ {A B v v' κ} {c : A ↔ B}
       → ［ c ∣ v ∣ κ ］◁ ↦ ［ c ∣ v' ∣ κ ］▷
       →  A ≡ 𝟘
Lemma₇ ↦η₊₁ = refl
Lemma₇ ↦η₊₂ = refl

Lemma₈ : ∀ {A B v κ} {c : A ↔ B}
       → ［ c ∣ v ∣ κ ］◁ ↦ ⊠
       → ¬ (base c)
Lemma₈ ↦⃖ηₓ₂ ()

Lemma₉ : ∀ {A B} {κ : Context} {v : ⟦ B ⟧} {v' : ⟦ A ⟧} {c : A ↔ B}
       → ［ c ∣ v ∣ κ ］◁ ↦ ⟨ c ∣ v' ∣ κ ⟩◁
       → ［ c ∣ v ∣ κ ］◁ ↦ ⊠
       → ⊥
Lemma₉ r' r with Lemma₈ r
Lemma₉ (↦⃖₁ {b = b}) r | nb = nb b
Lemma₉ (↦⃖ηₓ₁ {eq = eq}) (↦⃖ηₓ₂ {neq = neq}) | _ = ⊥-elim (neq eq)

Lemma₁₀ : ∀ {A B C D v v' κ κ'} {c : A ↔ B} {c' : C ↔ D}
        → ⟨ c ∣ v ∣ κ ⟩▷ ↦ ［ c' ∣ v' ∣ κ' ］▷
        → (A ≡ C × B ≡ D)
Lemma₁₀ ↦⃗₁ = refl , refl
Lemma₁₀ ↦⃗₂ = refl , refl
Lemma₁₀ ↦⃗ηₓ = refl , refl
Lemma₁₀ ↦⃗εₓ₁ = refl , refl

Lemma₁₁ : ∀ {A B v v' κ κ'} {c c' : A ↔ B}
        → ⟨ c ∣ v ∣ κ ⟩▷ ↦ ［ c' ∣ v' ∣ κ' ］▷
        → c ≡ c' × κ ≡ κ'
Lemma₁₁ ↦⃗₁ = refl , refl
Lemma₁₁ ↦⃗₂ = refl , refl
Lemma₁₁ ↦⃗ηₓ = refl , refl
Lemma₁₁ ↦⃗εₓ₁ = refl , refl

Lemma₁₂ : ∀ {A B v v' κ} {c : A ↔ B}
        → (r : ⟨ c ∣ v ∣ κ ⟩▷ ↦ ［ c ∣ v' ∣ κ ］▷)
        → base c ⊎ dual c ⊎ A ≡ B
Lemma₁₂ (↦⃗₁ {b = b}) = inj₁ b
Lemma₁₂ ↦⃗₂ = inj₂ (inj₂ refl)
Lemma₁₂ ↦⃗ηₓ = inj₂ (inj₁ tt)
Lemma₁₂ ↦⃗εₓ₁ = inj₂ (inj₁ tt)

Lemma₁₃ : ∀ {A v v' κ} {c : A ↔ A}
        → (r : ⟨ c ∣ v ∣ κ ⟩▷ ↦ ［ c ∣ v' ∣ κ ］▷)
        → base c ⊎ c ≡ id↔
Lemma₁₃ (↦⃗₁ {b = b}) = inj₁ b
Lemma₁₃ ↦⃗₂ = inj₂ refl
