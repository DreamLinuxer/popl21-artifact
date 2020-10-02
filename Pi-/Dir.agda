module Pi-.Dir where
open import Relation.Binary.PropositionalEquality

data Dir : Set where
  ◁ : Dir
  ▷ : Dir

-ᵈⁱʳ_ : Dir → Dir
-ᵈⁱʳ ▷ = ◁
-ᵈⁱʳ ◁ = ▷

_×ᵈⁱʳ_ : Dir → Dir → Dir
◁ ×ᵈⁱʳ ◁ = ▷
◁ ×ᵈⁱʳ ▷ = ◁
▷ ×ᵈⁱʳ ◁ = ◁
▷ ×ᵈⁱʳ ▷ = ▷

identˡᵈⁱʳ : ∀ d → ▷ ×ᵈⁱʳ d ≡ d
identˡᵈⁱʳ ◁ = refl
identˡᵈⁱʳ ▷ = refl

assoclᵈⁱʳ : ∀ d₁ d₂ d₃ → d₁ ×ᵈⁱʳ (d₂ ×ᵈⁱʳ d₃) ≡ (d₁ ×ᵈⁱʳ d₂) ×ᵈⁱʳ d₃
assoclᵈⁱʳ ◁ ◁ ◁ = refl
assoclᵈⁱʳ ◁ ◁ ▷ = refl
assoclᵈⁱʳ ◁ ▷ ◁ = refl
assoclᵈⁱʳ ◁ ▷ ▷ = refl
assoclᵈⁱʳ ▷ ◁ ◁ = refl
assoclᵈⁱʳ ▷ ◁ ▷ = refl
assoclᵈⁱʳ ▷ ▷ ◁ = refl
assoclᵈⁱʳ ▷ ▷ ▷ = refl

commᵈⁱʳ : ∀ d₁ d₂ → d₁ ×ᵈⁱʳ d₂ ≡ d₂ ×ᵈⁱʳ d₁
commᵈⁱʳ ◁ ◁ = refl
commᵈⁱʳ ◁ ▷ = refl
commᵈⁱʳ ▷ ◁ = refl
commᵈⁱʳ ▷ ▷ = refl

assocl-commᵈⁱʳ : ∀ d₁ d₂ d₃ → d₁ ×ᵈⁱʳ (d₂ ×ᵈⁱʳ d₃) ≡ (d₂ ×ᵈⁱʳ d₁) ×ᵈⁱʳ d₃
assocl-commᵈⁱʳ ◁ ◁ ◁ = refl
assocl-commᵈⁱʳ ◁ ◁ ▷ = refl
assocl-commᵈⁱʳ ◁ ▷ ◁ = refl
assocl-commᵈⁱʳ ◁ ▷ ▷ = refl
assocl-commᵈⁱʳ ▷ ◁ ◁ = refl
assocl-commᵈⁱʳ ▷ ◁ ▷ = refl
assocl-commᵈⁱʳ ▷ ▷ ◁ = refl
assocl-commᵈⁱʳ ▷ ▷ ▷ = refl

assoc-commᵈⁱʳ : ∀ d₁ d₂ d₃ → d₁ ×ᵈⁱʳ (d₂ ×ᵈⁱʳ d₃) ≡ d₂ ×ᵈⁱʳ (d₁ ×ᵈⁱʳ d₃)
assoc-commᵈⁱʳ ◁ ◁ ◁ = refl
assoc-commᵈⁱʳ ◁ ◁ ▷ = refl
assoc-commᵈⁱʳ ◁ ▷ ◁ = refl
assoc-commᵈⁱʳ ◁ ▷ ▷ = refl
assoc-commᵈⁱʳ ▷ ◁ ◁ = refl
assoc-commᵈⁱʳ ▷ ◁ ▷ = refl
assoc-commᵈⁱʳ ▷ ▷ ◁ = refl
assoc-commᵈⁱʳ ▷ ▷ ▷ = refl
