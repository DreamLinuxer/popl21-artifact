module Pi.NoRepeat where
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Pi.Syntax
open import Pi.Opsem
open import Pi.AuxLemmas
import RevNoRepeat

-- Forward deterministic
deterministic : ∀ {st st₁ st₂} → st ↦ st₁ → st ↦ st₂ → st₁ ≡ st₂
deterministic (↦₁ {b = b₁}) (↦₁ {b = b₂}) with base-is-prop _ b₁ b₂
... | refl = refl
deterministic ↦₂ ↦₂ = refl
deterministic ↦₃ ↦₃ = refl
deterministic ↦₄ ↦₄ = refl
deterministic ↦₅ ↦₅ = refl
deterministic ↦₆ ↦₆ = refl
deterministic ↦₇ ↦₇ = refl
deterministic ↦₈ ↦₈ = refl
deterministic ↦₉ ↦₉ = refl
deterministic ↦₁₀ ↦₁₀ = refl
deterministic ↦₁₁ ↦₁₁ = refl
deterministic ↦₁₂ ↦₁₂ = refl

-- Backward deterministic
deterministicᵣₑᵥ : ∀ {st st₁ st₂} → st₁ ↦ st → st₂ ↦ st → st₁ ≡ st₂
deterministicᵣₑᵥ {［ c ∣ _ ∣ κ ］} {⟨ c ∣ v ∣ κ ⟩} {⟨ c' ∣ v' ∣ κ' ⟩} ↦₁ r with Lemma₁ r
... | refl , refl with Lemma₂ r
deterministicᵣₑᵥ {［ unite₊l  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₂ y        ∣ κ ⟩} {⟨ _ ∣ inj₂ y        ∣ κ ⟩} ↦₁ ↦₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ uniti₊l  ∣ _ ∣ κ ］} {⟨ _ ∣ v             ∣ κ ⟩} {⟨ _ ∣ v             ∣ κ ⟩} ↦₁ ↦₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ swap₊    ∣ _ ∣ κ ］} {⟨ _ ∣ inj₁ x        ∣ κ ⟩} {⟨ _ ∣ inj₁ x        ∣ κ ⟩} ↦₁ ↦₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ swap₊    ∣ _ ∣ κ ］} {⟨ _ ∣ inj₂ y        ∣ κ ⟩} {⟨ _ ∣ inj₂ y        ∣ κ ⟩} ↦₁ ↦₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₁ x        ∣ κ ⟩} {⟨ _ ∣ inj₁ x        ∣ κ ⟩} ↦₁ ↦₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₁ x        ∣ κ ⟩} {⟨ _ ∣ inj₂ (inj₁ y) ∣ κ ⟩} ↦₁ () | refl , refl | refl , refl
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₁ x        ∣ κ ⟩} {⟨ _ ∣ inj₂ (inj₂ z) ∣ κ ⟩} ↦₁ () | refl , refl | refl , refl
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₂ (inj₁ y) ∣ κ ⟩} {⟨ _ ∣ inj₂ (inj₁ y) ∣ κ ⟩} ↦₁ ↦₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₂ (inj₂ z) ∣ κ ⟩} {⟨ _ ∣ inj₂ (inj₂ z) ∣ κ ⟩} ↦₁ ↦₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₁ (inj₁ x) ∣ κ ⟩} {⟨ _ ∣ inj₁ (inj₁ x) ∣ κ ⟩} ↦₁ ↦₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₁ (inj₂ y) ∣ κ ⟩} {⟨ _ ∣ inj₁ (inj₂ y) ∣ κ ⟩} ↦₁ ↦₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₂ z        ∣ κ ⟩} {⟨ _ ∣ inj₁ (inj₁ x) ∣ κ ⟩} ↦₁ () | refl , refl | refl , refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₂ z        ∣ κ ⟩} {⟨ _ ∣ inj₁ (inj₂ y) ∣ κ ⟩} ↦₁ () | refl , refl | refl , refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₂ z        ∣ κ ⟩} {⟨ _ ∣ inj₂ z        ∣ κ ⟩} ↦₁ ↦₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ unite⋆l  ∣ _ ∣ κ ］} {⟨ _ ∣ (tt , v)      ∣ κ ⟩} {⟨ _ ∣ (tt , v)      ∣ κ ⟩} ↦₁ ↦₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ uniti⋆l  ∣ _ ∣ κ ］} {⟨ _ ∣ v             ∣ κ ⟩} {⟨ _ ∣ v             ∣ κ ⟩} ↦₁ ↦₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ swap⋆    ∣ _ ∣ κ ］} {⟨ _ ∣ (x , y)       ∣ κ ⟩} {⟨ _ ∣ (x , y)       ∣ κ ⟩} ↦₁ ↦₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocl⋆  ∣ _ ∣ κ ］} {⟨ _ ∣ (x , (y , z)) ∣ κ ⟩} {⟨ _ ∣ (x , (y , z)) ∣ κ ⟩} ↦₁ ↦₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocr⋆  ∣ _ ∣ κ ］} {⟨ _ ∣ ((x , y) , z) ∣ κ ⟩} {⟨ _ ∣ ((x , y) , z) ∣ κ ⟩} ↦₁ ↦₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ dist     ∣ _ ∣ κ ］} {⟨ _ ∣ (inj₁ x , z)  ∣ κ ⟩} {⟨ _ ∣ (inj₁ x , z)  ∣ κ ⟩} ↦₁ ↦₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ dist     ∣ _ ∣ κ ］} {⟨ _ ∣ (inj₂ y , z)  ∣ κ ⟩} {⟨ _ ∣ (inj₂ y , z)  ∣ κ ⟩} ↦₁ ↦₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ factor   ∣ _ ∣ κ ］} {⟨ _ ∣ inj₁ (x , z)  ∣ κ ⟩} {⟨ _ ∣ inj₁ (x , z)  ∣ κ ⟩} ↦₁ ↦₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ factor   ∣ _ ∣ κ ］} {⟨ _ ∣ inj₂ (y , z)  ∣ κ ⟩} {⟨ _ ∣ inj₂ (y , z)  ∣ κ ⟩} ↦₁ ↦₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ unite₊l  ∣ _ ∣ κ ］} {⟨ _ ∣ v  ∣ κ ⟩} {［ c' ∣ v' ∣ κ' ］} ↦₁ ()
deterministicᵣₑᵥ {［ uniti₊l  ∣ _ ∣ κ ］} {⟨ _ ∣ v  ∣ κ ⟩} {［ c' ∣ v' ∣ κ' ］} ↦₁ ()
deterministicᵣₑᵥ {［ swap₊    ∣ _ ∣ κ ］} {⟨ _ ∣ v  ∣ κ ⟩} {［ c' ∣ v' ∣ κ' ］} ↦₁ ()
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］} {⟨ _ ∣ v  ∣ κ ⟩} {［ c' ∣ v' ∣ κ' ］} ↦₁ ()
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］} {⟨ _ ∣ v  ∣ κ ⟩} {［ c' ∣ v' ∣ κ' ］} ↦₁ ()
deterministicᵣₑᵥ {［ unite⋆l  ∣ _ ∣ κ ］} {⟨ _ ∣ v  ∣ κ ⟩} {［ c' ∣ v' ∣ κ' ］} ↦₁ ()
deterministicᵣₑᵥ {［ uniti⋆l  ∣ _ ∣ κ ］} {⟨ _ ∣ v  ∣ κ ⟩} {［ c' ∣ v' ∣ κ' ］} ↦₁ ()
deterministicᵣₑᵥ {［ swap⋆    ∣ _ ∣ κ ］} {⟨ _ ∣ v  ∣ κ ⟩} {［ c' ∣ v' ∣ κ' ］} ↦₁ ()
deterministicᵣₑᵥ {［ assocl⋆  ∣ _ ∣ κ ］} {⟨ _ ∣ v  ∣ κ ⟩} {［ c' ∣ v' ∣ κ' ］} ↦₁ ()
deterministicᵣₑᵥ {［ assocr⋆  ∣ _ ∣ κ ］} {⟨ _ ∣ v  ∣ κ ⟩} {［ c' ∣ v' ∣ κ' ］} ↦₁ ()
deterministicᵣₑᵥ {［ dist     ∣ _ ∣ κ ］} {⟨ _ ∣ v  ∣ κ ⟩} {［ c' ∣ v' ∣ κ' ］} ↦₁ ()
deterministicᵣₑᵥ {［ factor   ∣ _ ∣ κ ］} {⟨ _ ∣ v  ∣ κ ⟩} {［ c' ∣ v' ∣ κ' ］} ↦₁ ()
deterministicᵣₑᵥ {［ id↔      ∣ _ ∣ κ ］} {⟨ _ ∣ v  ∣ κ ⟩} {［ c' ∣ v' ∣ κ' ］} (↦₁ {b = ()})
deterministicᵣₑᵥ {［ c₁ ⨾ c₂  ∣ _ ∣ κ ］} {⟨ _ ∣ v  ∣ κ ⟩} {［ c' ∣ v' ∣ κ' ］} (↦₁ {b = ()})
deterministicᵣₑᵥ {［ c₁ ⊕ c₂  ∣ _ ∣ κ ］} {⟨ _ ∣ v  ∣ κ ⟩} {［ c' ∣ v' ∣ κ' ］} (↦₁ {b = ()})
deterministicᵣₑᵥ {［ c₁ ⊗ c₂  ∣ _ ∣ κ ］} {⟨ _ ∣ v  ∣ κ ⟩} {［ c' ∣ v' ∣ κ' ］} (↦₁ {b = ()})
deterministicᵣₑᵥ ↦₂ ↦₂ = refl
deterministicᵣₑᵥ ↦₃ ↦₃ = refl
deterministicᵣₑᵥ ↦₄ ↦₄ = refl
deterministicᵣₑᵥ ↦₅ ↦₅ = refl
deterministicᵣₑᵥ ↦₆ ↦₆ = refl
deterministicᵣₑᵥ ↦₇ ↦₇ = refl
deterministicᵣₑᵥ ↦₈ ↦₈ = refl
deterministicᵣₑᵥ ↦₉ ↦₉ = refl
deterministicᵣₑᵥ ↦₁₀ ↦₁₀ = refl
deterministicᵣₑᵥ {［ c₁ ⊕ c₂ ∣ inj₁ v ∣ κ ］} {_} {⟨ c₁' ⊕ c₂' ∣ v' ∣ κ' ⟩} ↦₁₁ r with Lemma₁ r
... | refl , refl with Lemma₂ r
... | refl , refl with Lemma₃ r
... | inj₂ refl with Lemma₄ r
... | inj₁ ()
... | inj₂ ()
deterministicᵣₑᵥ {［ c₁ ⊕ c₂ ∣ inj₁ v ∣ κ ］} {［ c₁ ∣ v ∣ ☐⊕ c₂ • κ ］} {［ c₁ ∣ v ∣ ☐⊕ c₂ • κ ］} ↦₁₁ ↦₁₁ = refl
deterministicᵣₑᵥ {［ c₁ ⊕ c₂ ∣ inj₂ y ∣ κ ］} {［ c₂ ∣ y ∣ c₁ ⊕☐• κ ］} {⟨ c ∣ x ∣ x₁ ⟩} ↦₁₂ r with Lemma₁ r
... | refl , refl with Lemma₂ r
... | refl , refl with Lemma₃ r
... | inj₂ refl with Lemma₄ r
... | inj₂ ()
deterministicᵣₑᵥ {［ c₁ ⊕ c₂ ∣ inj₂ y ∣ κ ］} {［ c₂ ∣ y ∣ c₁ ⊕☐• κ ］} {［ c₂ ∣ y ∣ (c₁ ⊕☐• κ) ］} ↦₁₂ ↦₁₂ = refl

-- Non-repeating Lemma
open RevNoRepeat (record { State = State
                         ; _↦_ = _↦_
                         ; deterministic = deterministic
                         ; deterministicᵣₑᵥ = deterministicᵣₑᵥ }) public
