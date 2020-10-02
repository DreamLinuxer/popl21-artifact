module Pi-.NoRepeat where
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
open import Pi-.AuxLemmas
import RevNoRepeat

-- Forward deterministic
deterministic : ∀ {st st₁ st₂} → st ↦ st₁ → st ↦ st₂ → st₁ ≡ st₂
deterministic (↦⃗₁ {b = b₁}) (↦⃗₁ {b = b₂}) with base-is-prop _ b₁ b₂
... | refl = refl
deterministic ↦⃗₂ ↦⃗₂ = refl
deterministic ↦⃗₃ ↦⃗₃ = refl
deterministic ↦⃗₄ ↦⃗₄ = refl
deterministic ↦⃗₅ ↦⃗₅ = refl
deterministic ↦⃗₆ ↦⃗₆ = refl
deterministic ↦⃗₇ ↦⃗₇ = refl
deterministic ↦⃗₈ ↦⃗₈ = refl
deterministic ↦⃗₉ ↦⃗₉ = refl
deterministic ↦⃗₁₀ ↦⃗₁₀ = refl
deterministic ↦⃗₁₁ ↦⃗₁₁ = refl
deterministic ↦⃗₁₂ ↦⃗₁₂ = refl
deterministic {［ c ∣ _ ∣ κ ］◁} {⟨ _ ∣ v ∣ _ ⟩◁} {［ _ ∣ _ ∣ _ ］▷} ↦⃖₁ r with Lemma₅ r
... | refl , refl with Lemma₆ r
... | refl , refl with Lemma₇ r
... | refl with v
... | ()
deterministic {［ c ∣ _ ∣ _ ］◁} {⟨ _ ∣ v ∣ _ ⟩◁} {⟨ _ ∣ v' ∣ _ ⟩◁} ↦⃖₁ r with Lemma₁ r
... | refl , refl with Lemma₂ r
deterministic {［ unite₊l  ∣ _ ∣ κ ］◁} {⟨ _ ∣ inj₂ y        ∣ κ ⟩◁} {⟨ _ ∣ inj₂ y        ∣ κ ⟩◁} ↦⃖₁ ↦⃖₁ | refl , refl | refl , refl = refl
deterministic {［ uniti₊l  ∣ _ ∣ κ ］◁} {⟨ _ ∣ v             ∣ κ ⟩◁} {⟨ _ ∣ v             ∣ κ ⟩◁} ↦⃖₁ ↦⃖₁ | refl , refl | refl , refl = refl
deterministic {［ swap₊    ∣ _ ∣ κ ］◁} {⟨ _ ∣ inj₁ x        ∣ κ ⟩◁} {⟨ _ ∣ inj₁ x        ∣ κ ⟩◁} ↦⃖₁ ↦⃖₁ | refl , refl | refl , refl = refl
deterministic {［ swap₊    ∣ _ ∣ κ ］◁} {⟨ _ ∣ inj₂ y        ∣ κ ⟩◁} {⟨ _ ∣ inj₂ y        ∣ κ ⟩◁} ↦⃖₁ ↦⃖₁ | refl , refl | refl , refl = refl
deterministic {［ assocl₊  ∣ _ ∣ κ ］◁} {⟨ _ ∣ inj₁ x        ∣ κ ⟩◁} {⟨ _ ∣ inj₁ x        ∣ κ ⟩◁} ↦⃖₁ ↦⃖₁ | refl , refl | refl , refl = refl
deterministic {［ assocl₊  ∣ _ ∣ κ ］◁} {⟨ _ ∣ inj₁ x        ∣ κ ⟩◁} {⟨ _ ∣ inj₂ (inj₁ y) ∣ κ ⟩◁} ↦⃖₁ (() ) | refl , refl | refl , refl
deterministic {［ assocl₊  ∣ _ ∣ κ ］◁} {⟨ _ ∣ inj₁ x        ∣ κ ⟩◁} {⟨ _ ∣ inj₂ (inj₂ z) ∣ κ ⟩◁} ↦⃖₁ (() ) | refl , refl | refl , refl
deterministic {［ assocl₊  ∣ _ ∣ κ ］◁} {⟨ _ ∣ inj₂ (inj₁ y) ∣ κ ⟩◁} {⟨ _ ∣ inj₂ (inj₁ y) ∣ κ ⟩◁} ↦⃖₁ ↦⃖₁ | refl , refl | refl , refl = refl
deterministic {［ assocl₊  ∣ _ ∣ κ ］◁} {⟨ _ ∣ inj₂ (inj₂ z) ∣ κ ⟩◁} {⟨ _ ∣ inj₂ (inj₂ z) ∣ κ ⟩◁} ↦⃖₁ ↦⃖₁ | refl , refl | refl , refl = refl
deterministic {［ assocr₊  ∣ _ ∣ κ ］◁} {⟨ _ ∣ inj₁ (inj₁ x) ∣ κ ⟩◁} {⟨ _ ∣ inj₁ (inj₁ x) ∣ κ ⟩◁} ↦⃖₁ ↦⃖₁ | refl , refl | refl , refl = refl
deterministic {［ assocr₊  ∣ _ ∣ κ ］◁} {⟨ _ ∣ inj₁ (inj₂ y) ∣ κ ⟩◁} {⟨ _ ∣ inj₁ (inj₂ y) ∣ κ ⟩◁} ↦⃖₁ ↦⃖₁ | refl , refl | refl , refl = refl
deterministic {［ assocr₊  ∣ _ ∣ κ ］◁} {⟨ _ ∣ inj₂ z        ∣ κ ⟩◁} {⟨ _ ∣ inj₁ (inj₁ x) ∣ κ ⟩◁} ↦⃖₁ (() ) | refl , refl | refl , refl
deterministic {［ assocr₊  ∣ _ ∣ κ ］◁} {⟨ _ ∣ inj₂ z        ∣ κ ⟩◁} {⟨ _ ∣ inj₁ (inj₂ y) ∣ κ ⟩◁} ↦⃖₁ (() ) | refl , refl | refl , refl
deterministic {［ assocr₊  ∣ _ ∣ κ ］◁} {⟨ _ ∣ inj₂ z        ∣ κ ⟩◁} {⟨ _ ∣ inj₂ z        ∣ κ ⟩◁} ↦⃖₁ ↦⃖₁ | refl , refl | refl , refl = refl
deterministic {［ unite⋆l  ∣ _ ∣ κ ］◁} {⟨ _ ∣ (tt , v)      ∣ κ ⟩◁} {⟨ _ ∣ (tt , v)      ∣ κ ⟩◁} ↦⃖₁ ↦⃖₁ | refl , refl | refl , refl = refl
deterministic {［ uniti⋆l  ∣ _ ∣ κ ］◁} {⟨ _ ∣ v             ∣ κ ⟩◁} {⟨ _ ∣ v             ∣ κ ⟩◁} ↦⃖₁ ↦⃖₁ | refl , refl | refl , refl = refl
deterministic {［ swap⋆    ∣ _ ∣ κ ］◁} {⟨ _ ∣ (x , y)       ∣ κ ⟩◁} {⟨ _ ∣ (x , y)       ∣ κ ⟩◁} ↦⃖₁ ↦⃖₁ | refl , refl | refl , refl = refl
deterministic {［ assocl⋆  ∣ _ ∣ κ ］◁} {⟨ _ ∣ (x , (y , z)) ∣ κ ⟩◁} {⟨ _ ∣ (x , (y , z)) ∣ κ ⟩◁} ↦⃖₁ ↦⃖₁ | refl , refl | refl , refl = refl
deterministic {［ assocr⋆  ∣ _ ∣ κ ］◁} {⟨ _ ∣ ((x , y) , z) ∣ κ ⟩◁} {⟨ _ ∣ ((x , y) , z) ∣ κ ⟩◁} ↦⃖₁ ↦⃖₁ | refl , refl | refl , refl = refl
deterministic {［ dist     ∣ _ ∣ κ ］◁} {⟨ _ ∣ (inj₁ x , z)  ∣ κ ⟩◁} {⟨ _ ∣ (inj₁ x , z)  ∣ κ ⟩◁} ↦⃖₁ ↦⃖₁ | refl , refl | refl , refl = refl
deterministic {［ dist     ∣ _ ∣ κ ］◁} {⟨ _ ∣ (inj₂ y , z)  ∣ κ ⟩◁} {⟨ _ ∣ (inj₂ y , z)  ∣ κ ⟩◁} ↦⃖₁ ↦⃖₁ | refl , refl | refl , refl = refl
deterministic {［ factor   ∣ _ ∣ κ ］◁} {⟨ _ ∣ inj₁ (x , z)  ∣ κ ⟩◁} {⟨ _ ∣ inj₁ (x , z)  ∣ κ ⟩◁} ↦⃖₁ ↦⃖₁ | refl , refl | refl , refl = refl
deterministic {［ factor   ∣ _ ∣ κ ］◁} {⟨ _ ∣ inj₂ (y , z)  ∣ κ ⟩◁} {⟨ _ ∣ inj₂ (y , z)  ∣ κ ⟩◁} ↦⃖₁ ↦⃖₁ | refl , refl | refl , refl = refl
deterministic {［ unite₊l ∣ _ ∣ _ ］◁} {⟨ _ ∣ _ ∣ _ ⟩◁} {［ _ ∣ _ ∣ _ ］◁} ↦⃖₁ ()
deterministic {［ uniti₊l ∣ _ ∣ _ ］◁} {⟨ _ ∣ _ ∣ _ ⟩◁} {［ _ ∣ _ ∣ _ ］◁} ↦⃖₁ ()
deterministic {［ swap₊   ∣ _ ∣ _ ］◁} {⟨ _ ∣ _ ∣ _ ⟩◁} {［ _ ∣ _ ∣ _ ］◁} ↦⃖₁ ()
deterministic {［ assocl₊ ∣ _ ∣ _ ］◁} {⟨ _ ∣ _ ∣ _ ⟩◁} {［ _ ∣ _ ∣ _ ］◁} ↦⃖₁ ()
deterministic {［ assocr₊ ∣ _ ∣ _ ］◁} {⟨ _ ∣ _ ∣ _ ⟩◁} {［ _ ∣ _ ∣ _ ］◁} ↦⃖₁ ()
deterministic {［ unite⋆l ∣ _ ∣ _ ］◁} {⟨ _ ∣ _ ∣ _ ⟩◁} {［ _ ∣ _ ∣ _ ］◁} ↦⃖₁ ()
deterministic {［ uniti⋆l ∣ _ ∣ _ ］◁} {⟨ _ ∣ _ ∣ _ ⟩◁} {［ _ ∣ _ ∣ _ ］◁} ↦⃖₁ ()
deterministic {［ swap⋆   ∣ _ ∣ _ ］◁} {⟨ _ ∣ _ ∣ _ ⟩◁} {［ _ ∣ _ ∣ _ ］◁} ↦⃖₁ ()
deterministic {［ assocl⋆ ∣ _ ∣ _ ］◁} {⟨ _ ∣ _ ∣ _ ⟩◁} {［ _ ∣ _ ∣ _ ］◁} ↦⃖₁ ()
deterministic {［ assocr⋆ ∣ _ ∣ _ ］◁} {⟨ _ ∣ _ ∣ _ ⟩◁} {［ _ ∣ _ ∣ _ ］◁} ↦⃖₁ ()
deterministic {［ dist    ∣ _ ∣ _ ］◁} {⟨ _ ∣ _ ∣ _ ⟩◁} {［ _ ∣ _ ∣ _ ］◁} ↦⃖₁ ()
deterministic {［ factor  ∣ _ ∣ _ ］◁} {⟨ _ ∣ _ ∣ _ ⟩◁} {［ _ ∣ _ ∣ _ ］◁} ↦⃖₁ ()
deterministic {［ id↔     ∣ _ ∣ _ ］◁} {⟨ _ ∣ _ ∣ _ ⟩◁} {［ _ ∣ _ ∣ _ ］◁} (↦⃖₁ {b = ()})
deterministic {［ _ ⨾ _   ∣ _ ∣ _ ］◁} {⟨ _ ∣ _ ∣ _ ⟩◁} {［ _ ∣ _ ∣ _ ］◁} (↦⃖₁ {b = ()})
deterministic {［ _ ⊕ _   ∣ _ ∣ _ ］◁} {⟨ _ ∣ _ ∣ _ ⟩◁} {［ _ ∣ _ ∣ _ ］◁} (↦⃖₁ {b = ()})
deterministic {［ _ ⊗ _   ∣ _ ∣ _ ］◁} {⟨ _ ∣ _ ∣ _ ⟩◁} {［ _ ∣ _ ∣ _ ］◁} (↦⃖₁ {b = ()})
deterministic {［ η₊      ∣ _ ∣ _ ］◁} {⟨ _ ∣ _ ∣ _ ⟩◁} {［ _ ∣ _ ∣ _ ］◁} (↦⃖₁ {b = ()})
deterministic {［ ε₊      ∣ _ ∣ _ ］◁} {⟨ _ ∣ _ ∣ _ ⟩◁} {［ _ ∣ _ ∣ _ ］◁} (↦⃖₁ {b = ()})
deterministic ↦⃖₂ ↦⃖₂ = refl
deterministic ↦⃖₃ ↦⃖₃ = refl
deterministic ↦⃖₄ ↦⃖₄ = refl
deterministic ↦⃖₅ ↦⃖₅ = refl
deterministic ↦⃖₆ ↦⃖₆ = refl
deterministic ↦⃖₇ ↦⃖₇ = refl
deterministic ↦⃖₈ ↦⃖₈ = refl
deterministic ↦⃖₉ ↦⃖₉ = refl
deterministic ↦⃖₁₀ ↦⃖₁₀ = refl
deterministic {［ c₁ ⊕ c₂ ∣ inj₁ v ∣ κ ］◁} {［ c₁ ∣ v ∣ ☐⊕ c₂ • κ ］◁} {⟨ _ ∣ x ∣ _ ⟩◁} ↦⃖₁₁ r with Lemma₁ r
... | refl , refl with Lemma₂ r
... | refl , refl with Lemma₃ r
... | inj₂ refl with Lemma₄ r
... | inj₁ ()
... | inj₂ ()
deterministic {［ c₁ ⊕ c₂ ∣ _ ∣ _ ］◁} {［ _ ∣ _ ∣ _ ］◁} {［ _ ∣ _ ∣ _ ］◁} ↦⃖₁₁ ↦⃖₁₁ = refl
deterministic {［ c₁ ⊕ c₂ ∣ inj₂ v ∣ _ ］◁} {［ _ ∣ _ ∣ _ ］◁} {⟨ _ ∣ x ∣ _ ⟩◁} ↦⃖₁₂ r with Lemma₁ r
... | refl , refl with Lemma₂ r
... | refl , refl with Lemma₃ r
... | inj₂ refl with Lemma₄ r
... | inj₁ ()
... | inj₂ ()
deterministic {［ c₁ ⊕ c₂ ∣ _ ∣ _ ］◁} {［ _ ∣ _ ∣ _ ］◁} {［ _ ∣ _ ∣ _ ］◁} ↦⃖₁₂ ↦⃖₁₂ = refl
deterministic {［ η₊ ∣ inj₁ v ∣ _ ］◁} {［ η₊ ∣ _ ∣ _ ］▷} {［ _ ∣ _ ∣ _ ］▷} ↦η₁ ↦η₁ = refl
deterministic {［ η₊ ∣ inj₁ v ∣ _ ］◁} {［ η₊ ∣ _ ∣ _ ］▷} {⟨ η₊ ∣ v' ∣ _ ⟩◁} ↦η₁ r with Lemma₁ r
... | refl , refl with Lemma₂ r
... | refl , refl with v'
... | ()
deterministic {［ η₊ ∣ inj₂ (- v) ∣ _ ］◁} {［ η₊ ∣ _ ∣ _ ］▷} {［ _ ∣ _ ∣ _ ］▷} ↦η₂ ↦η₂ = refl
deterministic {［ η₊ ∣ inj₂ (- v) ∣ _ ］◁} {［ η₊ ∣ _ ∣ _ ］▷} {⟨ η₊ ∣ v' ∣ _ ⟩◁} ↦η₂ r with Lemma₁ r
... | refl , refl with Lemma₂ r
... | refl , refl with v'
... | ()
deterministic ↦ε₁ ↦ε₁ = refl
deterministic ↦ε₂ ↦ε₂ = refl

-- Backward deterministic
deterministicᵣₑᵥ : ∀ {st st₁ st₂} → st₁ ↦ st → st₂ ↦ st → st₁ ≡ st₂
deterministicᵣₑᵥ {［ c ∣ _ ∣ κ ］▷} {⟨ c ∣ v ∣ κ ⟩▷} {⟨ c' ∣ v' ∣ κ' ⟩▷} ↦⃗₁ r with Lemma₈ r
... | refl , refl with Lemma₉ r
deterministicᵣₑᵥ {［ unite₊l  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₂ y        ∣ κ ⟩▷} {⟨ _ ∣ inj₂ y        ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ uniti₊l  ∣ _ ∣ κ ］▷} {⟨ _ ∣ v             ∣ κ ⟩▷} {⟨ _ ∣ v             ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ swap₊    ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₁ x        ∣ κ ⟩▷} {⟨ _ ∣ inj₁ x        ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ swap₊    ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₂ y        ∣ κ ⟩▷} {⟨ _ ∣ inj₂ y        ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₁ x        ∣ κ ⟩▷} {⟨ _ ∣ inj₁ x        ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₁ x        ∣ κ ⟩▷} {⟨ _ ∣ inj₂ (inj₁ y) ∣ κ ⟩▷} ↦⃗₁ () | refl , refl | refl , refl
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₁ x        ∣ κ ⟩▷} {⟨ _ ∣ inj₂ (inj₂ z) ∣ κ ⟩▷} ↦⃗₁ () | refl , refl | refl , refl
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₂ (inj₁ y) ∣ κ ⟩▷} {⟨ _ ∣ inj₂ (inj₁ y) ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₂ (inj₂ z) ∣ κ ⟩▷} {⟨ _ ∣ inj₂ (inj₂ z) ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₁ (inj₁ x) ∣ κ ⟩▷} {⟨ _ ∣ inj₁ (inj₁ x) ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₁ (inj₂ y) ∣ κ ⟩▷} {⟨ _ ∣ inj₁ (inj₂ y) ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₂ z        ∣ κ ⟩▷} {⟨ _ ∣ inj₁ (inj₁ x) ∣ κ ⟩▷} ↦⃗₁ () | refl , refl | refl , refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₂ z        ∣ κ ⟩▷} {⟨ _ ∣ inj₁ (inj₂ y) ∣ κ ⟩▷} ↦⃗₁ () | refl , refl | refl , refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₂ z        ∣ κ ⟩▷} {⟨ _ ∣ inj₂ z        ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ unite⋆l  ∣ _ ∣ κ ］▷} {⟨ _ ∣ (tt , v)      ∣ κ ⟩▷} {⟨ _ ∣ (tt , v)      ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ uniti⋆l  ∣ _ ∣ κ ］▷} {⟨ _ ∣ v             ∣ κ ⟩▷} {⟨ _ ∣ v             ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ swap⋆    ∣ _ ∣ κ ］▷} {⟨ _ ∣ (x , y)       ∣ κ ⟩▷} {⟨ _ ∣ (x , y)       ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocl⋆  ∣ _ ∣ κ ］▷} {⟨ _ ∣ (x , (y , z)) ∣ κ ⟩▷} {⟨ _ ∣ (x , (y , z)) ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocr⋆  ∣ _ ∣ κ ］▷} {⟨ _ ∣ ((x , y) , z) ∣ κ ⟩▷} {⟨ _ ∣ ((x , y) , z) ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ dist     ∣ _ ∣ κ ］▷} {⟨ _ ∣ (inj₁ x , z)  ∣ κ ⟩▷} {⟨ _ ∣ (inj₁ x , z)  ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ dist     ∣ _ ∣ κ ］▷} {⟨ _ ∣ (inj₂ y , z)  ∣ κ ⟩▷} {⟨ _ ∣ (inj₂ y , z)  ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ factor   ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₁ (x , z)  ∣ κ ⟩▷} {⟨ _ ∣ inj₁ (x , z)  ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ factor   ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₂ (y , z)  ∣ κ ⟩▷} {⟨ _ ∣ inj₂ (y , z)  ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ unite₊l  ∣ _ ∣ κ ］▷} {⟨ _ ∣ v  ∣ κ ⟩▷} {［ c' ∣ v' ∣ κ' ］▷} ↦⃗₁ ()
deterministicᵣₑᵥ {［ uniti₊l  ∣ _ ∣ κ ］▷} {⟨ _ ∣ v  ∣ κ ⟩▷} {［ c' ∣ v' ∣ κ' ］▷} ↦⃗₁ ()
deterministicᵣₑᵥ {［ swap₊    ∣ _ ∣ κ ］▷} {⟨ _ ∣ v  ∣ κ ⟩▷} {［ c' ∣ v' ∣ κ' ］▷} ↦⃗₁ ()
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ v  ∣ κ ⟩▷} {［ c' ∣ v' ∣ κ' ］▷} ↦⃗₁ ()
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ v  ∣ κ ⟩▷} {［ c' ∣ v' ∣ κ' ］▷} ↦⃗₁ ()
deterministicᵣₑᵥ {［ unite⋆l  ∣ _ ∣ κ ］▷} {⟨ _ ∣ v  ∣ κ ⟩▷} {［ c' ∣ v' ∣ κ' ］▷} ↦⃗₁ ()
deterministicᵣₑᵥ {［ uniti⋆l  ∣ _ ∣ κ ］▷} {⟨ _ ∣ v  ∣ κ ⟩▷} {［ c' ∣ v' ∣ κ' ］▷} ↦⃗₁ ()
deterministicᵣₑᵥ {［ swap⋆    ∣ _ ∣ κ ］▷} {⟨ _ ∣ v  ∣ κ ⟩▷} {［ c' ∣ v' ∣ κ' ］▷} ↦⃗₁ ()
deterministicᵣₑᵥ {［ assocl⋆  ∣ _ ∣ κ ］▷} {⟨ _ ∣ v  ∣ κ ⟩▷} {［ c' ∣ v' ∣ κ' ］▷} ↦⃗₁ ()
deterministicᵣₑᵥ {［ assocr⋆  ∣ _ ∣ κ ］▷} {⟨ _ ∣ v  ∣ κ ⟩▷} {［ c' ∣ v' ∣ κ' ］▷} ↦⃗₁ ()
deterministicᵣₑᵥ {［ dist     ∣ _ ∣ κ ］▷} {⟨ _ ∣ v  ∣ κ ⟩▷} {［ c' ∣ v' ∣ κ' ］▷} ↦⃗₁ ()
deterministicᵣₑᵥ {［ factor   ∣ _ ∣ κ ］▷} {⟨ _ ∣ v  ∣ κ ⟩▷} {［ c' ∣ v' ∣ κ' ］▷} ↦⃗₁ ()
deterministicᵣₑᵥ {［ id↔      ∣ _ ∣ κ ］▷} {⟨ _ ∣ v  ∣ κ ⟩▷} {［ c' ∣ v' ∣ κ' ］▷} (↦⃗₁ {b = ()})
deterministicᵣₑᵥ {［ c₁ ⨾ c₂  ∣ _ ∣ κ ］▷} {⟨ _ ∣ v  ∣ κ ⟩▷} {［ c' ∣ v' ∣ κ' ］▷} (↦⃗₁ {b = ()})
deterministicᵣₑᵥ {［ c₁ ⊕ c₂  ∣ _ ∣ κ ］▷} {⟨ _ ∣ v  ∣ κ ⟩▷} {［ c' ∣ v' ∣ κ' ］▷} (↦⃗₁ {b = ()})
deterministicᵣₑᵥ {［ c₁ ⊗ c₂  ∣ _ ∣ κ ］▷} {⟨ _ ∣ v  ∣ κ ⟩▷} {［ c' ∣ v' ∣ κ' ］▷} (↦⃗₁ {b = ()})
deterministicᵣₑᵥ {［ c ∣ _ ∣ κ ］▷} {⟨ c ∣ v ∣ κ ⟩▷} {［ _ ∣ _ ∣ _ ］◁} ↦⃗₁ r with Lemma₅ r
... | refl , refl with Lemma₆ r
... | refl , refl with Lemma₇ r
... | refl with v
... | ()
deterministicᵣₑᵥ ↦⃗₂ ↦⃗₂ = refl
deterministicᵣₑᵥ ↦⃗₃ ↦⃗₃ = refl
deterministicᵣₑᵥ ↦⃗₄ ↦⃗₄ = refl
deterministicᵣₑᵥ ↦⃗₅ ↦⃗₅ = refl
deterministicᵣₑᵥ ↦⃗₆ ↦⃗₆ = refl
deterministicᵣₑᵥ ↦⃗₇ ↦⃗₇ = refl
deterministicᵣₑᵥ ↦⃗₈ ↦⃗₈ = refl
deterministicᵣₑᵥ ↦⃗₉ ↦⃗₉ = refl
deterministicᵣₑᵥ ↦⃗₁₀ ↦⃗₁₀ = refl
deterministicᵣₑᵥ {［ c₁ ⊕ c₂ ∣ inj₁ v ∣ κ ］▷} {_} {⟨ _ ∣ _ ∣ _ ⟩▷} ↦⃗₁₁ r with Lemma₈ r
... | refl , refl with Lemma₉ r
... | refl , refl with Lemma₁₀ r
... | inj₂ refl with Lemma₁₁ r
... | inj₁ ()
... | inj₂ ()
deterministicᵣₑᵥ {［ c₁ ⊕ c₂ ∣ inj₁ v ∣ κ ］▷} {_} {［ _ ∣ _ ∣ _ ］▷} ↦⃗₁₁ ↦⃗₁₁ = refl
deterministicᵣₑᵥ {［ c₁ ⊕ c₂ ∣ inj₂ v ∣ κ ］▷} {_} {⟨ _ ∣ _ ∣ _ ⟩▷} ↦⃗₁₂ r with Lemma₈ r
... | refl , refl with Lemma₉ r
... | refl , refl with Lemma₁₀ r
... | inj₂ refl with Lemma₁₁ r
... | inj₁ ()
... | inj₂ ()
deterministicᵣₑᵥ {［ c₁ ⊕ c₂ ∣ inj₂ v ∣ κ ］▷} {_} {［ _ ∣ _ ∣ _ ］▷} ↦⃗₁₂ ↦⃗₁₂ = refl
deterministicᵣₑᵥ (↦⃖₁ {b = b₁}) (↦⃖₁ {b = b₂})  with base-is-prop _ b₁ b₂
... | refl = refl
deterministicᵣₑᵥ ↦⃖₂ ↦⃖₂ = refl
deterministicᵣₑᵥ ↦⃖₃ ↦⃖₃ = refl
deterministicᵣₑᵥ ↦⃖₄ ↦⃖₄ = refl
deterministicᵣₑᵥ ↦⃖₅ ↦⃖₅ = refl
deterministicᵣₑᵥ ↦⃖₆ ↦⃖₆ = refl
deterministicᵣₑᵥ ↦⃖₇ ↦⃖₇ = refl
deterministicᵣₑᵥ ↦⃖₈ ↦⃖₈ = refl
deterministicᵣₑᵥ ↦⃖₉ ↦⃖₉ = refl
deterministicᵣₑᵥ ↦⃖₁₀ ↦⃖₁₀ = refl
deterministicᵣₑᵥ ↦⃖₁₁ ↦⃖₁₁ = refl
deterministicᵣₑᵥ ↦⃖₁₂ ↦⃖₁₂ = refl
deterministicᵣₑᵥ {_} {［ η₊ ∣ inj₁ _ ∣ _ ］◁} {⟨ _ ∣ v ∣ _ ⟩▷} ↦η₁ r with Lemma₈ r
... | refl , refl with Lemma₉ r
... | refl , refl with Lemma₁₀ r
... | inj₁ ()
... | inj₂ ()
deterministicᵣₑᵥ {_} {［ η₊ ∣ inj₁ v ∣ _ ］◁} {［ _ ∣ _ ∣ _ ］◁} ↦η₁ ↦η₁ = refl
deterministicᵣₑᵥ {_} {［ η₊ ∣ inj₂ (- v) ∣ _ ］◁} {⟨ c ∣ x ∣ x₁ ⟩▷} ↦η₂ r with Lemma₈ r
... | refl , refl with Lemma₉ r
... | refl , refl with Lemma₁₀ r
... | inj₁ ()
... | inj₂ ()
deterministicᵣₑᵥ {_} {［ η₊ ∣ inj₂ (- v) ∣ _ ］◁} {［ _ ∣ _ ∣ _ ］◁} ↦η₂ ↦η₂ = refl
deterministicᵣₑᵥ ↦ε₁ ↦ε₁ = refl
deterministicᵣₑᵥ ↦ε₂ ↦ε₂ = refl

-- Non-repeating Lemma
open RevNoRepeat (record { State = State
                         ; _↦_ = _↦_
                         ; deterministic = deterministic
                         ; deterministicᵣₑᵥ = deterministicᵣₑᵥ }) public

NoRepeatPi- : ∀ {A B stₙ stₘ n m} (c : A ↔ B) (v : ⟦ A ⟧)
            → n < m
            → ⟨ c ∣ v ∣ ☐ ⟩▷ ↦[ n ] stₙ
            → ⟨ c ∣ v ∣ ☐ ⟩▷ ↦[ m ] stₘ
            → stₙ ≢ stₘ
NoRepeatPi- c v n<m st₀↦stₙ st₀↦stₘ = NoRepeat (λ ()) n<m st₀↦stₙ st₀↦stₘ

