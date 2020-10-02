module PiQ.NoRepeat where
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
open import PiQ.AuxLemmas
import PartialRevNoRepeat

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
deterministic {_} {_} {⊠} (↦⃖₁ {b = b}) r with Lemma₈ r
... | nbase = ⊥-elim (nbase b)
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
... | inj₂ (inj₂ refl) with Lemma₄ r
... | inj₁ ()
... | inj₂ ()
deterministic {［ c₁ ⊕ c₂ ∣ _ ∣ _ ］◁} {［ _ ∣ _ ∣ _ ］◁} {［ _ ∣ _ ∣ _ ］◁} ↦⃖₁₁ ↦⃖₁₁ = refl
deterministic {［ c₁ ⊕ c₂ ∣ inj₂ v ∣ _ ］◁} {［ _ ∣ _ ∣ _ ］◁} {⟨ _ ∣ x ∣ _ ⟩◁} ↦⃖₁₂ r with Lemma₁ r
... | refl , refl with Lemma₂ r
... | refl , refl with Lemma₃ r
... | inj₂ (inj₂ refl) with Lemma₄ r
... | inj₁ ()
... | inj₂ ()
deterministic {［ c₁ ⊕ c₂ ∣ _ ∣ _ ］◁} {［ _ ∣ _ ∣ _ ］◁} {［ _ ∣ _ ∣ _ ］◁} ↦⃖₁₂ ↦⃖₁₂ = refl
deterministic {［ η₊ ∣ inj₁ _ ∣ _ ］◁} {［ _ ∣ _ ∣ _ ］▷} {［ _ ∣ _ ∣ _ ］▷} ↦η₊₁ ↦η₊₁ = refl
deterministic {［ η₊ ∣ inj₁ _ ∣ _ ］◁} {［ _ ∣ _ ∣ _ ］▷} {⟨ η₊ ∣ v' ∣ _ ⟩◁} ↦η₊₁ r with Lemma₁ r
... | refl , refl with Lemma₂ r
... | refl , refl with v'
... | ()
deterministic {［ η₊ ∣ inj₂ (- _) ∣ _ ］◁} {［ η₊ ∣ inj₁ _ ∣ _ ］▷} {［ _ ∣ _ ∣ _ ］▷} ↦η₊₂ ↦η₊₂ = refl
deterministic {［ η₊ ∣ inj₂ (- _) ∣ _ ］◁} {［ η₊ ∣ inj₁ _ ∣ _ ］▷} {⟨ η₊ ∣ v' ∣ _ ⟩◁} ↦η₊₂ r with Lemma₁ r
... | refl , refl with Lemma₂ r
... | refl , refl with v'
... | ()
deterministic ↦ε₊₁ ↦ε₊₁ = refl
deterministic ↦ε₊₂ ↦ε₊₂ = refl
deterministic {⟨ ηₓ _ ∣ _ ∣ _ ⟩▷} {［ _ ∣ _ ∣ _ ］▷} {［ _ ∣ _ ∣ _ ］▷} ↦⃗ηₓ ↦⃗ηₓ = refl
deterministic {［ ηₓ _ ∣ _ ∣ _ ］◁} {⟨ _ ∣ _ ∣ _ ⟩◁} {⟨ _ ∣ v ∣ _ ⟩◁} ↦⃖ηₓ₁ r with Lemma₁ r
... | refl , refl with Lemma₂ r
... | refl , refl with v
... | tt = refl
deterministic {［ ηₓ _ ∣ _ ∣ _ ］◁} {⟨ _ ∣ _ ∣ _ ⟩◁} {⊠} r₁ r₂ with Lemma₁ r₁
... | refl , refl with Lemma₂ r₁
... | refl , refl = ⊥-elim (Lemma₉ r₁ r₂)
deterministic {［ ηₓ _ ∣ _ ∣ _ ］◁} {⊠} {⟨ _ ∣ v ∣ _ ⟩◁} r₁ r₂ with Lemma₁ r₂
... | refl , refl with Lemma₂ r₂
... | refl , refl = ⊥-elim (Lemma₉ r₂ r₁)
deterministic {［ ηₓ _ ∣ _ ∣ _ ］◁} {⊠} {⊠} ↦⃖ηₓ₂ ↦⃖ηₓ₂ = refl
deterministic {⟨ εₓ _ ∣ _ ∣ _ ⟩▷} {［ _ ∣ _ ∣ _ ］▷} {［ _ ∣ _ ∣ _ ］▷} ↦⃗εₓ₁ ↦⃗εₓ₁ = refl
deterministic {⟨ εₓ _ ∣ _ ∣ _ ⟩▷} {［ εₓ _ ∣ tt ∣ _ ］▷} {⊠} (↦⃗εₓ₁ {eq = eq}) (↦⃗εₓ₂ {neq = neq}) = ⊥-elim (neq eq)
deterministic {⟨ εₓ _ ∣ _ ∣ _ ⟩▷} {⊠} {［ εₓ _ ∣ tt ∣ _ ］▷} (↦⃗εₓ₂ {neq = neq}) (↦⃗εₓ₁ {eq = eq}) = ⊥-elim (neq eq)
deterministic {⟨ εₓ _ ∣ _ ∣ _ ⟩▷} {⊠} {⊠} ↦⃗εₓ₂ ↦⃗εₓ₂ = refl
deterministic {［ εₓ _ ∣ _ ∣ _ ］◁} {⟨ _ ∣ _ ∣ _ ⟩◁} {⟨ _ ∣ _ ∣ _ ⟩◁} ↦⃖εₓ ↦⃖εₓ = refl

-- Backward deterministic
deterministicᵣₑᵥ : ∀ {st st₁ st₂} → st₁ ↦ st → st₂ ↦ st → st ≢ ⊠ → st₁ ≡ st₂
deterministicᵣₑᵥ {_} {_} {⟨ _ ∣ _ ∣ _ ⟩▷} ↦⃗₁ r nf with Lemma₁₀ r
... | refl , refl with Lemma₁₁ r
deterministicᵣₑᵥ {［ unite₊l  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₂ y        ∣ κ ⟩▷} {⟨ _ ∣ inj₂ y        ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ uniti₊l  ∣ _ ∣ κ ］▷} {⟨ _ ∣ v             ∣ κ ⟩▷} {⟨ _ ∣ v             ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ swap₊    ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₁ x        ∣ κ ⟩▷} {⟨ _ ∣ inj₁ x        ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ swap₊    ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₂ y        ∣ κ ⟩▷} {⟨ _ ∣ inj₂ y        ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₁ x        ∣ κ ⟩▷} {⟨ _ ∣ inj₁ x        ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₁ x        ∣ κ ⟩▷} {⟨ _ ∣ inj₂ (inj₁ y) ∣ κ ⟩▷} ↦⃗₁ () _ | refl , refl | refl , refl
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₁ x        ∣ κ ⟩▷} {⟨ _ ∣ inj₂ (inj₂ z) ∣ κ ⟩▷} ↦⃗₁ () _ | refl , refl | refl , refl
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₂ (inj₁ y) ∣ κ ⟩▷} {⟨ _ ∣ inj₂ (inj₁ y) ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₂ (inj₂ z) ∣ κ ⟩▷} {⟨ _ ∣ inj₂ (inj₂ z) ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₂ (inj₂ z) ∣ κ ⟩▷} {⟨ _ ∣ inj₁ x        ∣ κ ⟩▷} ↦⃗₁ () _ | refl , refl | refl , refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₁ (inj₁ x) ∣ κ ⟩▷} {⟨ _ ∣ inj₁ (inj₁ x) ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₁ (inj₂ y) ∣ κ ⟩▷} {⟨ _ ∣ inj₁ (inj₂ y) ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₁ (inj₁ x) ∣ κ ⟩▷} {⟨ _ ∣ inj₂ z        ∣ κ ⟩▷} ↦⃗₁ () _ | refl , refl | refl , refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₁ (inj₂ y) ∣ κ ⟩▷} {⟨ _ ∣ inj₂ z        ∣ κ ⟩▷} ↦⃗₁ () _ | refl , refl | refl , refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₂ z        ∣ κ ⟩▷} {⟨ _ ∣ inj₁ (inj₁ x) ∣ κ ⟩▷} ↦⃗₁ () _ | refl , refl | refl , refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₂ z        ∣ κ ⟩▷} {⟨ _ ∣ inj₁ (inj₂ y) ∣ κ ⟩▷} ↦⃗₁ () _ | refl , refl | refl , refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₂ z        ∣ κ ⟩▷} {⟨ _ ∣ inj₂ z        ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ unite⋆l  ∣ _ ∣ κ ］▷} {⟨ _ ∣ (tt , v)      ∣ κ ⟩▷} {⟨ _ ∣ (tt , v)      ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ uniti⋆l  ∣ _ ∣ κ ］▷} {⟨ _ ∣ v             ∣ κ ⟩▷} {⟨ _ ∣ v             ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ swap⋆    ∣ _ ∣ κ ］▷} {⟨ _ ∣ (x , y)       ∣ κ ⟩▷} {⟨ _ ∣ (x , y)       ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocl⋆  ∣ _ ∣ κ ］▷} {⟨ _ ∣ (x , (y , z)) ∣ κ ⟩▷} {⟨ _ ∣ (x , (y , z)) ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocr⋆  ∣ _ ∣ κ ］▷} {⟨ _ ∣ ((x , y) , z) ∣ κ ⟩▷} {⟨ _ ∣ ((x , y) , z) ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ dist     ∣ _ ∣ κ ］▷} {⟨ _ ∣ (inj₁ x , z)  ∣ κ ⟩▷} {⟨ _ ∣ (inj₁ x , z)  ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ dist     ∣ _ ∣ κ ］▷} {⟨ _ ∣ (inj₂ y , z)  ∣ κ ⟩▷} {⟨ _ ∣ (inj₂ y , z)  ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ factor   ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₁ (x , z)  ∣ κ ⟩▷} {⟨ _ ∣ inj₁ (x , z)  ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ factor   ∣ _ ∣ κ ］▷} {⟨ _ ∣ inj₂ (y , z)  ∣ κ ⟩▷} {⟨ _ ∣ inj₂ (y , z)  ∣ κ ⟩▷} ↦⃗₁ ↦⃗₁ _ | refl , refl | refl , refl = refl
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
deterministicᵣₑᵥ {_} {⟨ _ ∣ v ∣ _ ⟩▷} {［ _ ∣ _ ∣ _ ］◁} ↦⃗₁ r nf with Lemma₅ r
... | refl , refl with Lemma₆ r
... | refl , refl with Lemma₇ r
... | refl with v
... | ()
deterministicᵣₑᵥ ↦⃗₂ ↦⃗₂ nf = refl
deterministicᵣₑᵥ ↦⃗₃ ↦⃗₃ nf = refl
deterministicᵣₑᵥ ↦⃗₄ ↦⃗₄ nf = refl
deterministicᵣₑᵥ ↦⃗₅ ↦⃗₅ nf = refl
deterministicᵣₑᵥ ↦⃗₆ ↦⃗₆ nf = refl
deterministicᵣₑᵥ ↦⃗₇ ↦⃗₇ nf = refl
deterministicᵣₑᵥ ↦⃗₈ ↦⃗₈ nf = refl
deterministicᵣₑᵥ ↦⃗₉ ↦⃗₉ nf = refl
deterministicᵣₑᵥ ↦⃗₁₀ ↦⃗₁₀ nf = refl
deterministicᵣₑᵥ {_} {_} {⟨ c ∣ x ∣ x₁ ⟩▷} ↦⃗₁₁ r nf with Lemma₁₀ r
... | refl , refl with Lemma₁₁ r
... | refl , refl with Lemma₁₂ r
... | inj₂ (inj₂ refl) with Lemma₁₃ r
... | inj₁ ()
... | inj₂ ()
deterministicᵣₑᵥ {_} {_} {［ _ ∣ _ ∣ _ ］▷} ↦⃗₁₁ ↦⃗₁₁ nf = refl
deterministicᵣₑᵥ {_} {_} {⟨ _ ∣ _ ∣ _ ⟩▷} ↦⃗₁₂ r nf with Lemma₁₀ r
... | refl , refl with Lemma₁₁ r
... | refl , refl with Lemma₁₂ r
... | inj₂ (inj₂ refl) with Lemma₁₃ r
... | inj₁ ()
... | inj₂ ()
deterministicᵣₑᵥ {_} {_} {［ _ ∣ _ ∣ _ ］▷} ↦⃗₁₂ ↦⃗₁₂ nf = refl
deterministicᵣₑᵥ (↦⃖₁ {b = b₁}) (↦⃖₁ {b = b₂}) nf with base-is-prop _ b₁ b₂
... | refl = refl
deterministicᵣₑᵥ ↦⃖₂ ↦⃖₂ nf = refl
deterministicᵣₑᵥ ↦⃖₃ ↦⃖₃ nf = refl
deterministicᵣₑᵥ ↦⃖₄ ↦⃖₄ nf = refl
deterministicᵣₑᵥ ↦⃖₅ ↦⃖₅ nf = refl
deterministicᵣₑᵥ ↦⃖₆ ↦⃖₆ nf = refl
deterministicᵣₑᵥ ↦⃖₇ ↦⃖₇ nf = refl
deterministicᵣₑᵥ ↦⃖₈ ↦⃖₈ nf = refl
deterministicᵣₑᵥ ↦⃖₉ ↦⃖₉ nf = refl
deterministicᵣₑᵥ ↦⃖₁₀ ↦⃖₁₀ nf = refl
deterministicᵣₑᵥ ↦⃖₁₁ ↦⃖₁₁ nf = refl
deterministicᵣₑᵥ ↦⃖₁₂ ↦⃖₁₂ nf = refl
deterministicᵣₑᵥ {_} {_} {⟨ _ ∣ v ∣ _ ⟩▷} ↦η₊₁ r nf with Lemma₁₀ r
... | refl , refl with Lemma₁₁ r
... | refl , refl with v
... | ()
deterministicᵣₑᵥ {_} {_} {［ _ ∣ _ ∣ _ ］◁} ↦η₊₁ ↦η₊₁ nf = refl
deterministicᵣₑᵥ {_} {_} {⟨ _ ∣ v ∣ _ ⟩▷} ↦η₊₂ r nf with Lemma₁₀ r
... | refl , refl with Lemma₁₁ r
... | refl , refl with v
... | ()
deterministicᵣₑᵥ {_} {_} {［ _ ∣ _ ∣ _ ］◁} ↦η₊₂ ↦η₊₂ nf = refl
deterministicᵣₑᵥ ↦ε₊₁ ↦ε₊₁ nf = refl
deterministicᵣₑᵥ ↦ε₊₂ ↦ε₊₂ nf = refl
deterministicᵣₑᵥ {_} {_} {⟨ _ ∣ v ∣ _ ⟩▷} ↦⃗ηₓ r nf with Lemma₁₀ r
... | refl , refl with Lemma₁₁ r
... | refl , refl with v
... | tt = refl
deterministicᵣₑᵥ (↦⃖ηₓ₁ {eq = refl}) (↦⃖ηₓ₁ {eq = refl}) nf = refl
deterministicᵣₑᵥ ↦⃖ηₓ₂ ↦⃖ηₓ₂ nf = ⊥-elim (nf refl)
deterministicᵣₑᵥ ↦⃖ηₓ₂ ↦⃗εₓ₂ nf = ⊥-elim (nf refl)
deterministicᵣₑᵥ (↦⃗εₓ₁ {eq = refl}) (↦⃗εₓ₁ {eq = refl}) nf = refl
deterministicᵣₑᵥ ↦⃗εₓ₂ ↦⃖ηₓ₂ nf = ⊥-elim (nf refl)
deterministicᵣₑᵥ ↦⃗εₓ₂ ↦⃗εₓ₂ nf = ⊥-elim (nf refl)
deterministicᵣₑᵥ ↦⃖εₓ ↦⃖εₓ nf = refl

-- Non-repeating Lemma

⊠-is-stuck : ∀ {st} → st ≡ ⊠ → ∄[ st' ] (st ↦ st')
⊠-is-stuck refl = λ ()

open PartialRevNoRepeat (record { State = State
                                ; _↦_ = _↦_
                                ; is-fail = λ st → st ≡ ⊠
                                ; is-fail? = (λ { ⊠ → yes refl
                                                ; ⟨ _ ∣ _ ∣ _ ⟩▷ → no (λ ())
                                                ; ［ _ ∣ _ ∣ _ ］▷ → no (λ ())
                                                ; ⟨ _ ∣ _ ∣ _ ⟩◁ → no (λ ())
                                                ; ［ _ ∣ _ ∣ _ ］◁ → no (λ ())})
                                ; fail-is-stuck = ⊠-is-stuck
                                ; deterministic = deterministic
                                ; deterministicᵣₑᵥ = deterministicᵣₑᵥ}) public

st-is-initial⇒st≢⊠ : (st : State) → is-initial st → st ≢ ⊠
st-is-initial⇒st≢⊠ ⟨ c ∣ x ∣ x₁ ⟩▷ _ ()
st-is-initial⇒st≢⊠ ［ c ∣ x ∣ x₁ ］▷ _ ()
st-is-initial⇒st≢⊠ ⟨ c ∣ x ∣ x₁ ⟩◁ _ ()
st-is-initial⇒st≢⊠ ［ c ∣ x ∣ x₁ ］◁ _ ()
st-is-initial⇒st≢⊠ ⊠ init _ = init (⟨ εₓ (inj₁ tt) ∣ (inj₂ tt , ↻) ∣ ☐ ⟩▷ , ↦⃗εₓ₂ {𝟙 +ᵤ 𝟙} {inj₁ tt} {_} {_} {λ ()})
