module PiFrac.NoRepeat where
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
open import PiFrac.AuxLemmas
import PartialRevNoRepeat

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
deterministic ↦η ↦η = refl
deterministic ↦ε₁ ↦ε₁ = refl
deterministic (↦ε₁ {eq = eq}) (↦ε₂ {neq = neq}) = ⊥-elim (neq eq)
deterministic (↦ε₂ {neq = neq}) (↦ε₁ {eq = eq}) = ⊥-elim (neq eq)
deterministic ↦ε₂ ↦ε₂ = refl

-- Backward deterministic
deterministicᵣₑᵥ : ∀ {st st₁ st₂} → st₁ ↦ st → st₂ ↦ st → st ≢ ⊠ → st₁ ≡ st₂
deterministicᵣₑᵥ {［ c ∣ _ ∣ κ ］} {⟨ c ∣ v ∣ κ ⟩} {⟨ c' ∣ v' ∣ κ' ⟩} ↦₁ r st≠⊠ with Lemma₁ r
... | refl , refl with Lemma₂ r
deterministicᵣₑᵥ {［ uniti₊l  ∣ _ ∣ κ ］} {⟨ _ ∣ x             ∣ κ ⟩} {⟨ _ ∣ x             ∣ κ ⟩} ↦₁ ↦₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ unite₊l  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₂ x        ∣ κ ⟩} {⟨ _ ∣ inj₂ x        ∣ κ ⟩} ↦₁ ↦₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ swap₊    ∣ _ ∣ κ ］} {⟨ _ ∣ inj₁ x        ∣ κ ⟩} {⟨ _ ∣ inj₁ x        ∣ κ ⟩} ↦₁ ↦₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ swap₊    ∣ _ ∣ κ ］} {⟨ _ ∣ inj₂ y        ∣ κ ⟩} {⟨ _ ∣ inj₂ y        ∣ κ ⟩} ↦₁ ↦₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₁ x        ∣ κ ⟩} {⟨ _ ∣ inj₁ x        ∣ κ ⟩} ↦₁ ↦₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₁ x        ∣ κ ⟩} {⟨ _ ∣ inj₂ (inj₁ y) ∣ κ ⟩} ↦₁ () _ | refl , refl | refl , refl
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₁ x        ∣ κ ⟩} {⟨ _ ∣ inj₂ (inj₂ z) ∣ κ ⟩} ↦₁ () _ | refl , refl | refl , refl
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₂ (inj₁ y) ∣ κ ⟩} {⟨ _ ∣ inj₂ (inj₁ y) ∣ κ ⟩} ↦₁ ↦₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocl₊  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₂ (inj₂ z) ∣ κ ⟩} {⟨ _ ∣ inj₂ (inj₂ z) ∣ κ ⟩} ↦₁ ↦₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₁ (inj₁ x) ∣ κ ⟩} {⟨ _ ∣ inj₁ (inj₁ x) ∣ κ ⟩} ↦₁ ↦₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₁ (inj₂ y) ∣ κ ⟩} {⟨ _ ∣ inj₁ (inj₂ y) ∣ κ ⟩} ↦₁ ↦₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₂ z        ∣ κ ⟩} {⟨ _ ∣ inj₁ (inj₁ x) ∣ κ ⟩} ↦₁ () _ | refl , refl | refl , refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₂ z        ∣ κ ⟩} {⟨ _ ∣ inj₁ (inj₂ y) ∣ κ ⟩} ↦₁ () _ | refl , refl | refl , refl
deterministicᵣₑᵥ {［ assocr₊  ∣ _ ∣ κ ］} {⟨ _ ∣ inj₂ z        ∣ κ ⟩} {⟨ _ ∣ inj₂ z        ∣ κ ⟩} ↦₁ ↦₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ unite⋆l  ∣ _ ∣ κ ］} {⟨ _ ∣ (tt , v)      ∣ κ ⟩} {⟨ _ ∣ (tt , v)      ∣ κ ⟩} ↦₁ ↦₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ uniti⋆l  ∣ _ ∣ κ ］} {⟨ _ ∣ v             ∣ κ ⟩} {⟨ _ ∣ v             ∣ κ ⟩} ↦₁ ↦₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ swap⋆    ∣ _ ∣ κ ］} {⟨ _ ∣ (x , y)       ∣ κ ⟩} {⟨ _ ∣ (x , y)       ∣ κ ⟩} ↦₁ ↦₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocl⋆  ∣ _ ∣ κ ］} {⟨ _ ∣ (x , (y , z)) ∣ κ ⟩} {⟨ _ ∣ (x , (y , z)) ∣ κ ⟩} ↦₁ ↦₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ assocr⋆  ∣ _ ∣ κ ］} {⟨ _ ∣ ((x , y) , z) ∣ κ ⟩} {⟨ _ ∣ ((x , y) , z) ∣ κ ⟩} ↦₁ ↦₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ dist     ∣ _ ∣ κ ］} {⟨ _ ∣ (inj₁ x , z)  ∣ κ ⟩} {⟨ _ ∣ (inj₁ x , z)  ∣ κ ⟩} ↦₁ ↦₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ dist     ∣ _ ∣ κ ］} {⟨ _ ∣ (inj₂ y , z)  ∣ κ ⟩} {⟨ _ ∣ (inj₂ y , z)  ∣ κ ⟩} ↦₁ ↦₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ factor   ∣ _ ∣ κ ］} {⟨ _ ∣ inj₁ (x , z)  ∣ κ ⟩} {⟨ _ ∣ inj₁ (x , z)  ∣ κ ⟩} ↦₁ ↦₁ _ | refl , refl | refl , refl = refl
deterministicᵣₑᵥ {［ factor   ∣ _ ∣ κ ］} {⟨ _ ∣ inj₂ (y , z)  ∣ κ ⟩} {⟨ _ ∣ inj₂ (y , z)  ∣ κ ⟩} ↦₁ ↦₁ _ | refl , refl | refl , refl = refl
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
deterministicᵣₑᵥ {_} {_} {_} ↦₂ ↦₂ st≠⊠ = refl
deterministicᵣₑᵥ {_} {_} {_} ↦₃ ↦₃ st≠⊠ = refl
deterministicᵣₑᵥ {_} {_} {_} ↦₄ ↦₄ st≠⊠ = refl
deterministicᵣₑᵥ {_} {_} {_} ↦₅ ↦₅ st≠⊠ = refl
deterministicᵣₑᵥ {_} {_} {_} ↦₆ ↦₆ st≠⊠ = refl
deterministicᵣₑᵥ {_} {_} {_} ↦₇ ↦₇ st≠⊠ = refl
deterministicᵣₑᵥ {_} {_} {_} ↦₈ ↦₈ st≠⊠ = refl
deterministicᵣₑᵥ {_} {_} {_} ↦₉ ↦₉ st≠⊠ = refl
deterministicᵣₑᵥ {_} {_} {_} ↦₁₀ ↦₁₀ st≠⊠ = refl
deterministicᵣₑᵥ {.(［ _ ⊕ _ ∣ inj₁ _ ∣ _ ］)} {_} {⟨ c ∣ v ∣ κ ⟩} ↦₁₁ r st≠⊠ with Lemma₁ r
... | refl , refl with Lemma₂ r
... | refl , refl with Lemma₃ r
... | inj₂ (inj₂ refl) with Lemma₄ r
... | inj₁ ()
... | inj₂ ()
deterministicᵣₑᵥ {［ _ ⊕ _ ∣ inj₁ _ ∣ _ ］} {_} {_} ↦₁₁ ↦₁₁ st≠⊠ = refl
deterministicᵣₑᵥ {［ _ ⊕ _ ∣ inj₂ _ ∣ _ ］} {［ _ ∣ _ ∣ _ ⊕☐• _ ］} {⟨ c ∣ v ∣ κ ⟩} ↦₁₂ r st≠⊠ with Lemma₁ r
... | refl , refl with Lemma₂ r
... | refl , refl with Lemma₃ r
... | inj₂ (inj₂ refl) with Lemma₄ r
... | inj₁ ()
... | inj₂ ()
deterministicᵣₑᵥ {［ _ ⊕ _ ∣ inj₂ _ ∣ _ ］} {_} {_} ↦₁₂ ↦₁₂ st≠⊠ = refl
deterministicᵣₑᵥ {［ ηₓ v ∣ _ ∣ _ ］} {⟨ ηₓ v ∣ tt ∣ _ ⟩} {⟨ _ ∣ v' ∣ _ ⟩} ↦η r st≠⊠ with Lemma₁ r
... | refl , refl with Lemma₂ r
... | refl , refl with v'
... | tt = refl
deterministicᵣₑᵥ {［ εₓ v ∣ tt ∣ _ ］} {_} {_} (↦ε₁ {eq = refl}) (↦ε₁ {eq = refl}) st≠⊠ = refl
deterministicᵣₑᵥ {⊠} {⟨ εₓ v ∣ _ , ↻ ∣ _ ⟩} {_} ↦ε₂ ↦ε₂ st≠⊠ = ⊥-elim (st≠⊠ refl)

-- Non-repeating Lemma

⊠-is-stuck : ∀ {st} → st ≡ ⊠ → ∄[ st' ] (st ↦ st')
⊠-is-stuck refl = λ ()

open PartialRevNoRepeat (record { State = State
                                ; _↦_ = _↦_
                                ; is-fail = λ st → st ≡ ⊠
                                ; is-fail? = (λ { ⊠ → yes refl
                                                ; ⟨ _ ∣ _ ∣ _ ⟩ → no (λ ())
                                                ; ［ _ ∣ _ ∣ _ ］ → no (λ ())})
                                ; fail-is-stuck = ⊠-is-stuck
                                ; deterministic = deterministic
                                ; deterministicᵣₑᵥ = deterministicᵣₑᵥ}) public
