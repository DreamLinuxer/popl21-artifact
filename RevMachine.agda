module RevMachine where
open import Level
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product

record RevMachine {ℓ} : Set (suc ℓ) where
  field
    State : Set ℓ
    _↦_ : Rel State ℓ
    deterministic : ∀ {st st₁ st₂} → st ↦ st₁ → st ↦ st₂ → st₁ ≡ st₂
    deterministicᵣₑᵥ : ∀ {st st₁ st₂} → st₁ ↦ st → st₂ ↦ st → st₁ ≡ st₂

record PartialRevMachine {ℓ} : Set (suc ℓ) where
  field
    State : Set ℓ
    _↦_ : Rel State ℓ
    is-fail : State → Set ℓ
    is-fail? : (st : State) → Dec (is-fail st)
    fail-is-stuck : ∀ {st} → is-fail st → ∄[ st' ] (st ↦ st')
    deterministic : ∀ {st st₁ st₂} → st ↦ st₁ → st ↦ st₂ → st₁ ≡ st₂
    deterministicᵣₑᵥ : ∀ {st st₁ st₂} → st₁ ↦ st → st₂ ↦ st → ¬ (is-fail st) → st₁ ≡ st₂
    


