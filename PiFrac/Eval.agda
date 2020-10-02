module PiFrac.Eval where
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Sum
open import Data.Product
open import Data.List as L hiding (_∷_)
open import Data.Maybe
open import Relation.Binary.Core
open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_)
open import PiFrac.Syntax
open import PiFrac.Opsem
open import PiFrac.NoRepeat

-- Stuck states must be either of the form ［ c ∣ v ∣ ☐ ］ or ⊠
Stuck : ∀ {st} → is-stuck st
      → (Σ[ A ∈ 𝕌 ] Σ[ B ∈ 𝕌 ] Σ[ c ∈ A ↔ B ] Σ[ v ∈ ⟦ B ⟧ ] st ≡ ［ c ∣ v ∣ ☐ ］) ⊎ st ≡ ⊠
Stuck {⟨ uniti₊l  ∣ v       ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₁))
Stuck {⟨ unite₊l  ∣ v       ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₁))
Stuck {⟨ swap₊    ∣ v       ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₁))
Stuck {⟨ assocl₊  ∣ v       ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₁))
Stuck {⟨ assocr₊  ∣ v       ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₁))
Stuck {⟨ unite⋆l  ∣ v       ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₁))
Stuck {⟨ uniti⋆l  ∣ v       ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₁))
Stuck {⟨ swap⋆    ∣ v       ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₁))
Stuck {⟨ assocl⋆  ∣ v       ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₁))
Stuck {⟨ assocr⋆  ∣ v       ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₁))
Stuck {⟨ dist     ∣ v       ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₁))
Stuck {⟨ factor   ∣ v       ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₁))
Stuck {⟨ id↔      ∣ v       ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₂))
Stuck {⟨ ηₓ v     ∣ tt      ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦η))
Stuck {⟨ εₓ v     ∣ v' , ↻  ∣ κ ⟩} stuck with v ≟ v'
... | yes eq  = ⊥-elim (stuck (_ , ↦ε₁ {eq = eq}))
... | no  neq = ⊥-elim (stuck (_ , ↦ε₂ {neq = neq}))
Stuck {⟨ c₁ ⨾ c₂  ∣ v       ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₃))
Stuck {⟨ c₁ ⊕ c₂  ∣ inj₁ x  ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₄))
Stuck {⟨ c₁ ⊕ c₂  ∣ inj₂ y  ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₅))
Stuck {⟨ c₁ ⊗ c₂  ∣ (x , y) ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₆))
Stuck {［ c ∣ v ∣ ☐               ］} stuck = inj₁ (_ , _ , _ , _ , refl)
Stuck {［ c ∣ v ∣ ☐⨾ c₂ • κ       ］} stuck = ⊥-elim (stuck (_ , ↦₇))
Stuck {［ c ∣ v ∣ c₁ ⨾☐• κ        ］} stuck = ⊥-elim (stuck (_ , ↦₁₀))
Stuck {［ c ∣ v ∣ ☐⊕ c₂ • κ       ］} stuck = ⊥-elim (stuck (_ , ↦₁₁))
Stuck {［ c ∣ v ∣ c₁ ⊕☐• κ        ］} stuck = ⊥-elim (stuck (_ , ↦₁₂))
Stuck {［ c ∣ v ∣ ☐⊗[ c₂ , y ]• κ ］} stuck = ⊥-elim (stuck (_ , ↦₈))
Stuck {［ c ∣ v ∣ [ c₁ , x ]⊗☐• κ ］} stuck = ⊥-elim (stuck (_ , ↦₉))
Stuck {⊠} stuck = inj₂ refl

-- Auxiliary function for forward evaluator
ev : ∀ {A B κ} → (c : A ↔ B) (v : ⟦ A ⟧)
   → Σ[ v' ∈ ⟦ B ⟧ ] ⟨ c ∣ v ∣ κ ⟩ ↦* ［ c ∣ v' ∣ κ ］
   ⊎ ⟨ c ∣ v ∣ κ ⟩ ↦* ⊠
ev uniti₊l v = inj₁ ((inj₂ v) , ↦₁ ∷ ◾)
ev unite₊l (inj₂ y) = inj₁ (y , ↦₁ ∷ ◾)
ev swap₊ (inj₁ v) = inj₁ (inj₂ v , (↦₁ ∷ ◾))
ev swap₊ (inj₂ v) = inj₁ (inj₁ v , (↦₁ ∷ ◾))
ev assocl₊ (inj₁ v) = inj₁ (inj₁ (inj₁ v) , (↦₁ ∷ ◾))
ev assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₁ (inj₂ v) , (↦₁ ∷ ◾))
ev assocl₊ (inj₂ (inj₂ v)) = inj₁ (inj₂ v , (↦₁ ∷ ◾))
ev assocr₊ (inj₁ (inj₁ v)) = inj₁ (inj₁ v , (↦₁ ∷ ◾))
ev assocr₊ (inj₁ (inj₂ v)) = inj₁ (inj₂ (inj₁ v) , (↦₁ ∷ ◾))
ev assocr₊ (inj₂ v) = inj₁ (inj₂ (inj₂ v) , (↦₁ ∷ ◾))
ev unite⋆l (tt , v) = inj₁ (v , (↦₁ ∷ ◾))
ev uniti⋆l v = inj₁ ((tt , v) , (↦₁ ∷ ◾))
ev swap⋆ (x , y) = inj₁ ((y , x) , (↦₁ ∷ ◾))
ev assocl⋆ (x , (y , z)) = inj₁ (((x , y) , z) , (↦₁ ∷ ◾))
ev assocr⋆ ((x , y) , z) = inj₁ ((x , (y , z)) , (↦₁ ∷ ◾))
ev dist (inj₁ x , z) = inj₁ (inj₁ (x , z) , (↦₁ ∷ ◾))
ev dist (inj₂ y , z) = inj₁ (inj₂ (y , z) , (↦₁ ∷ ◾))
ev factor (inj₁ (x , z)) = inj₁ ((inj₁ x , z) , (↦₁ ∷ ◾))
ev factor (inj₂ (y , z)) = inj₁ ((inj₂ y , z) , (↦₁ ∷ ◾))
ev id↔ v = inj₁ (v , (↦₂ ∷ ◾))
ev {κ = κ} (c₁ ⨾ c₂) v₁ with ev {κ = ☐⨾ c₂ • κ} c₁ v₁
... | inj₁ (v₂ , c₁↦*) with ev {κ = c₁ ⨾☐• κ} c₂ v₂
... | inj₁ (v₃ , c₂↦*) = inj₁ (v₃ , ((↦₃ ∷ c₁↦* ++↦ (↦₇ ∷ ◾)) ++↦ (c₂↦* ++↦ (↦₁₀ ∷ ◾))))
... | inj₂ c₂↦* = inj₂ ((↦₃ ∷ c₁↦* ++↦ (↦₇ ∷ ◾)) ++↦ c₂↦*)
ev {κ = κ} (c₁ ⨾ c₂) v₁ | inj₂ c₁↦* = inj₂ (↦₃ ∷ c₁↦*)
ev {κ = κ} (c₁ ⊕ c₂) (inj₁ x) with ev {κ = ☐⊕ c₂ • κ} c₁ x
... | inj₁ (x' , c₁↦*) = inj₁ (inj₁ x' , ↦₄ ∷ c₁↦* ++↦ (↦₁₁ ∷ ◾))
... | inj₂ c₁↦* = inj₂ (↦₄ ∷ c₁↦*) 
ev {κ = κ} (c₁ ⊕ c₂) (inj₂ y) with ev {κ = c₁ ⊕☐• κ} c₂ y
... | inj₁ (y' , c₂↦*) = inj₁ (inj₂ y' , ↦₅ ∷ c₂↦* ++↦ (↦₁₂ ∷ ◾))
... | inj₂ c₂↦* = inj₂ (↦₅ ∷ c₂↦*)
ev {κ = κ} (c₁ ⊗ c₂) (x , y) with ev {κ = ☐⊗[ c₂ , y ]• κ} c₁ x
... | inj₁ (x' , c₁↦*) with ev {κ = [ c₁ , x' ]⊗☐• κ} c₂ y
... | inj₁ (y' , c₂↦*) = inj₁ ((x' , y') , ((↦₆ ∷ c₁↦*) ++↦ ((↦₈ ∷ c₂↦*) ++↦ (↦₉ ∷ ◾))))
... | inj₂ c₂↦* = inj₂ ((↦₆ ∷ c₁↦*) ++↦ (↦₈ ∷ c₂↦*))
ev {κ = κ} (c₁ ⊗ c₂) (x , y) | inj₂ c₁↦* = inj₂ (↦₆ ∷ c₁↦*)
ev (ηₓ v) tt = inj₁ ((v , ↻) , (↦η ∷ ◾))
ev (εₓ v) (v' , ↻) with v ≟ v'
... | yes eq  = inj₁ (tt , (↦ε₁ {eq = eq} ∷ ◾))
... | no  neq = inj₂ (↦ε₂ {neq = neq} ∷ ◾)

-- Forward evaluator for PiFrac
eval : ∀ {A B} → (c : A ↔ B) → ⟦ A ⟧ → Maybe ⟦ B ⟧
eval c v = [ just ∘ proj₁ , (λ _ → nothing) ]′ (ev {κ = ☐} c v)

-- Forward evaluator which returns execution trace
evalₜᵣ : ∀ {A B} → (c : A ↔ B) → ⟦ A ⟧ → List State
evalₜᵣ c v = [ convert ∘ proj₂ , convert ]′ (ev {κ = ☐} c v)
  where
    convert : ∀ {st st'} → st ↦* st' → List State
    convert (◾ {st}) = st L.∷ []
    convert (_∷_ {st} r rs) = st L.∷ convert rs

-- Auxiliary function for backward evaluator
evᵣₑᵥ : ∀ {A B κ} → (c : A ↔ B) (v : ⟦ B ⟧)
      → Σ[ v' ∈ ⟦ A ⟧ ] ［ c ∣ v ∣ κ ］ ↦ᵣₑᵥ* ⟨ c ∣ v' ∣ κ ⟩
      ⊎ ∃[ A ] (∃[ v' ] (∃[ v'' ] (∃[ κ' ] (v' ≢ v'' × ［ c ∣ v ∣ κ ］ ↦ᵣₑᵥ* ［ ηₓ {A} v' ∣ (v'' , ↻) ∣ κ' ］))))
evᵣₑᵥ uniti₊l (inj₂ v) = inj₁ (v , (↦₁ ᵣₑᵥ ∷ ◾))
evᵣₑᵥ unite₊l v = inj₁ ((inj₂ v) , (↦₁ ᵣₑᵥ ∷ ◾))
evᵣₑᵥ swap₊ (inj₁ x) = inj₁ (inj₂ x , (↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ swap₊ (inj₂ y) = inj₁ (inj₁ y , (↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ assocl₊ (inj₁ (inj₁ x)) = inj₁ (inj₁ x , (↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ assocl₊ (inj₁ (inj₂ y)) = inj₁ (inj₂ (inj₁ y) , (↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ assocl₊ (inj₂ z) = inj₁ (inj₂ (inj₂ z) , (↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ assocr₊ (inj₁ x) = inj₁ (inj₁ (inj₁ x) , (↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ assocr₊ (inj₂ (inj₁ y)) = inj₁ (inj₁ (inj₂ y) , (↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ assocr₊ (inj₂ (inj₂ z)) = inj₁ (inj₂ z , (↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ unite⋆l v = inj₁ ((tt , v) , (↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ uniti⋆l (tt , v) = inj₁ (v , (↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ swap⋆ (x , y) = inj₁ ((y , x) , (↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ assocl⋆ ((x , y) , z) = inj₁ ((x , (y , z)) , (↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ assocr⋆ (x , (y , z)) = inj₁ (((x , y) , z) , (↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ dist (inj₁ (x , z)) = inj₁ ((inj₁ x , z) , (↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ dist (inj₂ (y , z)) = inj₁ ((inj₂ y , z) , (↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ factor (inj₁ x , z) = inj₁ (inj₁ (x , z) , (↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ factor (inj₂ y , z) = inj₁ (inj₂ (y , z) , (↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ id↔ v = inj₁ (v , (↦₂ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ {κ = κ} (c₁ ⨾ c₂) v₃ with evᵣₑᵥ {κ = c₁ ⨾☐• κ} c₂ v₃
... | inj₁ (v₂ , rs) with evᵣₑᵥ {κ = ☐⨾ c₂ • κ} c₁ v₂
... | inj₁ (v₁ , rs') = inj₁ (v₁ , ((↦₁₀ ᵣₑᵥ) ∷ (rs ++↦ᵣₑᵥ ((↦₇ ᵣₑᵥ) ∷ ◾))) ++↦ᵣₑᵥ (rs' ++↦ᵣₑᵥ ((↦₃ ᵣₑᵥ) ∷ ◾)))
... | inj₂ (_ , _ , _ , _ , neq , rs') = inj₂ (_ , _ , _ , _ , neq , (((↦₁₀ ᵣₑᵥ) ∷ (rs ++↦ᵣₑᵥ ((↦₇ ᵣₑᵥ) ∷ ◾))) ++↦ᵣₑᵥ rs'))
evᵣₑᵥ (c₁ ⨾ c₂) v₃ | inj₂ (_ , _ , _ , _ , neq , rs) = inj₂ (_ , _ , _ , _ , neq , (((↦₁₀ ᵣₑᵥ) ∷ ◾) ++↦ᵣₑᵥ rs))
evᵣₑᵥ {κ = κ} (c₁ ⊕ c₂) (inj₁ x) with evᵣₑᵥ {κ = ☐⊕ c₂ • κ} c₁ x
... | inj₁ (x' , rs) = inj₁ (inj₁ x' , (↦₁₁ ᵣₑᵥ) ∷ (rs ++↦ᵣₑᵥ ((↦₄ ᵣₑᵥ) ∷ ◾)))
... | inj₂ (_ , _ , _ , _ , neq , rs) = inj₂ (_ , _ , _ , _ , neq , (↦₁₁ ᵣₑᵥ) ∷ rs)
evᵣₑᵥ {κ = κ} (c₁ ⊕ c₂) (inj₂ y) with evᵣₑᵥ {κ = c₁ ⊕☐• κ} c₂ y
... | inj₁ (y' , rs) = inj₁ (inj₂ y' , (↦₁₂ ᵣₑᵥ) ∷ (rs ++↦ᵣₑᵥ ((↦₅ ᵣₑᵥ) ∷ ◾)))
... | inj₂ (_ , _ , _ , _ , neq , rs) = inj₂ (_ , _ , _ , _ , neq , (↦₁₂ ᵣₑᵥ) ∷ rs)
evᵣₑᵥ {κ = κ} (c₁ ⊗ c₂) (x , y) with evᵣₑᵥ {κ = [ c₁ , x ]⊗☐• κ} c₂ y
... | inj₁ (y' , rs) with evᵣₑᵥ {κ = ☐⊗[ c₂ , y' ]• κ} c₁ x
... | inj₁ (x' , rs') = inj₁ ((x' , y') , (((↦₉ ᵣₑᵥ) ∷ (rs ++↦ᵣₑᵥ ((↦₈ ᵣₑᵥ) ∷ ◾))) ++↦ᵣₑᵥ (rs' ++↦ᵣₑᵥ ((↦₆ ᵣₑᵥ) ∷ ◾))))
... | inj₂ (_ , _ , _ , _ , neq , rs') = inj₂ (_ , _ , _ , _ , neq , (((↦₉ ᵣₑᵥ) ∷ (rs ++↦ᵣₑᵥ ((↦₈ ᵣₑᵥ) ∷ ◾))) ++↦ᵣₑᵥ rs'))
evᵣₑᵥ (c₁ ⊗ c₂) (x , y) | inj₂ (_ , _ , _ , _ , neq , rs) = inj₂ (_ , _ , _ , _ , neq , ((↦₉ ᵣₑᵥ) ∷ rs))
evᵣₑᵥ (ηₓ v) (v' , ↻) with v ≟ v'
... | yes refl = inj₁ (tt , ((↦η ᵣₑᵥ) ∷ ◾))
... | no  neq  = inj₂ (_ , _ , _ , _ , neq , ◾)
evᵣₑᵥ (εₓ v) tt = inj₁ ((v , ↻) , ((↦ε₁ {eq = refl} ᵣₑᵥ) ∷ ◾))

-- Backward evaluator for Pi
evalᵣₑᵥ : ∀ {A B} → (c : A ↔ B) → ⟦ B ⟧ → Maybe ⟦ A ⟧
evalᵣₑᵥ c v = [ just ∘ proj₁ , (λ _ → nothing) ]′ (evᵣₑᵥ {κ = ☐} c v)
