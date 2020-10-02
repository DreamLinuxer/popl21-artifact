module Pi.Eval where
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.List as L hiding (_∷_)
open import Relation.Binary.PropositionalEquality
open import Pi.Syntax
open import Pi.Opsem
open import Pi.NoRepeat

-- Stuck states must be of the form ［ c ∣ v ∣ ☐ ］
Stuck : ∀ {st} → is-stuck st
      → (Σ[ A ∈ 𝕌 ] Σ[ B ∈ 𝕌 ] Σ[ c ∈ A ↔ B ] Σ[ v ∈ ⟦ B ⟧ ] st ≡ ［ c ∣ v ∣ ☐ ］)
Stuck {⟨ unite₊l  ∣ v       ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₁))
Stuck {⟨ uniti₊l  ∣ v       ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₁))
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
Stuck {⟨ absorbr  ∣ v       ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₁))
Stuck {⟨ factorzl ∣ v       ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₁))
Stuck {⟨ id↔      ∣ v       ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₂))
Stuck {⟨ c₁ ⨾ c₂  ∣ v       ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₃))
Stuck {⟨ c₁ ⊕ c₂  ∣ inj₁ x  ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₄))
Stuck {⟨ c₁ ⊕ c₂  ∣ inj₂ y  ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₅))
Stuck {⟨ c₁ ⊗ c₂  ∣ (x , y) ∣ κ ⟩} stuck = ⊥-elim (stuck (_ , ↦₆))
Stuck {［ c ∣ v ∣ ☐               ］} stuck = _ , _ , _ , _ , refl
Stuck {［ c ∣ v ∣ ☐⨾ c₂ • κ       ］} stuck = ⊥-elim (stuck (_ , ↦₇))
Stuck {［ c ∣ v ∣ c₁ ⨾☐• κ        ］} stuck = ⊥-elim (stuck (_ , ↦₁₀))
Stuck {［ c ∣ v ∣ ☐⊕ c₂ • κ       ］} stuck = ⊥-elim (stuck (_ , ↦₁₁))
Stuck {［ c ∣ v ∣ c₁ ⊕☐• κ        ］} stuck = ⊥-elim (stuck (_ , ↦₁₂))
Stuck {［ c ∣ v ∣ ☐⊗[ c₂ , y ]• κ ］} stuck = ⊥-elim (stuck (_ , ↦₈))
Stuck {［ c ∣ v ∣ [ c₁ , x ]⊗☐• κ ］} stuck = ⊥-elim (stuck (_ , ↦₉))

-- Auxiliary function for forward evaluator
ev : ∀ {A B κ} → (c : A ↔ B) (v : ⟦ A ⟧) → Σ[ v' ∈ ⟦ B ⟧ ] ⟨ c ∣ v ∣ κ ⟩ ↦* ［ c ∣ v' ∣ κ ］
ev unite₊l (inj₂ v) = v , (↦₁ ∷ ◾)
ev uniti₊l v = inj₂ v , (↦₁ ∷ ◾)
ev swap₊ (inj₁ v) = inj₂ v , (↦₁ ∷ ◾)
ev swap₊ (inj₂ v) = inj₁ v , (↦₁ ∷ ◾)
ev assocl₊ (inj₁ v) = inj₁ (inj₁ v) , (↦₁ ∷ ◾)
ev assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v) , (↦₁ ∷ ◾)
ev assocl₊ (inj₂ (inj₂ v)) = inj₂ v , (↦₁ ∷ ◾)
ev assocr₊ (inj₁ (inj₁ v)) = inj₁ v , (↦₁ ∷ ◾)
ev assocr₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v) , (↦₁ ∷ ◾)
ev assocr₊ (inj₂ v) = inj₂ (inj₂ v) , (↦₁ ∷ ◾)
ev unite⋆l (tt , v) = v , (↦₁ ∷ ◾)
ev uniti⋆l v = (tt , v) , (↦₁ ∷ ◾)
ev swap⋆ (x , y) = (y , x) , (↦₁ ∷ ◾)
ev assocl⋆ (x , (y , z)) = ((x , y) , z) , (↦₁ ∷ ◾)
ev assocr⋆ ((x , y) , z) = (x , (y , z)) , (↦₁ ∷ ◾)
ev dist (inj₁ x , z) = inj₁ (x , z) , (↦₁ ∷ ◾)
ev dist (inj₂ y , z) = inj₂ (y , z) , (↦₁ ∷ ◾)
ev factor (inj₁ (x , z)) = (inj₁ x , z) , (↦₁ ∷ ◾)
ev factor (inj₂ (y , z)) = (inj₂ y , z) , (↦₁ ∷ ◾)
ev id↔ v = v , (↦₂ ∷ ◾)
ev {κ = κ} (c₁ ⨾ c₂) v₁ with ev {κ = ☐⨾ c₂ • κ} c₁ v₁
... | (v₂ , c₁↦*) with ev {κ = c₁ ⨾☐• κ} c₂ v₂
... | (v₃ , c₂↦*) = v₃ , ((↦₃ ∷ c₁↦* ++↦ (↦₇ ∷ ◾)) ++↦ (c₂↦* ++↦ (↦₁₀ ∷ ◾)))
ev {κ = κ} (c₁ ⊕ c₂) (inj₁ x) with ev {κ = ☐⊕ c₂ • κ} c₁ x
... | x' , c₁↦* = inj₁ x' , ↦₄ ∷ c₁↦* ++↦ (↦₁₁ ∷ ◾)
ev {κ = κ} (c₁ ⊕ c₂) (inj₂ y) with ev {κ = c₁ ⊕☐• κ} c₂ y
... | y' , c₂↦* = inj₂ y' , ↦₅ ∷ c₂↦* ++↦ (↦₁₂ ∷ ◾)
ev {κ = κ} (c₁ ⊗ c₂) (x , y) with ev {κ = ☐⊗[ c₂ , y ]• κ} c₁ x
... | x' , c₁↦* with ev {κ = [ c₁ , x' ]⊗☐• κ} c₂ y
... | y' , c₂↦* = (x' , y') , ((↦₆ ∷ c₁↦*) ++↦ ((↦₈ ∷ c₂↦*) ++↦ (↦₉ ∷ ◾)))

-- Forward evaluator for Pi
eval : ∀ {A B} → (c : A ↔ B) → ⟦ A ⟧ → ⟦ B ⟧
eval c v = proj₁ (ev {κ = ☐} c v)

-- Forward evaluator which returns execution trace
evalₜᵣ : ∀ {A B} → (c : A ↔ B) → ⟦ A ⟧ → List State
evalₜᵣ c v = convert (proj₂ (ev {κ = ☐} c v))
  where
    convert : ∀ {st st'} → st ↦* st' → List State
    convert (◾ {st}) = st L.∷ []
    convert (_∷_ {st} r rs) = st L.∷ convert rs

-- Auxiliary function for backward evaluator
evᵣₑᵥ : ∀ {A B κ} → (c : A ↔ B) (v' : ⟦ B ⟧) → Σ[ v ∈ ⟦ A ⟧ ] ［ c ∣ v' ∣ κ ］ ↦ᵣₑᵥ* ⟨ c ∣ v ∣ κ ⟩
evᵣₑᵥ unite₊l v' = inj₂ v' , ((↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ uniti₊l (inj₂ v') = v' , ((↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ swap₊ (inj₁ v') = inj₂ v' , ((↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ swap₊ (inj₂ v') = inj₁ v' , ((↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ assocl₊ (inj₁ (inj₁ v')) = inj₁ v' , ((↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ assocl₊ (inj₁ (inj₂ v')) = inj₂ (inj₁ v') , ((↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ assocl₊ (inj₂ v') = inj₂ (inj₂ v') , ((↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ assocr₊ (inj₁ v') = inj₁ (inj₁ v') , ((↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ assocr₊ (inj₂ (inj₁ v')) = inj₁ (inj₂ v') , ((↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ assocr₊ (inj₂ (inj₂ v')) = inj₂ v' , ((↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ unite⋆l v' = (tt , v') , ((↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ uniti⋆l (tt , v') = v' , ((↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ swap⋆ (x' , y') = (y' , x') , ((↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ assocl⋆ ((x' , y') , z') = (x' , (y' , z')) , ((↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ assocr⋆ (x' , (y' , z')) = ((x' , y') , z') , ((↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ dist (inj₁ (x' , z')) = (inj₁ x' , z') , ((↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ dist (inj₂ (y' , z')) = (inj₂ y' , z') , ((↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ factor (inj₁ x' , z') = (inj₁ (x' , z')) , ((↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ factor (inj₂ y' , z') = (inj₂ (y' , z')) , ((↦₁ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ id↔ v' = v' , ((↦₂ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ {κ = κ} (c₁ ⨾ c₂) v₃ with evᵣₑᵥ {κ = c₁ ⨾☐• κ} c₂ v₃
... | (v₂ , c₂↦ᵣₑᵥ*) with evᵣₑᵥ {κ = ☐⨾ c₂ • κ} c₁ v₂
... | (v₁ , c₁↦ᵣₑᵥ*) = v₁ , ((↦₁₀ ᵣₑᵥ) ∷ c₂↦ᵣₑᵥ*) ++↦ᵣₑᵥ ((↦₇ ᵣₑᵥ) ∷ (c₁↦ᵣₑᵥ* ++↦ᵣₑᵥ ((↦₃ ᵣₑᵥ) ∷ ◾)))
evᵣₑᵥ {κ = κ} (c₁ ⊕ c₂) (inj₁ v') with evᵣₑᵥ {κ = ☐⊕ c₂ • κ} c₁ v'
... | v , c₁↦ᵣₑᵥ* = inj₁ v , ((↦₁₁ ᵣₑᵥ) ∷ c₁↦ᵣₑᵥ*) ++↦ᵣₑᵥ ((↦₄ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ {κ = κ} (c₁ ⊕ c₂) (inj₂ v') with evᵣₑᵥ {κ = c₁ ⊕☐• κ} c₂ v'
... | v , c₂↦ᵣₑᵥ* = inj₂ v , ((↦₁₂ ᵣₑᵥ) ∷ c₂↦ᵣₑᵥ*) ++↦ᵣₑᵥ ((↦₅ ᵣₑᵥ) ∷ ◾)
evᵣₑᵥ {κ = κ} (c₁ ⊗ c₂) (x' , y') with evᵣₑᵥ {κ = [ c₁ , x' ]⊗☐• κ} c₂ y'
... | y , c₂↦ᵣₑᵥ* with evᵣₑᵥ {κ = ☐⊗[ c₂ , y ]• κ} c₁ x'
... | x , c₁↦ᵣₑᵥ* = (x , y) , ((↦₉ ᵣₑᵥ) ∷ c₂↦ᵣₑᵥ*) ++↦ᵣₑᵥ (((↦₈ ᵣₑᵥ) ∷ c₁↦ᵣₑᵥ*) ++↦ᵣₑᵥ ((↦₆ ᵣₑᵥ) ∷ ◾))

-- Backward evaluator for Pi
evalᵣₑᵥ : ∀ {A B} → (c : A ↔ B) → ⟦ B ⟧ → ⟦ A ⟧
evalᵣₑᵥ c v' = proj₁ (evᵣₑᵥ {κ = ☐} c v')
