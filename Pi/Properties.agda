module Pi.Properties where
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Pi.Syntax
open import Pi.Opsem
open import Pi.NoRepeat
open import Pi.Invariants
open import Pi.Eval
open import Pi.Interp

-- Forward evaluation is deterministic
deterministic-eval : ∀ {A B} → (c : A ↔ B) (v : ⟦ A ⟧) (v₁ v₂ : ⟦ B ⟧)
                   → ⟨ c ∣ v ∣ ☐ ⟩ ↦* ［ c ∣ v₁ ∣ ☐ ］
                   → ⟨ c ∣ v ∣ ☐ ⟩ ↦* ［ c ∣ v₂ ∣ ☐ ］
                   → v₁ ≡ v₂
deterministic-eval c v v₁ v₂ ↦*₁ ↦*₂ with deterministic* ↦*₁ ↦*₂ (λ ()) (λ ())
... | refl = refl

-- Backward evaluation is deterministic
deterministic-evalᵣₑᵥ : ∀ {A B} → (c : A ↔ B) (v : ⟦ B ⟧) (v₁ v₂ : ⟦ A ⟧)
                      → ［ c ∣ v ∣ ☐ ］ ↦ᵣₑᵥ* ⟨ c ∣ v₁ ∣ ☐ ⟩
                      → ［ c ∣ v ∣ ☐ ］ ↦ᵣₑᵥ* ⟨ c ∣ v₂ ∣ ☐ ⟩
                      → v₁ ≡ v₂
deterministic-evalᵣₑᵥ c v v₁ v₂ ↦ᵣₑᵥ*₁ ↦ᵣₑᵥ*₂ with deterministicᵣₑᵥ* ↦ᵣₑᵥ*₁ ↦ᵣₑᵥ*₂ (λ ()) (λ ())
... | refl = refl

-- Forward evaluator is reversible
evalIsRev : ∀ {A B} → (c : A ↔ B) (v₁ : ⟦ A ⟧) (v₂ : ⟦ B ⟧)
          → eval c v₁ ≡ v₂ → evalᵣₑᵥ c v₂ ≡ v₁
evalIsRev c v₁ v₂ eq with ev {κ = ☐} c v₁
... | v₂' , c↦* with eq
... | refl with evᵣₑᵥ {κ = ☐} c v₂
... | v₁' , c↦*ᵣₑᵥ with deterministicᵣₑᵥ* c↦*ᵣₑᵥ (Rev↦ c↦*) (λ ()) (λ ())
... | refl = refl

-- Backward evaluator is reversible
evalᵣₑᵥIsRev : ∀ {A B} → (c : A ↔ B) (v₁ : ⟦ B ⟧) (v₂ : ⟦ A ⟧)
             → evalᵣₑᵥ c v₁ ≡ v₂ → eval c v₂ ≡ v₁
evalᵣₑᵥIsRev c v₁ v₂ eq with evᵣₑᵥ {κ = ☐} c v₁
... | v₂' , c↦ᵣₑᵥ* with eq
... | refl with ev {κ = ☐} c v₂
... | v₁' , c↦* with deterministic* c↦* (Rev↦ᵣₑᵥ c↦ᵣₑᵥ*) (λ ()) (λ ())
... | refl = refl

-- The abstract machine semantics is equivalent to the big-step semantics
eval≡interp : ∀ {A B} → (c : A ↔ B) → (v : ⟦ A ⟧) → eval c v ≡ interp c v
eval≡interp unite₊l (inj₂ y) = refl
eval≡interp uniti₊l v = refl
eval≡interp swap₊ (inj₁ x) = refl
eval≡interp swap₊ (inj₂ y) = refl
eval≡interp assocl₊ (inj₁ x) = refl
eval≡interp assocl₊ (inj₂ (inj₁ y)) = refl
eval≡interp assocl₊ (inj₂ (inj₂ z)) = refl
eval≡interp assocr₊ (inj₁ (inj₁ x)) = refl
eval≡interp assocr₊ (inj₁ (inj₂ y)) = refl
eval≡interp assocr₊ (inj₂ z) = refl
eval≡interp unite⋆l (tt , v) = refl
eval≡interp uniti⋆l v = refl
eval≡interp swap⋆ (x , y) = refl
eval≡interp assocl⋆ (x , (y , z)) = refl
eval≡interp assocr⋆ ((x , y) , z) = refl
eval≡interp dist (inj₁ x , z) = refl
eval≡interp dist (inj₂ y , z) = refl
eval≡interp factor (inj₁ (x , z)) = refl
eval≡interp factor (inj₂ (y , z)) = refl
eval≡interp id↔ v = refl
eval≡interp (c₁ ⨾ c₂) v with ev {κ = ☐} c₁ v | inspect (ev {κ = ☐} c₁) v
... | (v' , rs)   | [ eq ] with ev {κ = ☐} c₂ v' | inspect (ev {κ = ☐} c₂) v'
... | (v'' , rs') | [ eq' ] with ev {κ = ☐} (c₁ ⨾ c₂) v | inspect (ev {κ = ☐} (c₁ ⨾ c₂)) v
... | (u , rs'')  | [ refl ] rewrite (sym (eval≡interp c₁ v)) | eq | (sym (eval≡interp c₂ v')) | eq' with deterministic* ((↦₃ ∷ ◾) ++↦ appendκ↦* rs refl (☐⨾ c₂ • ☐) ++↦ (↦₇ ∷ ◾) ++↦ appendκ↦* rs' refl (c₁ ⨾☐• ☐) ++↦ (↦₁₀ ∷ ◾)) rs'' (λ ()) (λ ())
... | refl = refl
eval≡interp (c₁ ⊕ c₂) (inj₁ x) with ev {κ = ☐} c₁ x | inspect (ev {κ = ☐} c₁) x
... | (x' , rs) | [ eq ] with ev {κ = ☐} (c₁ ⊕ c₂) (inj₁ x) | inspect (ev {κ = ☐} (c₁ ⊕ c₂)) (inj₁ x)
... | (v , rs') | [ refl ] rewrite (sym (eval≡interp c₁ x)) | eq with deterministic* ((↦₄ ∷ ◾) ++↦ appendκ↦* rs refl (☐⊕ c₂ • ☐) ++↦ (↦₁₁ ∷ ◾)) rs' (λ ()) (λ ())
... | refl = refl
eval≡interp (c₁ ⊕ c₂) (inj₂ y) with ev {κ = ☐} c₂ y | inspect (ev {κ = ☐} c₂) y
... | (x' , rs) | [ eq ] with ev {κ = ☐} (c₁ ⊕ c₂) (inj₂ y) | inspect (ev {κ = ☐} (c₁ ⊕ c₂)) (inj₂ y)
... | (v , rs') | [ refl ] rewrite (sym (eval≡interp c₂ y)) | eq with deterministic* ((↦₅ ∷ ◾) ++↦ appendκ↦* rs refl (c₁ ⊕☐• ☐) ++↦ (↦₁₂ ∷ ◾)) rs' (λ ()) (λ ())
... | refl = refl
eval≡interp (c₁ ⊗ c₂) (x , y) with ev {κ = ☐} c₁ x | inspect (ev {κ = ☐} c₁) x
... | (x' , rs) | [ eq ] with ev {κ = ☐} c₂ y | inspect (ev {κ = ☐} c₂) y
... | (y' , rs') | [ eq' ] with ev {κ = ☐} (c₁ ⊗ c₂) (x , y) | inspect (ev {κ = ☐} (c₁ ⊗ c₂)) (x , y)
... | (_ , rs'') | [ refl ] rewrite (sym (eval≡interp c₁ x)) | eq | (sym (eval≡interp c₂ y)) | eq' with deterministic* (((↦₆ ∷ ◾) ++↦ appendκ↦* rs refl (☐⊗[ c₂ , y ]• ☐)) ++↦ (↦₈ ∷ ◾) ++↦ appendκ↦* rs' refl ([ c₁ , x' ]⊗☐• ☐) ++↦ (↦₉ ∷ ◾)) rs'' (λ ()) (λ ())
... | refl = refl

c⨾!c≡id↔ : ∀ {A B} (c : A ↔ B) → (x : ⟦ A ⟧) → interp (c ⨾ ! c) x ≡ interp id↔ x
c⨾!c≡id↔ unite₊l (inj₂ y) = refl
c⨾!c≡id↔ uniti₊l x = refl
c⨾!c≡id↔ swap₊ (inj₁ x) = refl
c⨾!c≡id↔ swap₊ (inj₂ y) = refl
c⨾!c≡id↔ assocl₊ (inj₁ x) = refl
c⨾!c≡id↔ assocl₊ (inj₂ (inj₁ y)) = refl
c⨾!c≡id↔ assocl₊ (inj₂ (inj₂ z)) = refl
c⨾!c≡id↔ assocr₊ (inj₁ (inj₁ x)) = refl
c⨾!c≡id↔ assocr₊ (inj₁ (inj₂ y)) = refl
c⨾!c≡id↔ assocr₊ (inj₂ z) = refl
c⨾!c≡id↔ unite⋆l (tt , x) = refl
c⨾!c≡id↔ uniti⋆l x = refl
c⨾!c≡id↔ swap⋆ (x , y) = refl
c⨾!c≡id↔ assocl⋆ (x , (y , z)) = refl
c⨾!c≡id↔ assocr⋆ ((x , y) , z) = refl
c⨾!c≡id↔ dist (inj₁ x , z) = refl
c⨾!c≡id↔ dist (inj₂ y , z) = refl
c⨾!c≡id↔ factor (inj₁ (x , z)) = refl
c⨾!c≡id↔ factor (inj₂ (y , z)) = refl
c⨾!c≡id↔ id↔ x = refl
c⨾!c≡id↔ (c₁ ⨾ c₂) x rewrite c⨾!c≡id↔ c₂ (interp c₁ x) = c⨾!c≡id↔ c₁ x
c⨾!c≡id↔ (c₁ ⊕ c₂) (inj₁ x) rewrite c⨾!c≡id↔ c₁ x = refl
c⨾!c≡id↔ (c₁ ⊕ c₂) (inj₂ y) rewrite c⨾!c≡id↔ c₂ y = refl
c⨾!c≡id↔ (c₁ ⊗ c₂) (x , y) rewrite c⨾!c≡id↔ c₁ x | c⨾!c≡id↔ c₂ y = refl

!!c≡c : ∀ {A B} (c : A ↔ B) → ! (! c) ≡ c
!!c≡c unite₊l = refl
!!c≡c uniti₊l = refl
!!c≡c swap₊ = refl
!!c≡c assocl₊ = refl
!!c≡c assocr₊ = refl
!!c≡c unite⋆l = refl
!!c≡c uniti⋆l = refl
!!c≡c swap⋆ = refl
!!c≡c assocl⋆ = refl
!!c≡c assocr⋆ = refl
!!c≡c absorbr = refl
!!c≡c factorzl = refl
!!c≡c dist = refl
!!c≡c factor = refl
!!c≡c id↔ = refl
!!c≡c (c₁ ⨾ c₂) rewrite !!c≡c c₁ | !!c≡c c₂ = refl
!!c≡c (c₁ ⊕ c₂) rewrite !!c≡c c₁ | !!c≡c c₂ = refl
!!c≡c (c₁ ⊗ c₂) rewrite !!c≡c c₁ | !!c≡c c₂ = refl

!c⨾c≡id↔ : ∀ {A B} (c : A ↔ B) → (x : ⟦ B ⟧) → interp (! c ⨾ c) x ≡ interp id↔ x
!c⨾c≡id↔ c x = trans (cong (λ c' → interp c' (interp (! c) x)) (sym (!!c≡c c)))
                    (c⨾!c≡id↔ (! c) x)
