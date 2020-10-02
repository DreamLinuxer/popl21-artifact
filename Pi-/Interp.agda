module Pi-.Interp where
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Pi-.Syntax
open import Pi-.Opsem
open import Pi-.Eval

{-# TERMINATING #-}
mutual
  interp : {A B : 𝕌} → (A ↔ B) → Val A B → Val B A
  -- Forward
  interp unite₊l (inj₂ y ⃗)        = y ⃗
  interp uniti₊l (v ⃗)             = inj₂ v ⃗
  interp swap₊   (inj₁ x ⃗)        = inj₂ x ⃗
  interp swap₊   (inj₂ y ⃗)        = inj₁ y ⃗
  interp assocl₊ (inj₁ x ⃗)        = inj₁ (inj₁ x) ⃗
  interp assocl₊ (inj₂ (inj₁ y) ⃗) = inj₁ (inj₂ y) ⃗
  interp assocl₊ (inj₂ (inj₂ z) ⃗) = inj₂ z ⃗
  interp assocr₊ (inj₁ (inj₁ x) ⃗) = inj₁ x ⃗
  interp assocr₊ (inj₁ (inj₂ y) ⃗) = inj₂ (inj₁ y) ⃗
  interp assocr₊ (inj₂ z ⃗)        = inj₂ (inj₂ z) ⃗
  interp unite⋆l ((tt , v) ⃗)      = v ⃗
  interp uniti⋆l (v ⃗)             = (tt , v) ⃗
  interp swap⋆   ((x , y) ⃗)       = (y , x) ⃗
  interp assocl⋆ ((x , (y , z)) ⃗) = ((x , y) , z) ⃗
  interp assocr⋆ (((x , y) , z) ⃗) = (x , y , z) ⃗
  interp dist    ((inj₁ x , z) ⃗)  = inj₁ (x , z) ⃗
  interp dist    ((inj₂ y , z) ⃗)  = inj₂ (y , z) ⃗
  interp factor  (inj₁ (x , z) ⃗)  = (inj₁ x , z) ⃗
  interp factor  (inj₂ (y , z) ⃗)  = (inj₂ y , z) ⃗
  interp id↔     (v ⃗)             = v ⃗
  interp (c₁ ⨾ c₂) (v ⃗) with interp c₁ (v ⃗)
  interp (c₁ ⨾ c₂) (v ⃗) | (v' ⃖) = v' ⃖
  interp (c₁ ⨾ c₂) (v ⃗) | (v' ⃗) = c₁ ⨾[ v' ⃗]⨾ c₂
  interp (c₁ ⊕ c₂) (inj₁ x ⃗) with interp c₁ (x ⃗)
  interp (c₁ ⊕ c₂) (inj₁ x ⃗) | (x' ⃗) = inj₁ x' ⃗
  interp (c₁ ⊕ c₂) (inj₁ x ⃗) | (x' ⃖) = inj₁ x' ⃖
  interp (c₁ ⊕ c₂) (inj₂ y ⃗) with interp c₂ (y ⃗)
  interp (c₁ ⊕ c₂) (inj₂ y ⃗) | (y' ⃗) = inj₂ y' ⃗
  interp (c₁ ⊕ c₂) (inj₂ y ⃗) | (y' ⃖) = inj₂ y' ⃖
  interp (c₁ ⊗ c₂) ((x , y) ⃗) with interp c₁ (x ⃗)
  interp (c₁ ⊗ c₂) ((x , y) ⃗) | (x' ⃖) = (x' , y) ⃖
  interp (c₁ ⊗ c₂) ((x , y) ⃗) | (x' ⃗) with interp c₂ (y ⃗)
  interp (c₁ ⊗ c₂) ((x , y) ⃗) | (x' ⃗) | (y' ⃗) = (x' , y') ⃗
  interp (c₁ ⊗ c₂) ((x , y) ⃗) | (x' ⃗) | (y' ⃖) = (x , y') ⃖
  interp ε₊ (inj₁ v ⃗)     = inj₂ (- v) ⃖
  interp ε₊ (inj₂ (- v) ⃗) = inj₁ v ⃖
  -- Backward
  interp unite₊l (v ⃖)             = inj₂ v ⃖
  interp uniti₊l (inj₂ v ⃖)        = v ⃖
  interp swap₊   (inj₁ x ⃖)        = inj₂ x ⃖
  interp swap₊   (inj₂ y ⃖)        = inj₁ y ⃖
  interp assocl₊ (inj₁ (inj₁ x) ⃖) = inj₁ x ⃖
  interp assocl₊ (inj₁ (inj₂ y) ⃖) = inj₂ (inj₁ y) ⃖
  interp assocl₊ (inj₂ z ⃖)        = inj₂ (inj₂ z) ⃖
  interp assocr₊ (inj₁ x ⃖)        = inj₁ (inj₁ x) ⃖
  interp assocr₊ (inj₂ (inj₁ y) ⃖) = inj₁ (inj₂ y) ⃖
  interp assocr₊ (inj₂ (inj₂ z) ⃖) = inj₂ z ⃖
  interp unite⋆l (v ⃖)             = (tt , v) ⃖
  interp uniti⋆l ((tt , v) ⃖)      = v ⃖
  interp swap⋆   ((x , y) ⃖)       = (y , x) ⃖
  interp assocl⋆ (((x , y) , z) ⃖) = (x , (y , z)) ⃖
  interp assocr⋆ ((x , (y , z)) ⃖) = ((x , y) , z) ⃖
  interp dist    (inj₁ (x , z) ⃖)  = (inj₁ x , z) ⃖
  interp dist    (inj₂ (y , z) ⃖)  = (inj₂ y , z) ⃖
  interp factor  ((inj₁ x , z) ⃖)  = inj₁ (x , z) ⃖
  interp factor  ((inj₂ y , z) ⃖)  = inj₂ (y , z) ⃖
  interp id↔ (v ⃖) = v ⃖
  interp (c₁ ⨾ c₂) (v ⃖) with interp c₂ (v ⃖)
  interp (c₁ ⨾ c₂) (v ⃖) | v' ⃗ = v' ⃗
  interp (c₁ ⨾ c₂) (v ⃖) | v' ⃖ = c₁ ⨾[ v' ⃖]⨾ c₂
  interp (c₁ ⊕ c₂) (inj₁ x ⃖) with interp c₁ (x ⃖)
  interp (c₁ ⊕ c₂) (inj₁ x ⃖) | (x' ⃖) = inj₁ x' ⃖
  interp (c₁ ⊕ c₂) (inj₁ x ⃖) | (x' ⃗) = inj₁ x' ⃗
  interp (c₁ ⊕ c₂) (inj₂ y ⃖) with interp c₂ (y ⃖)
  interp (c₁ ⊕ c₂) (inj₂ y ⃖) | (y' ⃖) = inj₂ y' ⃖
  interp (c₁ ⊕ c₂) (inj₂ y ⃖) | (y' ⃗) = inj₂ y' ⃗
  interp (c₁ ⊗ c₂) ((x , y) ⃖) with interp c₂ (y ⃖)
  interp (c₁ ⊗ c₂) ((x , y) ⃖) | (y' ⃗) = (x , y') ⃗
  interp (c₁ ⊗ c₂) ((x , y) ⃖) | (y' ⃖) with interp c₁ (x ⃖)
  interp (c₁ ⊗ c₂) ((x , y) ⃖) | (y' ⃖) | (x' ⃖) = (x' , y') ⃖
  interp (c₁ ⊗ c₂) ((x , y) ⃖) | (y' ⃖) | (x' ⃗) = (x' , y) ⃗
  interp η₊ (inj₁ v ⃖)     = inj₂ (- v) ⃗
  interp η₊ (inj₂ (- v) ⃖) = inj₁ v ⃗

  _⨾[_⃗]⨾_ : ∀ {A B C} → (A ↔ B) → ⟦ B ⟧ → (B ↔ C) → Val C A
  c₁ ⨾[ b ⃗]⨾ c₂ with interp c₂ (b ⃗)
  c₁ ⨾[ b ⃗]⨾ c₂ | c ⃗ = c ⃗
  c₁ ⨾[ b ⃗]⨾ c₂ | b' ⃖ = c₁ ⨾[ b' ⃖]⨾ c₂

  _⨾[_⃖]⨾_ : ∀ {A B C} → (A ↔ B) → ⟦ B ⟧ → (B ↔ C) → Val C A
  c₁ ⨾[ b ⃖]⨾ c₂ with interp c₁ (b ⃖)
  c₁ ⨾[ b ⃖]⨾ c₂ | a ⃖ = a ⃖
  c₁ ⨾[ b ⃖]⨾ c₂ | b' ⃗ = c₁ ⨾[ b' ⃗]⨾ c₂
