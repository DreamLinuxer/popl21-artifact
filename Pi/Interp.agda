module Pi.Interp where
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Pi.Syntax
open import Pi.Opsem

-- Big-step intepreter
interp : {A B : 𝕌} → (A ↔ B) → ⟦ A ⟧ → ⟦ B ⟧
interp unite₊l (inj₂ v)         = v
interp uniti₊l v                = inj₂ v
interp swap₊   (inj₁ v)         = inj₂ v
interp swap₊   (inj₂ v)         = inj₁ v
interp assocl₊ (inj₁ v)         = inj₁ (inj₁ v)
interp assocl₊ (inj₂ (inj₁ v))  = inj₁ (inj₂ v)
interp assocl₊ (inj₂ (inj₂ v))  = inj₂ v
interp assocr₊ (inj₁ (inj₁ v))  = inj₁ v
interp assocr₊ (inj₁ (inj₂ v))  = inj₂ (inj₁ v)
interp assocr₊ (inj₂ v)         = inj₂ (inj₂ v)
interp unite⋆l (tt , v)         = v
interp uniti⋆l v                = (tt , v)
interp swap⋆   (v₁ , v₂)        = (v₂ , v₁)
interp assocl⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
interp assocr⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
interp dist    (inj₁ v₁ , v₃)   = inj₁ (v₁ , v₃)
interp dist    (inj₂ v₂ , v₃)   = inj₂ (v₂ , v₃)
interp factor  (inj₁ (v₁ , v₃)) = (inj₁ v₁ , v₃)
interp factor  (inj₂ (v₂ , v₃)) = (inj₂ v₂ , v₃)
interp id↔     v                = v
interp (c₁ ⨾ c₂) v = interp c₂ (interp c₁ v)
interp (c₁ ⊕ c₂) (inj₁ v) = inj₁ (interp c₁ v)
interp (c₁ ⊕ c₂) (inj₂ v) = inj₂ (interp c₂ v)
interp (c₁ ⊗ c₂) (v₁ , v₂) = (interp c₁ v₁ , interp c₂ v₂)
