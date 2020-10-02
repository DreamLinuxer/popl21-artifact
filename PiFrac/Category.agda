module PiFrac.Category where
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Braided
open import Categories.Category.Monoidal.Symmetric
open import Categories.Category.Monoidal.Rigid
open import Categories.Category.Monoidal.CompactClosed
open import Categories.Functor.Bifunctor
open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Groupoid
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Sum
open import Data.Product
open import Data.Maybe
open import Relation.Binary.Core
open import Relation.Binary hiding (Symmetric)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_)
open import PiFrac.Syntax
open import PiFrac.Opsem
open import PiFrac.Interp
open import PiFrac.Properties

Pi∙ : Category _ _ _ 
Pi∙ = record
    { Obj = Σ[ t ∈ 𝕌 ] ⟦ t ⟧
    ; _⇒_ = λ (A , a) (B , b) → Σ[ c ∈ (A ↔ B) ] (interp c a ≡ just b)
    ; _≈_ = λ {(A , a)} {(B , b)} (c , eq) (c' , eq) → ⊤
    ; id = id↔ , refl
    ; _∘_ = λ (c₂ , eq₂) (c₁ , eq₁) → comp (c₁ , eq₁) (c₂ , eq₂)
    ; assoc = tt
    ; sym-assoc = tt
    ; identityˡ = tt
    ; identityʳ = tt
    ; identity² = tt
    ; equiv = record { refl = tt ; sym = λ _ → tt ; trans = λ _ _ → tt }
    ; ∘-resp-≈ = λ _ _ → tt
    }
    where
    comp : ∀ {A B C a b c} → Σ[ c₁ ∈ (A ↔ B) ] (interp c₁ a ≡ just b) → Σ[ c₂ ∈ (B ↔ C) ] (interp c₂ b ≡ just c)
         → Σ[ c' ∈ (A ↔ C) ] (interp c' a ≡ just c)
    comp {c = c} (c₁ , eq₁) (c₂ , eq₂) = (c₁ ⨾ c₂) , subst (λ x → (x >>= interp c₂) ≡ just c) (sym eq₁) eq₂

Pi∙Groupoid : Groupoid _ _ _
Pi∙Groupoid = record { category = Pi∙
                     ; isGroupoid = record { _⁻¹ = λ (c , eq) → ! c , interp! c _ _ eq
                                           ; iso = record { isoˡ = tt
                                                          ; isoʳ = tt } } }

Pi∙Monoidal : Monoidal Pi∙
Pi∙Monoidal = record
            { ⊗ = record
                { F₀ = λ ((A , a) , (B , b)) → (A ×ᵤ B) , (a , b)
                ; F₁ = λ {((A , a) , (B , b))} {((C , c) , (D , d))} ((c₁ , eq₁) , (c₂ , eq₂)) →
                         (c₁ ⊗ c₂) , subst (λ x → (x >>= (λ v₁' → interp c₂ b >>= λ v₂' → just (v₁' , v₂'))) ≡ just (c , d))
                                           (sym eq₁) (subst (λ x → (x >>= λ v₂' → just (c , v₂')) ≡ just (c , d)) (sym eq₂) refl)
                ; identity = tt
                ; homomorphism = tt
                ; F-resp-≈ = λ _ → tt
                }
            ; unit = (𝟙 , tt)
            ; unitorˡ = record { from = unite⋆l , refl
                               ; to   = uniti⋆l , refl
                               ; iso  = record { isoˡ = tt ; isoʳ = tt } }
            ; unitorʳ = record { from = unite⋆r , refl
                               ; to   = uniti⋆r , refl
                               ; iso  = record { isoˡ = tt ; isoʳ = tt } }
            ; associator = record { from = assocr⋆ , refl
                                  ; to   = assocl⋆ , refl
                                  ; iso  = record { isoˡ = tt ; isoʳ = tt } }
            ; unitorˡ-commute-from = tt
            ; unitorˡ-commute-to = tt
            ; unitorʳ-commute-from = tt
            ; unitorʳ-commute-to = tt
            ; assoc-commute-from = tt
            ; assoc-commute-to = tt
            ; triangle = tt
            ; pentagon = tt
            }

Pi∙Braided : Braided Pi∙Monoidal
Pi∙Braided = record { braiding = record { F⇒G = record { η = λ _ → swap⋆ , refl
                                                       ; commute = λ _ → tt
                                                       ; sym-commute = λ _ → tt }
                                        ; F⇐G = record { η = λ _ → swap⋆ , refl
                                                       ; commute = λ _ → tt
                                                       ; sym-commute = λ _ → tt }
                                        ; iso = λ X → record { isoˡ = tt ; isoʳ = tt } }
                    ; hexagon₁ = tt
                    ; hexagon₂ = tt }

Pi∙Symmetric : Symmetric Pi∙Monoidal
Pi∙Symmetric = record { braided = Pi∙Braided
                      ; commutative = tt}

Pi∙Rigid : LeftRigid Pi∙Monoidal
Pi∙Rigid = record { _⁻¹ = λ {(A , a) → 𝟙/ a , ↻}
                  ; η = λ {(X , x)} → ηₓ x , refl
                  ; ε = λ {(X , x)} → (swap⋆ ⨾ εₓ x) , εₓ≡
                  ; snake₁ = tt
                  ; snake₂ = tt}
           where
             εₓ≡ : ∀ {X} {x : ⟦ X ⟧} → interp (swap⋆ ⨾ εₓ x) (↻ , x) ≡ just tt
             εₓ≡ {X} {x} with x ≟  x
             ... | yes refl = refl
             ... | no  neq  = ⊥-elim (neq refl)

Pi∙CompactClosed : CompactClosed Pi∙Monoidal
Pi∙CompactClosed = record { symmetric = Pi∙Symmetric
                          ; rigid     = inj₁ Pi∙Rigid }
