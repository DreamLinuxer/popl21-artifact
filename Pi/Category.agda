module Pi.Category where
open import Categories.Category
open import Categories.Category.Groupoid
open import Categories.Category.Product
open import Categories.Functor.Bifunctor
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Braided
open import Categories.Category.Monoidal.Symmetric
open import Categories.Category.RigCategory
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
open import Base
open import Pi.Syntax
open import Pi.Opsem
open import Pi.Interp
open import Pi.Properties

Pi : Category _ _ _ 
Pi = record {
       Obj = 𝕌
     ; _⇒_ = _↔_
     ; _≈_ = λ c₁ c₂ → interp c₁ ∼ interp c₂
     ; id = id↔
     ; _∘_ = λ f g → g ⨾ f
     ; assoc = λ _ → refl
     ; sym-assoc = λ _ → refl
     ; identityˡ = λ _ → refl
     ; identityʳ = λ _ → refl
     ; identity² = λ _ → refl
     ; equiv = record { refl = λ _ → refl ;
                        sym = λ f~g x → sym (f~g x) ;
                        trans = λ f~g g~h x → trans (f~g x) (g~h x) }
     ; ∘-resp-≈ = λ {A} {B} {C} {f} {h} {g} {i} f~h g~i x → trans (cong (interp f) (g~i x))
                                                                  (f~h (interp i x))}

PiGroupoid : Groupoid _ _ _
PiGroupoid = record {
               category = Pi
             ; isGroupoid = record { _⁻¹ = !_
                                   ; iso = λ {A} {B} {c} →
                                             record { isoˡ = c⨾!c≡id↔ c
                                                    ; isoʳ = !c⨾c≡id↔ c}}}

Pi+Monoidal : Monoidal Pi
Pi+Monoidal = record {
                ⊗ = record {
                      F₀ = λ {(A , B) → A +ᵤ B}
                    ; F₁ = λ {(c₁ , c₂) → c₁ ⊕ c₂ }
                    ; identity = λ {(inj₁ x) → refl ; (inj₂ y) → refl}
                    ; homomorphism = λ {(inj₁ x) → refl ; (inj₂ y) → refl}
                    ; F-resp-≈ = λ { (f~h , g~i) (inj₁ x) → cong inj₁ (f~h x)
                                   ; (f~h , g~i) (inj₂ y) → cong inj₂ (g~i y)}}
              ; unit = 𝟘
              ; unitorˡ = record {
                            from = unite₊l
                          ; to = uniti₊l
                          ; iso = record { isoˡ = λ {(inj₂ y) → refl} ; isoʳ = λ x → refl}}
              ; unitorʳ = record {
                            from = unite₊r
                          ; to = uniti₊r
                          ; iso = record { isoˡ = λ {(inj₁ x) → refl} ; isoʳ = λ x → refl}}
              ; associator = record {
                               from = assocr₊
                             ; to = assocl₊
                             ; iso = record { isoˡ = λ {(inj₁ (inj₁ x)) → refl ; (inj₁ (inj₂ y)) → refl ; (inj₂ z) → refl}
                                            ; isoʳ = λ {(inj₁ x) → refl ; (inj₂ (inj₁ y)) → refl ; (inj₂ (inj₂ z)) → refl}}}
              ; unitorˡ-commute-from = λ {(inj₂ y) → refl}
              ; unitorˡ-commute-to = λ x → refl
              ; unitorʳ-commute-from = λ {(inj₁ x) → refl}
              ; unitorʳ-commute-to = λ x → refl
              ; assoc-commute-from = λ {(inj₁ (inj₁ x)) → refl ; (inj₁ (inj₂ y)) → refl ; (inj₂ z) → refl}
              ; assoc-commute-to = λ {(inj₁ x) → refl ; (inj₂ (inj₁ y)) → refl ; (inj₂ (inj₂ z)) → refl}
              ; triangle = λ {(inj₁ (inj₁ x)) → refl ; (inj₂ z) → refl}
              ; pentagon = λ {(inj₁ (inj₁ (inj₁ x))) → refl ;
                              (inj₁ (inj₁ (inj₂ y))) → refl ;
                              (inj₁ (inj₂ z)) → refl ;
                              (inj₂ w) → refl}}

Pi×Monoidal : Monoidal Pi
Pi×Monoidal = record {
                ⊗ = record {
                      F₀ = λ {(A , B) → A ×ᵤ B}
                    ; F₁ = λ {(c₁ , c₂) → c₁ ⊗ c₂ }
                    ; identity = λ {(x , y) → refl}
                    ; homomorphism = λ {(x , y) → refl}
                    ; F-resp-≈ = λ { {(A , B)} {(C , D)} {(f , g)} {(h , i)} (f~h , g~i) (x , y) →
                                     trans (cong ((interp f x ,_)) (g~i y)) (cong (_, (interp i y)) (f~h x))}}
              ; unit = 𝟙
              ; unitorˡ = record {
                            from = unite⋆l
                          ; to = uniti⋆l
                          ; iso = record { isoˡ = λ {(tt , x) → refl} ; isoʳ = λ x → refl}}
              ; unitorʳ = record {
                            from = unite⋆r
                          ; to = uniti⋆r
                          ; iso = record { isoˡ = λ {(x , tt) → refl} ; isoʳ = λ x → refl}}
              ; associator = record {
                               from = assocr⋆
                             ; to = assocl⋆
                             ; iso = record { isoˡ = λ {((x , y) , z) → refl} ; isoʳ = λ {(x , (y , z)) → refl}}}
              ; unitorˡ-commute-from = λ {(tt , x) → refl}
              ; unitorˡ-commute-to = λ x → refl
              ; unitorʳ-commute-from = λ {(x , tt) → refl}
              ; unitorʳ-commute-to = λ x → refl
              ; assoc-commute-from = λ {((x , y) , z) → refl}
              ; assoc-commute-to = λ {(x , (y , z)) → refl}
              ; triangle = λ {((x , tt) , y) → refl}
              ; pentagon = λ {(((x , y) , z) , w) → refl}}

Pi+Braided : Braided Pi+Monoidal
Pi+Braided = record {
               braiding = record { F⇒G = record { η = λ _ → swap₊
                                                ; commute = λ {(f , g) (inj₁ x) → refl;
                                                               (f , g) (inj₂ y) → refl}
                                                ; sym-commute = λ {(f , g) (inj₁ x) → refl;
                                                                   (f , g) (inj₂ y) → refl}}
                                 ; F⇐G = record { η = λ _ → swap₊
                                                ; commute = λ {(f , g) (inj₁ x) → refl;
                                                               (f , g) (inj₂ y) → refl}
                                                ; sym-commute = λ {(f , g) (inj₁ x) → refl;
                                                                   (f , g) (inj₂ y) → refl}}
                                 ; iso = λ (A , B) → record { isoˡ = λ {(inj₁ x) → refl ; (inj₂ y) → refl}
                                                            ; isoʳ = λ {(inj₁ x) → refl ; (inj₂ y) → refl}}}
             ; hexagon₁ = λ {(inj₁ (inj₁ x)) → refl ; (inj₁ (inj₂ y)) → refl ; (inj₂ z) → refl}
             ; hexagon₂ = λ {(inj₁ x) → refl ; (inj₂ (inj₁ y)) → refl ; (inj₂ (inj₂ z)) → refl}}

Pi×Braided : Braided Pi×Monoidal
Pi×Braided = record {
               braiding = record { F⇒G = record { η = λ _ → swap⋆
                                                ; commute = λ {(f , g) (x , y) → refl}
                                                ; sym-commute = λ {(f , g) (x , y) → refl}}
                                 ; F⇐G = record { η = λ _ → swap⋆
                                                ; commute = λ {(f , g) (x , y) → refl}
                                                ; sym-commute = λ {(f , g) (x , y) → refl}}
                                 ; iso = λ (A , B) → record { isoˡ = λ {(x , y) → refl}
                                                            ; isoʳ = λ {(x , y) → refl}}}
             ; hexagon₁ = λ {((x , y) , z) → refl}
             ; hexagon₂ = λ {(x , (y , z)) → refl}}

Pi+Symmetric : Symmetric Pi+Monoidal
Pi+Symmetric = record {
                 braided = Pi+Braided
               ; commutative = λ {(inj₁ x) → refl ; (inj₂ y) → refl}}

Pi×Symmetric : Symmetric Pi×Monoidal
Pi×Symmetric = record {
                 braided = Pi×Braided
               ; commutative = λ {(x , y) → refl}}

PiRig : RigCategory Pi Pi+Symmetric Pi×Symmetric
PiRig = record {
          annₗ = record { from = absorbr
                        ; to = factorzl
                        ; iso = record { isoˡ = λ () ; isoʳ = λ ()}}
        ; annᵣ = record { from = absorbl
                        ; to = factorzr
                        ; iso = record { isoˡ = λ () ; isoʳ = λ ()}}
        ; distribₗ = record { from = distl
                            ; to = factorl
                            ; iso = record { isoˡ = λ {(x , inj₁ y) → refl ; (x , inj₂ z) → refl}
                                           ; isoʳ = λ {(inj₁ (x , y)) → refl ; (inj₂ (x , z)) → refl}}}
        ; distribᵣ = record { from = dist
                            ; to = factor
                            ; iso = record { isoˡ = λ {(inj₁ x , z) → refl ; (inj₂ y , z) → refl}
                                           ; isoʳ = λ {(inj₁ (x , z)) → refl ; (inj₂ (y , z)) → refl}}}
        ; laplazaI = λ {(x , inj₁ y) → refl ; (x , inj₂ z) → refl}
        ; laplazaII = λ {(inj₁ x , z) → refl ; (inj₂ y , z) → refl}
        ; laplazaIV = λ {(inj₁ x , w) → refl ; (inj₂ (inj₁ y) , w) → refl ; (inj₂ (inj₂ z) , w) → refl}
        ; laplazaVI = λ {(x , (y , inj₁ z)) → refl ; (x , (y , inj₂ w)) → refl}
        ; laplazaIX = λ {(inj₁ x , inj₁ z) → refl ;
                         (inj₁ x , inj₂ w) → refl ;
                         (inj₂ y , inj₁ z) → refl ;
                         (inj₂ y , inj₂ w) → refl}
        ; laplazaX = λ ()
        ; laplazaXI = λ ()
        ; laplazaXIII = λ ()
        ; laplazaXV = λ ()
        ; laplazaXVI = λ ()
        ; laplazaXVII = λ ()
        ; laplazaXIX = λ {(x , inj₂ y) → refl}
        ; laplazaXXIII = λ {(tt , inj₁ x) → refl ; (tt , inj₂ y) → refl}}
