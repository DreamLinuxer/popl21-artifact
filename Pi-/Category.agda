module Pi-.Category where
open import Relation.Binary.PropositionalEquality
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Braided
open import Categories.Category.Monoidal.Symmetric
open import Categories.Category.Monoidal.Rigid
open import Categories.Category.Monoidal.CompactClosed
open import Categories.Functor.Bifunctor
open import Categories.Category
open import Categories.Category.Inverse
open import Categories.Category.Product
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Relation.Nullary
open import Base
open import Pi-.Syntax
open import Pi-.Opsem
open import Pi-.Eval
open import Pi-.NoRepeat
open import Pi-.Interp
open import Pi-.Properties
open import Pi-.Invariants
open import Pi-.Examples

Pi- : Category _ _ _ 
Pi- = record {
      Obj = 𝕌
    ; _⇒_ = _↔_
    ; _≈_ = λ c₁ c₂ → eval c₁ ∼ eval c₂
    ; id = id↔
    ; _∘_ = λ f g → g ⨾ f

    ; assoc = assoc
    ; sym-assoc = λ x → sym (assoc x)
    ; identityˡ = identityˡ _
    ; identityʳ = identityʳ _
    ; identity² = λ {(v ⃗) → refl ; (v ⃖) → refl}
    ; equiv = record { refl = λ a → refl
                     ; sym = λ f~g a → sym (f~g a)
                     ; trans = λ f~g g~h a → trans (f~g a) (g~h a) } 
    ; ∘-resp-≈ = ∘-resp-≈
    }
  where
  identityˡ : ∀ {A B} (c : A ↔ B) (v : Val A B) → eval (c ⨾ id↔) v ≡ eval c v
  identityˡ c v rewrite eval≡interp (c ⨾ id↔) v | eval≡interp c v = lem c v
    where
    lem : ∀ {A B} (c : A ↔ B) (v : Val A B) → interp (c ⨾ id↔) v ≡ interp c v
    lem c (x ⃗) with interp c (x ⃗)
    ... | x₁ ⃗ = refl
    ... | x₁ ⃖ = refl
    lem c (x ⃖) with interp c (x ⃖)
    ... | x₁ ⃗ = refl
    ... | x₁ ⃖ = refl

  identityʳ : ∀ {A B} (c : A ↔ B) (v : Val A B) → eval (id↔ ⨾ c) v ≡ eval c v
  identityʳ c v rewrite eval≡interp (id↔ ⨾ c) v | eval≡interp c v = lem c v
    where
    lem : ∀ {A B} (c : A ↔ B) (v : Val A B) → interp (id↔ ⨾ c) v ≡ interp c v
    lem c (x ⃗) with interp c (x ⃗)
    ... | x₁ ⃗ = refl
    ... | x₁ ⃖ = refl
    lem c (x ⃖) with interp c (x ⃖)
    ... | x₁ ⃗ = refl
    ... | x₁ ⃖ = refl

Pi-Monoidal : Monoidal Pi-
Pi-Monoidal = record {
              ⊗ = record { F₀ = λ {(A , B) → A +ᵤ B}
                         ; F₁ = λ {(c₁ , c₂) → c₁ ⊕ c₂ }
                         ; identity = λ { (inj₁ v ⃗) → refl
                                        ; (inj₂ v ⃗) → refl
                                        ; (inj₁ v ⃖) → refl
                                        ; (inj₂ v ⃖) → refl}
                         ; homomorphism = homomorphism
                         ; F-resp-≈ = λ {(A , B)} {(C , D)} {(f , g)} {(f' , g')} (f~f' , g~g')
                                        → F-resp-≈ f f' g g' f~f' g~g'}
            ; unit = 𝟘
            ; unitorˡ = record { from = unite₊l
                               ; to = uniti₊l
                               ; iso = record { isoˡ = λ { (inj₂ v ⃗) → refl
                                                         ; (inj₂ v ⃖) → refl}
                                              ; isoʳ = λ { (v ⃗) → refl
                                                         ; (v ⃖) → refl}}}
            ; unitorʳ = record { from = unite₊r
                               ; to = uniti₊r
                               ; iso = record { isoˡ = λ { (inj₁ v ⃗) → refl
                                                         ; (inj₁ v ⃖) → refl}
                                              ; isoʳ = λ { (v ⃗) → refl
                                                         ; (v ⃖) → refl}}}
            ; associator = record { from = assocr₊
                                  ; to = assocl₊
                                  ; iso = record { isoˡ = λ { (inj₁ (inj₁ v) ⃗) → refl
                                                            ; (inj₁ (inj₂ v) ⃗) → refl
                                                            ; (inj₂ v ⃗) → refl
                                                            ; (inj₁ (inj₁ v) ⃖) → refl
                                                            ; (inj₁ (inj₂ v) ⃖) → refl
                                                            ; (inj₂ v ⃖) → refl}
                                                 ; isoʳ = λ { (inj₁ v ⃗) → refl
                                                            ; (inj₂ (inj₁ v) ⃗) → refl
                                                            ; (inj₂ (inj₂ v) ⃗) → refl
                                                            ; (inj₁ v ⃖) → refl
                                                            ; (inj₂ (inj₁ v) ⃖) → refl
                                                            ; (inj₂ (inj₂ v) ⃖) → refl}}}
            ; unitorˡ-commute-from = unitorˡ-commute-from _
            ; unitorˡ-commute-to = unitorˡ-commute-to _
            ; unitorʳ-commute-from = unitorʳ-commute-from _
            ; unitorʳ-commute-to = unitorʳ-commute-to _
            ; assoc-commute-from = assoc-commute-from _ _ _
            ; assoc-commute-to = assoc-commute-to _ _ _
            ; triangle = λ { (inj₁ (inj₁ v) ⃗) → refl
                           ; (inj₂ v ⃗) → refl
                           ; (inj₁ v ⃖) → refl
                           ; (inj₂ v ⃖) → refl}
            ; pentagon = λ { (inj₁ (inj₁ (inj₁ v)) ⃗) → refl
                           ; (inj₁ (inj₁ (inj₂ v)) ⃗) → refl
                           ; (inj₁ (inj₂ v) ⃗) → refl
                           ; (inj₂ v ⃗) → refl
                           ; (inj₁ v ⃖) → refl
                           ; (inj₂ (inj₁ v) ⃖) → refl
                           ; (inj₂ (inj₂ (inj₁ v)) ⃖) → refl
                           ; (inj₂ (inj₂ (inj₂ v)) ⃖) → refl}
            }
  where
  F-resp-≈ : ∀ {A B C D} (f f' : A ↔ B) (g g' : C ↔ D) → (eval f ∼ eval f') → (eval g ∼ eval g')
           → (eval (f ⊕ g) ∼ eval (f' ⊕ g'))
  F-resp-≈ f f' g g' f~f' g~g' x rewrite eval≡interp (f ⊕ g) x | eval≡interp (f' ⊕ g') x =
    lem f f' g g' (λ x → trans (sym (eval≡interp f x)) (trans (f~f' x) (eval≡interp f' x)))
                  (λ x → trans (sym (eval≡interp g x)) (trans (g~g' x) (eval≡interp g' x))) x
    where
    lem : ∀ {A B C D} (f f' : A ↔ B) (g g' : C ↔ D) → (interp f ∼ interp f') → (interp g ∼ interp g')
        → (interp (f ⊕ g) ∼ interp (f' ⊕ g'))
    lem f f' g g' f~f' g~g' (inj₁ x ⃗) with f~f' (x ⃗) | interp f' (x ⃗) | inspect (interp f') (x ⃗)
    ... | eq | x' ⃗ | [ eq' ] rewrite eq | eq' = refl
    ... | eq | x' ⃖ | [ eq' ] rewrite eq | eq' = refl
    lem f f' g g' f~f' g~g' (inj₂ y ⃗) with g~g' (y ⃗) | interp g' (y ⃗) | inspect (interp g') (y ⃗)
    ... | eq | y' ⃗ | [ eq' ] rewrite eq | eq' = refl
    ... | eq | y' ⃖ | [ eq' ] rewrite eq | eq' = refl
    lem f f' g g' f~f' g~g' (inj₁ x ⃖) with f~f' (x ⃖) | interp f' (x ⃖) | inspect (interp f') (x ⃖)
    ... | eq | x' ⃗ | [ eq' ] rewrite eq | eq' = refl
    ... | eq | x' ⃖ | [ eq' ] rewrite eq | eq' = refl
    lem f f' g g' f~f' g~g' (inj₂ y ⃖) with g~g' (y ⃖) | interp g' (y ⃖) | inspect (interp g') (y ⃖)
    ... | eq | y' ⃗ | [ eq' ] rewrite eq | eq' = refl
    ... | eq | y' ⃖ | [ eq' ] rewrite eq | eq' = refl
           
  unitorˡ-commute-from : ∀ {A B} (f : A ↔ B) (x : _) → eval ((id↔ ⊕ f) ⨾ unite₊l) x ≡ eval (unite₊l ⨾ f) x
  unitorˡ-commute-from f x rewrite eval≡interp ((id↔ ⊕ f) ⨾ unite₊l) x | eval≡interp (unite₊l ⨾ f) x = lem f x
    where
    lem : ∀ {A B} (f : A ↔ B) (x : _) → interp ((id↔ ⊕ f) ⨾ unite₊l) x ≡ interp (unite₊l ⨾ f) x
    lem f (inj₂ y ⃗) with interp f (y ⃗)
    ... | x ⃗ = refl
    ... | x ⃖ = refl
    lem f (x ⃖) with interp f (x ⃖)
    ... | x₁ ⃗ = refl
    ... | x₁ ⃖ = refl

  unitorˡ-commute-to : ∀ {A B} (f : A ↔ B) (x : _) → eval (f ⨾ uniti₊l) x ≡ eval (uniti₊l ⨾ (id↔ ⊕ f)) x
  unitorˡ-commute-to f x rewrite eval≡interp (f ⨾ uniti₊l) x | eval≡interp (uniti₊l ⨾ (id↔ ⊕ f)) x = lem f x
    where
    lem : ∀ {A B} (f : A ↔ B) (x : _) → interp (f ⨾ uniti₊l) x ≡ interp (uniti₊l ⨾ (id↔ ⊕ f)) x
    lem f (x ⃗) with interp f (x ⃗)
    ... | x₁ ⃗ = refl
    ... | x₁ ⃖ = refl
    lem f (inj₂ y ⃖) with interp f (y ⃖)
    ... | x ⃗ = refl
    ... | x ⃖ = refl

  unitorʳ-commute-from : ∀ {A B} (f : A ↔ B) (x : _) → eval ((f ⊕ id↔) ⨾ swap₊ ⨾ unite₊l) x ≡ eval ((swap₊ ⨾ unite₊l) ⨾ f) x
  unitorʳ-commute-from f x rewrite eval≡interp ((f ⊕ id↔) ⨾ swap₊ ⨾ unite₊l) x | eval≡interp ((swap₊ ⨾ unite₊l) ⨾ f) x = lem f x
    where
    lem : ∀ {A B} (f : A ↔ B) (x : _) → interp ((f ⊕ id↔) ⨾ swap₊ ⨾ unite₊l) x ≡ interp ((swap₊ ⨾ unite₊l) ⨾ f) x
    lem f (inj₁ x ⃗) with interp f (x ⃗)
    ... | x₁ ⃗ = refl
    ... | x₁ ⃖ = refl
    lem f (x ⃖) with interp f (x ⃖)
    ... | x₁ ⃗ = refl
    ... | x₁ ⃖ = refl
    
  unitorʳ-commute-to : ∀ {A B} (f : A ↔ B) (x : _) → eval (f ⨾ uniti₊l ⨾ swap₊) x ≡ eval ((uniti₊l ⨾ swap₊) ⨾ (f ⊕ id↔)) x
  unitorʳ-commute-to f x rewrite eval≡interp (f ⨾ uniti₊l ⨾ swap₊) x | eval≡interp ((uniti₊l ⨾ swap₊) ⨾ (f ⊕ id↔)) x = lem f x
    where
    lem : ∀ {A B} (f : A ↔ B) (x : _) → interp (f ⨾ uniti₊l ⨾ swap₊) x ≡ interp ((uniti₊l ⨾ swap₊) ⨾ (f ⊕ id↔)) x
    lem f (x ⃗) with interp f (x ⃗)
    ... | x₁ ⃗ = refl
    ... | x₁ ⃖ = refl
    lem f (inj₁ x ⃖) with interp f (x ⃖)
    ... | x₁ ⃗ = refl
    ... | x₁ ⃖ = refl
    
  assoc-commute-from : ∀ {A B C D E F} (f : A ↔ B) (g : C ↔ D) (h : E ↔ F) (x : _) → eval (((f ⊕ g) ⊕ h) ⨾ assocr₊) x ≡ eval (assocr₊ ⨾ (f ⊕ (g ⊕ h))) x
  assoc-commute-from f g h x rewrite eval≡interp (((f ⊕ g) ⊕ h) ⨾ assocr₊) x | eval≡interp (assocr₊ ⨾ (f ⊕ (g ⊕ h))) x = lem f g h x
    where
    lem : ∀ {A B C D E F} (f : A ↔ B) (g : C ↔ D) (h : E ↔ F) (x : _) → interp (((f ⊕ g) ⊕ h) ⨾ assocr₊) x ≡ interp (assocr₊ ⨾ (f ⊕ (g ⊕ h))) x
    lem f g h (inj₁ (inj₁ x) ⃗) with interp f (x ⃗)
    ... | x' ⃗ = refl
    ... | x' ⃖ = refl
    lem f g h (inj₁ (inj₂ y) ⃗) with interp g (y ⃗)
    ... | y' ⃗ = refl
    ... | y' ⃖ = refl
    lem f g h (inj₂ z ⃗) with interp h (z ⃗)
    ... | z' ⃗ = refl
    ... | z' ⃖ = refl
    lem f g h (inj₁ x ⃖) with interp f (x ⃖)
    ... | x' ⃗ = refl
    ... | x' ⃖ = refl
    lem f g h (inj₂ (inj₁ y) ⃖) with interp g (y ⃖)
    ... | y' ⃗ = refl
    ... | y' ⃖ = refl
    lem f g h (inj₂ (inj₂ z) ⃖) with interp h (z ⃖)
    ... | z' ⃗ = refl
    ... | z' ⃖ = refl
    
  assoc-commute-to : ∀ {A B C D E F} (f : A ↔ B) (g : C ↔ D) (h : E ↔ F) (x : _) → eval ((f ⊕ (g ⊕ h)) ⨾ assocl₊) x ≡ eval (assocl₊ ⨾ ((f ⊕ g) ⊕ h)) x
  assoc-commute-to f g h x rewrite eval≡interp ((f ⊕ (g ⊕ h)) ⨾ assocl₊) x | eval≡interp (assocl₊ ⨾ ((f ⊕ g) ⊕ h)) x = lem f g h x
    where
    lem : ∀ {A B C D E F} (f : A ↔ B) (g : C ↔ D) (h : E ↔ F) (x : _) → interp ((f ⊕ (g ⊕ h)) ⨾ assocl₊) x ≡ interp (assocl₊ ⨾ ((f ⊕ g) ⊕ h)) x
    lem f g h (inj₁ x ⃗) with interp f (x ⃗)
    ... | x' ⃗ = refl
    ... | x' ⃖ = refl
    lem f g h (inj₂ (inj₁ y) ⃗) with interp g (y ⃗)
    ... | y' ⃗ = refl
    ... | y' ⃖ = refl
    lem f g h (inj₂ (inj₂ z) ⃗) with interp h (z ⃗)
    ... | z' ⃗ = refl
    ... | z' ⃖ = refl
    lem f g h (inj₁ (inj₁ x) ⃖) with interp f (x ⃖)
    ... | x' ⃗ = refl
    ... | x' ⃖ = refl
    lem f g h (inj₁ (inj₂ y) ⃖) with interp g (y ⃖)
    ... | y' ⃗ = refl
    ... | y' ⃖ = refl
    lem f g h (inj₂ z ⃖) with interp h (z ⃖)
    ... | z' ⃗ = refl
    ... | z' ⃖ = refl
    
Pi-Braided : Braided Pi-Monoidal
Pi-Braided = record { braiding = record { F⇒G = record { η = λ _ → swap₊
                                                       ; commute = λ {(f , g) x → commute f g x}
                                                       ; sym-commute = λ {(f , g) x → sym (commute f g x)}}
                                        ; F⇐G = record { η = λ _ → swap₊
                                                       ; commute = λ { (f , g) x → commute g f x}
                                                       ; sym-commute = λ {(f , g) x → sym (commute g f x)}}
                                        ; iso = λ _ → record { isoˡ = λ { (inj₁ v ⃗) → refl
                                                                        ; (inj₂ v ⃗) → refl
                                                                        ; (inj₁ v ⃖) → refl
                                                                        ; (inj₂ v ⃖) → refl}
                                                             ; isoʳ = λ { (inj₁ v ⃗) → refl
                                                                        ; (inj₂ v ⃗) → refl
                                                                        ; (inj₁ v ⃖) → refl
                                                                        ; (inj₂ v ⃖) → refl} } }
                    ; hexagon₁ = λ { (inj₁ (inj₁ v) ⃗) → refl
                                   ; (inj₁ (inj₂ v) ⃗) → refl
                                   ; (inj₂ v ⃗) → refl
                                   ; (inj₁ v ⃖) → refl
                                   ; (inj₂ (inj₁ v) ⃖) → refl
                                   ; (inj₂ (inj₂ v) ⃖) → refl}
                    ; hexagon₂ = λ { (inj₁ (inj₁ v) ⃖) → refl
                                   ; (inj₁ (inj₂ v) ⃖) → refl
                                   ; (inj₂ v ⃖) → refl
                                   ; (inj₁ v ⃗) → refl
                                   ; (inj₂ (inj₁ v) ⃗) → refl
                                   ; (inj₂ (inj₂ v) ⃗) → refl}}
  where
  commute : ∀ {A B C D} (f : A ↔ C) (g : B ↔ D) (x : _)
          → eval ((f ⊕ g) ⨾ swap₊) x ≡ eval (swap₊ ⨾ (g ⊕ f)) x
  commute f g x rewrite eval≡interp ((f ⊕ g) ⨾ swap₊) x | eval≡interp (swap₊ ⨾ (g ⊕ f)) x = lem f g x
    where
    lem : ∀ {A B C D} (f : A ↔ C) (g : B ↔ D) (x : _)
        → interp ((f ⊕ g) ⨾ swap₊) x ≡ interp (swap₊ ⨾ (g ⊕ f)) x
    lem f g (inj₁ x ⃗) with interp f (x ⃗)
    ... | _ ⃗ = refl
    ... | _ ⃖ = refl
    lem f g (inj₂ y ⃗) with interp g (y ⃗)
    ... | _ ⃗ = refl
    ... | _ ⃖ = refl
    lem f g (inj₁ y ⃖) with interp g (y ⃖)
    ... | _ ⃗ = refl
    ... | _ ⃖ = refl
    lem f g (inj₂ x ⃖) with interp f (x ⃖)
    ... | _ ⃗ = refl
    ... | _ ⃖ = refl

Pi-Symmetric : Symmetric Pi-Monoidal
Pi-Symmetric = record { braided = Pi-Braided
                      ; commutative = λ { (inj₁ v ⃗) → refl
                                        ; (inj₂ v ⃗) → refl
                                        ; (inj₁ v ⃖) → refl
                                        ; (inj₂ v ⃖) → refl}}

Pi-Rigid : LeftRigid Pi-Monoidal
Pi-Rigid = record { _⁻¹ = -_
                  ; η = η₊
                  ; ε = swap₊ ⨾ ε₊
                  ; snake₁ = λ { (v ⃗) → refl
                               ; (v ⃖) → refl}
                  ; snake₂ = λ { ((- v) ⃗) → refl
                               ; ((- v) ⃖) → refl}}

Pi-CompactClosed : CompactClosed Pi-Monoidal
Pi-CompactClosed = record { symmetric = Pi-Symmetric
                          ; rigid     = inj₁ Pi-Rigid}

¬Pi-Inverse : ¬(Inverse Pi-)
¬Pi-Inverse record { _⁻¹ = _⁻¹ } with (ε₊ {𝟙} ⊕ id↔ {𝟙}) ⁻¹
... | c , (_ , _) , uniq = contr
  where
  c₁ c₂ : 𝟘 +ᵤ 𝟙 ↔ (𝟙 +ᵤ - 𝟙) +ᵤ 𝟙
  c₁ = η₊ ⊕ id↔
  c₂ = (η₊ ⊕ id↔) ⨾ swap₊ ⨾ (id↔ ⊕ swap₊) ⨾ assocl₊
  
  c₁pinv : (eval (((ε₊ {𝟙} ⊕ id↔) ⨾ c₁) ⨾ (ε₊ ⊕ id↔)) ∼ eval (ε₊ ⊕ id↔))
         × (eval ((c₁ ⨾ (ε₊ ⊕ id↔)) ⨾ c₁) ∼ eval c₁)
  c₁pinv = p₁ , p₂
    where
    p₁ : eval (((ε₊ {𝟙} ⊕ id↔) ⨾ c₁) ⨾ (ε₊ ⊕ id↔)) ∼ eval (ε₊ ⊕ id↔)
    p₁ (inj₁ (inj₁ tt) ⃗) = refl
    p₁ (inj₁ (inj₂ (- tt)) ⃗) = refl
    p₁ (inj₂ tt ⃗) = refl
    p₁ (inj₂ tt ⃖) = refl

    p₂ : eval ((c₁ ⨾ (ε₊ ⊕ id↔)) ⨾ c₁) ∼ eval c₁
    p₂ (inj₂ tt ⃗) = refl
    p₂ (inj₁ (inj₁ tt) ⃖) = refl
    p₂ (inj₁ (inj₂ (- tt)) ⃖) = refl
    p₂ (inj₂ tt ⃖) = refl

  c₂pinv : (eval (((ε₊ {𝟙} ⊕ id↔) ⨾ c₂) ⨾ (ε₊ ⊕ id↔)) ∼ eval (ε₊ ⊕ id↔))
         × (eval ((c₂ ⨾ (ε₊ ⊕ id↔)) ⨾ c₂) ∼ eval c₂)
  c₂pinv = p₁ , p₂
    where
    p₁ : eval (((ε₊ {𝟙} ⊕ id↔) ⨾ c₂) ⨾ (ε₊ ⊕ id↔)) ∼ eval (ε₊ ⊕ id↔)
    p₁ (inj₁ (inj₁ tt) ⃗) = refl
    p₁ (inj₁ (inj₂ (- tt)) ⃗) = refl
    p₁ (inj₂ tt ⃗) = refl
    p₁ (inj₂ tt ⃖) = refl

    p₂ : eval ((c₂ ⨾ (ε₊ ⊕ id↔)) ⨾ c₂) ∼ eval c₂
    p₂ (inj₂ tt ⃗) = refl
    p₂ (inj₁ (inj₁ tt) ⃖) = refl
    p₂ (inj₁ (inj₂ (- tt)) ⃖) = refl
    p₂ (inj₂ tt ⃖) = refl

  c∼c₁ : eval c ∼ eval c₁
  c∼c₁ = uniq c₁pinv

  c∼c₂ : eval c ∼ eval c₂
  c∼c₂ = uniq c₂pinv

  contr : ⊥
  contr with trans (sym (c∼c₁ (inj₂ _ ⃗))) (c∼c₂ (inj₂ _ ⃗))
  ... | ()

IHom : ∀ {A B C} → C ↔ (- A +ᵤ B) → (C +ᵤ A) ↔ B
IHom f = (f ⊕ id↔) ⨾ [A+B]+C=[A+C]+B ⨾ (swap₊ ⊕ id↔) ⨾ (ε₊ ⊕ id↔) ⨾ unite₊l

IHom' : ∀ {A B C} → C +ᵤ A ↔ B → C ↔ - A +ᵤ B
IHom' f = uniti₊l ⨾ (η₊ ⊕ id↔) ⨾ (swap₊ ⊕ id↔) ⨾ (assocr₊ ⨾ id↔ ⊕ swap₊) ⨾ id↔ ⊕ f

IHom'∘IHom : ∀ {A B C} → (f : C ↔ (- A +ᵤ B)) → interp f ∼ interp (IHom' (IHom f))
IHom'∘IHom f (c ⃗) with interp f (c ⃗)
IHom'∘IHom f (c ⃗) | inj₁ (- a) ⃗ = refl
IHom'∘IHom f (c ⃗) | inj₂ b ⃗ = refl
IHom'∘IHom f (c ⃗) | (c' ⃖) = refl
IHom'∘IHom f (inj₁ (- a) ⃖) with interp f (inj₁ (- a) ⃖)
IHom'∘IHom f (inj₁ (- a) ⃖) | inj₁ (- a') ⃗ = refl
IHom'∘IHom f (inj₁ (- a) ⃖) | inj₂ b ⃗ = refl
IHom'∘IHom f (inj₁ (- a) ⃖) | c ⃖ = refl
IHom'∘IHom f (inj₂ b ⃖) with interp f (inj₂ b ⃖)
IHom'∘IHom f (inj₂ b ⃖) | inj₁ (- a) ⃗ = refl
IHom'∘IHom f (inj₂ b ⃖) | inj₂ b' ⃗ = refl
IHom'∘IHom f (inj₂ b ⃖) | c ⃖ = refl

IHom∘IHom' : ∀ {A B C} → (f : (C +ᵤ A) ↔ B) → interp f ∼ interp (IHom (IHom' f))
IHom∘IHom' f (inj₁ c ⃗) with interp f (inj₁ c ⃗)
IHom∘IHom' f (inj₁ c ⃗) | b ⃗ = refl
IHom∘IHom' f (inj₁ c ⃗) | inj₁ c' ⃖ = refl
IHom∘IHom' f (inj₁ c ⃗) | inj₂ a ⃖ = refl
IHom∘IHom' f (inj₂ a ⃗) with interp f (inj₂ a ⃗)
IHom∘IHom' f (inj₂ a ⃗) | b ⃗ = refl
IHom∘IHom' f (inj₂ a ⃗) | inj₁ c ⃖ = refl
IHom∘IHom' f (inj₂ a ⃗) | inj₂ a' ⃖ = refl
IHom∘IHom' f (b ⃖) with interp f (b ⃖)
IHom∘IHom' f (b ⃖) | b' ⃗ = refl
IHom∘IHom' f (b ⃖) | inj₁ c ⃖ = refl
IHom∘IHom' f (b ⃖) | inj₂ a ⃖ = refl

Ev : ∀ {A B} → (- A +ᵤ B) +ᵤ A ↔ B
Ev = [A+B]+C=[A+C]+B ⨾ ((swap₊ ⨾ ε₊) ⊕ id↔) ⨾ unite₊l

hof : ∀ {A B} → (𝟘 ↔ (- A +ᵤ B)) → (A ↔ B)
hof f = uniti₊l ⨾ (f ⊕ id↔) ⨾ [A+B]+C=[A+C]+B ⨾ (swap₊ ⨾ ε₊) ⊕ id↔ ⨾ unite₊l

hof' : ∀ {A B} → (A ↔ B) → (𝟘 ↔ (- A +ᵤ B))
hof' f = η₊ ⨾ (f ⊕ id↔) ⨾ swap₊

hof'∘hof : ∀ {A B} → (f : 𝟘 ↔ (- A +ᵤ B)) → interp f ∼ interp (hof' (hof f))
hof'∘hof f (inj₁ (- a) ⃖) with interp f (inj₁ (- a) ⃖)
hof'∘hof f (inj₁ (- a) ⃖) | inj₁ (- a') ⃗ = refl
hof'∘hof f (inj₁ (- a) ⃖) | inj₂ b ⃗ = refl
hof'∘hof f (inj₂ b ⃖) with interp f (inj₂ b ⃖)
hof'∘hof f (inj₂ b ⃖) | inj₁ (- a) ⃗ = refl
hof'∘hof f (inj₂ b ⃖) | inj₂ b' ⃗ = refl

hof∘hof' : ∀ {A B} → (f : A ↔ B) → interp f ∼ interp (hof (hof' f))
hof∘hof' f (a ⃗) with interp f (a ⃗)
hof∘hof' f (a ⃗) | b ⃗ = refl
hof∘hof' f (a ⃗) | a' ⃖ = refl
hof∘hof' f (b ⃖) with interp f (b ⃖)
hof∘hof' f (b ⃖) | b' ⃗ = refl
hof∘hof' f (b ⃖) | a ⃖ = refl
