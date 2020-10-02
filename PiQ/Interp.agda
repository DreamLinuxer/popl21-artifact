module PiQ.Interp where
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Sum
open import Data.Product
open import Data.Maybe
open import Data.Nat hiding (_≟_)
open import Data.List as L hiding (_∷_)
open import Relation.Binary.Core
open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_)
open import PiQ.Syntax
open import PiQ.Opsem
open import PiQ.Eval

{-# TERMINATING #-}
mutual
  interp : {A B : 𝕌} → (A ↔ B) → Val A B → Maybe (Val B A)
  -- Forward
  interp unite₊l (inj₂ y ⃗)        = just (y ⃗)
  interp uniti₊l (v ⃗)             = just (inj₂ v ⃗)
  interp swap₊   (inj₁ x ⃗)        = just (inj₂ x ⃗)
  interp swap₊   (inj₂ y ⃗)        = just (inj₁ y ⃗)
  interp assocl₊ (inj₁ x ⃗)        = just (inj₁ (inj₁ x) ⃗)
  interp assocl₊ (inj₂ (inj₁ y) ⃗) = just (inj₁ (inj₂ y) ⃗)
  interp assocl₊ (inj₂ (inj₂ z) ⃗) = just (inj₂ z ⃗)
  interp assocr₊ (inj₁ (inj₁ x) ⃗) = just (inj₁ x ⃗)
  interp assocr₊ (inj₁ (inj₂ y) ⃗) = just (inj₂ (inj₁ y) ⃗)
  interp assocr₊ (inj₂ z ⃗)        = just (inj₂ (inj₂ z) ⃗)
  interp unite⋆l ((tt , v) ⃗)      = just (v ⃗)
  interp uniti⋆l (v ⃗)             = just ((tt , v) ⃗)
  interp swap⋆   ((x , y) ⃗)       = just ((y , x) ⃗)
  interp assocl⋆ ((x , (y , z)) ⃗) = just (((x , y) , z) ⃗)
  interp assocr⋆ (((x , y) , z) ⃗) = just ((x , y , z) ⃗)
  interp dist    ((inj₁ x , z) ⃗)  = just (inj₁ (x , z) ⃗)
  interp dist    ((inj₂ y , z) ⃗)  = just (inj₂ (y , z) ⃗)
  interp factor  (inj₁ (x , z) ⃗)  = just ((inj₁ x , z) ⃗)
  interp factor  (inj₂ (y , z) ⃗)  = just ((inj₂ y , z) ⃗)
  interp id↔     (v ⃗)             = just (v ⃗)
  interp (c₁ ⨾ c₂) (v ⃗) = interp c₁ (v ⃗) >>=
                           λ {(v' ⃖) → just (v' ⃖) ;
                              (v' ⃗) → c₁ ⨾[ v' ⃗]⨾ c₂}
  interp (c₁ ⊕ c₂) (inj₁ x ⃗) = interp c₁ (x ⃗) >>=
                                λ {(x' ⃗) → just (inj₁ x' ⃗) ;
                                  (x' ⃖) → just (inj₁ x' ⃖)}
  interp (c₁ ⊕ c₂) (inj₂ y ⃗) = interp c₂ (y ⃗) >>=
                                λ {(y' ⃗) → just (inj₂ y' ⃗) ;
                                  (y' ⃖) → just (inj₂ y' ⃖)}
  interp (c₁ ⊗ c₂) ((x , y) ⃗) = interp c₁ (x ⃗) >>=
                                 λ {(x' ⃖) → just ((x' , y) ⃖) ;
                                   (x' ⃗) → interp c₂ (y ⃗) >>=
                                            λ {(y' ⃗) → just ((x' , y') ⃗) ;
                                               (y' ⃖) → just ((x , y') ⃖)}}
  interp ε₊      (inj₁ v ⃗)     = just (inj₂ (- v) ⃖)
  interp ε₊      (inj₂ (- v) ⃗) = just (inj₁ v ⃖)
  interp (ηₓ v)  (tt ⃗)         = just ((v , ↻) ⃗)
  interp (εₓ v)  ((v' , ↻) ⃗) with v ≟ v'
  ... | yes _ = just (tt ⃗)
  ... | no  _ = nothing
  -- Backward
  interp unite₊l (v ⃖)             = just (inj₂ v ⃖)
  interp uniti₊l (inj₂ v ⃖)        = just (v ⃖)
  interp swap₊   (inj₁ x ⃖)        = just (inj₂ x ⃖)
  interp swap₊   (inj₂ y ⃖)        = just (inj₁ y ⃖)
  interp assocl₊ (inj₁ (inj₁ x) ⃖) = just (inj₁ x ⃖)
  interp assocl₊ (inj₁ (inj₂ y) ⃖) = just (inj₂ (inj₁ y) ⃖)
  interp assocl₊ (inj₂ z ⃖)        = just (inj₂ (inj₂ z) ⃖)
  interp assocr₊ (inj₁ x ⃖)        = just (inj₁ (inj₁ x) ⃖)
  interp assocr₊ (inj₂ (inj₁ y) ⃖) = just (inj₁ (inj₂ y) ⃖)
  interp assocr₊ (inj₂ (inj₂ z) ⃖) = just (inj₂ z ⃖)
  interp unite⋆l (v ⃖)             = just ((tt , v) ⃖)
  interp uniti⋆l ((tt , v) ⃖)      = just (v ⃖)
  interp swap⋆   ((x , y) ⃖)       = just ((y , x) ⃖)
  interp assocl⋆ (((x , y) , z) ⃖) = just ((x , (y , z)) ⃖)
  interp assocr⋆ ((x , (y , z)) ⃖) = just (((x , y) , z) ⃖)
  interp dist    (inj₁ (x , z) ⃖)  = just ((inj₁ x , z) ⃖)
  interp dist    (inj₂ (y , z) ⃖)  = just ((inj₂ y , z) ⃖)
  interp factor  ((inj₁ x , z) ⃖)  = just (inj₁ (x , z) ⃖)
  interp factor  ((inj₂ y , z) ⃖)  = just (inj₂ (y , z) ⃖)
  interp id↔ (v ⃖) = just (v ⃖)
  interp (c₁ ⨾ c₂) (v ⃖) = interp c₂ (v ⃖) >>=
                           λ {(v' ⃗) → just (v' ⃗) ;
                              (v' ⃖) → c₁ ⨾[ v' ⃖]⨾ c₂}
  interp (c₁ ⊕ c₂) (inj₁ x ⃖) = interp c₁ (x ⃖) >>=
                                λ {(x' ⃖) → just (inj₁ x' ⃖) ;
                                  (x' ⃗) → just (inj₁ x' ⃗)}
  interp (c₁ ⊕ c₂) (inj₂ y ⃖) = interp c₂ (y ⃖) >>=
                                λ {(y' ⃖) → just (inj₂ y' ⃖) ;
                                  (y' ⃗) → just (inj₂ y' ⃗)}
  interp (c₁ ⊗ c₂) ((x , y) ⃖) = interp c₂ (y ⃖) >>=
                                 λ {(y' ⃗) → just ((x , y') ⃗) ;
                                    (y' ⃖) → interp c₁ (x ⃖) >>=
                                            λ {(x' ⃖) → just ((x' , y') ⃖) ;
                                               (x' ⃗) → just ((x' , y) ⃗)}}
  interp η₊     (inj₁ v ⃖)     = just (inj₂ (- v) ⃗)
  interp η₊     (inj₂ (- v) ⃖) = just (inj₁ v ⃗)
  interp (εₓ v) (tt ⃖)         = just ((v , ↻) ⃖)
  interp (ηₓ v) ((v' , ↻) ⃖) with v ≟ v'
  ... | yes _ = just (tt ⃖)
  ... | no  _ = nothing

  _⨾[_⃗]⨾_ : ∀ {A B C} → (A ↔ B) → ⟦ B ⟧ → (B ↔ C) → Maybe (Val C A)
  c₁ ⨾[ b ⃗]⨾ c₂ = interp c₂ (b ⃗) >>=
                   λ {(c ⃗)  → just (c ⃗) ;
                      (b' ⃖) → c₁ ⨾[ b' ⃖]⨾ c₂}

  _⨾[_⃖]⨾_ : ∀ {A B C} → (A ↔ B) → ⟦ B ⟧ → (B ↔ C) → Maybe (Val C A)
  c₁ ⨾[ b ⃖]⨾ c₂ = interp c₁ (b ⃖) >>=
                   λ {(a  ⃖) → just (a ⃖) ;
                      (b' ⃗) → c₁ ⨾[ b' ⃗]⨾ c₂}
