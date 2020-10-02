module PiFrac.Syntax where
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

infixr 12 _×ᵤ_
infixr 11 _+ᵤ_
infixr 50 _⨾_
infixr 10 _↔_
infixr 70 _⊕_
infixr 70 _⊗_
infix  99 !_
infix  99 𝟙/_

mutual
-- Types
  data 𝕌 : Set where
    𝟘    : 𝕌 
    𝟙    : 𝕌
    _+ᵤ_ : 𝕌 → 𝕌 → 𝕌
    _×ᵤ_ : 𝕌 → 𝕌 → 𝕌
    𝟙/_  : {t : 𝕌} → ⟦ t ⟧ → 𝕌

  data ◯ : Set where
    ↻ : ◯

  ⟦_⟧ : (A : 𝕌) → Set
  ⟦ 𝟘 ⟧ = ⊥
  ⟦ 𝟙 ⟧ = ⊤
  ⟦ t₁ +ᵤ t₂ ⟧ = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
  ⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧
  ⟦ 𝟙/ v ⟧ = ◯

-- Combinators
data _↔_ : 𝕌 → 𝕌 → Set where
  unite₊l  : {t : 𝕌} → 𝟘 +ᵤ t ↔ t
  uniti₊l  : {t : 𝕌} → t ↔ 𝟘 +ᵤ t
  swap₊    : {t₁ t₂ : 𝕌} → t₁ +ᵤ t₂ ↔ t₂ +ᵤ t₁
  assocl₊  : {t₁ t₂ t₃ : 𝕌} → t₁ +ᵤ (t₂ +ᵤ t₃) ↔ (t₁ +ᵤ t₂) +ᵤ t₃
  assocr₊  : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤ t₂) +ᵤ t₃ ↔ t₁ +ᵤ (t₂ +ᵤ t₃)
  unite⋆l  : {t : 𝕌} → 𝟙 ×ᵤ t ↔ t
  uniti⋆l  : {t : 𝕌} → t ↔ 𝟙 ×ᵤ t
  swap⋆    : {t₁ t₂ : 𝕌} → t₁ ×ᵤ t₂ ↔ t₂ ×ᵤ t₁
  assocl⋆  : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ ×ᵤ t₃) ↔ (t₁ ×ᵤ t₂) ×ᵤ t₃
  assocr⋆  : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₂) ×ᵤ t₃ ↔ t₁ ×ᵤ (t₂ ×ᵤ t₃)
  absorbr  : {t : 𝕌} → 𝟘 ×ᵤ t ↔ 𝟘
  factorzl : {t : 𝕌} → 𝟘 ↔ 𝟘 ×ᵤ t
  dist     : {t₁ t₂ t₃ : 𝕌} → (t₁ +ᵤ t₂) ×ᵤ t₃ ↔ (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃)
  factor   : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₃) +ᵤ (t₂ ×ᵤ t₃) ↔ (t₁ +ᵤ t₂) ×ᵤ t₃
  id↔      : {t : 𝕌} → t ↔ t
  _⨾_      : {t₁ t₂ t₃ : 𝕌} → (t₁ ↔ t₂) → (t₂ ↔ t₃) → (t₁ ↔ t₃)
  _⊕_      : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ↔ t₃) → (t₂ ↔ t₄) → (t₁ +ᵤ t₂ ↔ t₃ +ᵤ t₄)
  _⊗_      : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ↔ t₃) → (t₂ ↔ t₄) → (t₁ ×ᵤ t₂ ↔ t₃ ×ᵤ t₄)
  ηₓ       : {t : 𝕌} (v : ⟦ t ⟧) → 𝟙 ↔ t ×ᵤ 𝟙/ v
  εₓ       : {t : 𝕌} (v : ⟦ t ⟧) → t ×ᵤ 𝟙/ v ↔ 𝟙

-- Some useful combinators
unite⋆r  : {t : 𝕌} → t ×ᵤ 𝟙 ↔ t
unite⋆r  = swap⋆ ⨾ unite⋆l

uniti⋆r  : {t : 𝕌} → t ↔ t ×ᵤ 𝟙
uniti⋆r  = uniti⋆l ⨾ swap⋆

distl    : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ +ᵤ t₃) ↔ (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃)
distl    = swap⋆ ⨾ dist ⨾ (swap⋆ ⊕ swap⋆)

factorl  : {t₁ t₂ t₃ : 𝕌 } → (t₁ ×ᵤ t₂) +ᵤ (t₁ ×ᵤ t₃) ↔ t₁ ×ᵤ (t₂ +ᵤ t₃)
factorl  = (swap⋆ ⊕ swap⋆) ⨾ factor ⨾ swap⋆

-- Inverses of combinators
!_ : {A B : 𝕌} → A ↔ B → B ↔ A
! unite₊l = uniti₊l
! uniti₊l = unite₊l
! swap₊ = swap₊
! assocl₊ = assocr₊
! assocr₊ = assocl₊
! unite⋆l = uniti⋆l
! uniti⋆l = unite⋆l
! swap⋆ = swap⋆
! assocl⋆ = assocr⋆
! assocr⋆ = assocl⋆
! absorbr = factorzl
! factorzl = absorbr
! dist = factor
! factor = dist
! id↔ = id↔
! (c₁ ⨾ c₂) = ! c₂ ⨾ ! c₁
! (c₁ ⊕ c₂) = (! c₁) ⊕ (! c₂)
! (c₁ ⊗ c₂) = (! c₁) ⊗ (! c₂)
! (ηₓ v) = εₓ v
! (εₓ v) = ηₓ v
