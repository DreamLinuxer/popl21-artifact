module PiFrac.Properties where
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Sum
open import Data.Product
open import Relation.Binary.Core
open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Maybe
open import PiFrac.Syntax
open import PiFrac.Opsem
open import PiFrac.AuxLemmas
open import PiFrac.NoRepeat
open import PiFrac.Eval
open import PiFrac.Interp
open import PiFrac.Invariants

-- Forward evaluator is reversible
evalIsRev : ∀ {A B} → (c : A ↔ B) (v₁ : ⟦ A ⟧) (v₂ : ⟦ B ⟧)
          → eval c v₁ ≡ (just v₂) → evalᵣₑᵥ c v₂ ≡ (just v₁)
evalIsRev c v₁ v₂ eq with ev {κ = ☐} c v₁
evalIsRev c v₁ v₂ refl | inj₁ (v₂ , rs) with evᵣₑᵥ {κ = ☐} c v₂
... | inj₁ (v₁' , rs') with deterministicᵣₑᵥ* rs' (Rev↦ rs) (λ ()) (λ ()) (λ ())
... | refl = refl
evalIsRev c v₁ v₂ refl | inj₁ (v₂ , rs) | inj₂ (_ , v , _ , _ , neq , rs') with deterministicᵣₑᵥ* rs' (Rev↦ rs) (λ ()) (Lemma₆ neq) (λ ())
... | ()

-- Backward evaluator is reversible
evalᵣₑᵥIsRev : ∀ {A B} → (c : A ↔ B) (v₁ : ⟦ B ⟧) (v₂ : ⟦ A ⟧)
             → evalᵣₑᵥ c v₁ ≡ (just v₂) → eval c v₂ ≡ (just v₁)
evalᵣₑᵥIsRev c v₁ v₂ eq with evᵣₑᵥ {κ = ☐} c v₁
evalᵣₑᵥIsRev c v₁ v₂ refl | inj₁ (v₂ , rs) with ev {κ = ☐} c v₂
... | inj₁ (_ , rs') with deterministic* rs' (Rev↦ᵣₑᵥ rs) (λ ()) (λ ())
... | refl = refl
evalᵣₑᵥIsRev c v₁ v₂ refl | inj₁ (v₂ , rs) | inj₂ rs' with deterministic* rs' (Rev↦ᵣₑᵥ rs) (λ ()) (λ ())
... | ()

-- The abstract machine semantics is equivalent to the big-step semantics
eval≡interp : ∀ {A B} → (c : A ↔ B) → (v : ⟦ A ⟧) → eval c v ≡ interp c v
eval≡interp uniti₊l v = refl
eval≡interp unite₊l (inj₂ v) = refl
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
eval≡interp (c₁ ⨾ c₂) v | inj₁ (v' , rs) | [ eq ] with ev {κ = ☐} c₂ v' | inspect (ev {κ = ☐} c₂) v'
eval≡interp (c₁ ⨾ c₂) v | inj₁ (v' , rs) | [ eq ] | inj₁ (v'' , rs') | [ eq' ] with ev {κ = ☐} (c₁ ⨾ c₂) v | inspect (ev {κ = ☐} (c₁ ⨾ c₂)) v
eval≡interp (c₁ ⨾ c₂) v | inj₁ (v' , rs) | [ eq ] | inj₁ (v'' , rs') | [ eq' ] | inj₁ (u , rs'') | [ eq'' ] rewrite (sym (eval≡interp c₁ v)) | eq | (sym (eval≡interp c₂ v')) | eq' with deterministic* ((↦₃ ∷ ◾) ++↦ appendκ↦* rs (λ ()) (λ ()) refl (☐⨾ c₂ • ☐) ++↦ (↦₇ ∷ ◾) ++↦ appendκ↦* rs' (λ ()) (λ ()) refl (c₁ ⨾☐• ☐) ++↦ (↦₁₀ ∷ ◾)) rs'' (λ ()) (λ ())
... | refl = refl
eval≡interp (c₁ ⨾ c₂) v | inj₁ (v' , rs) | [ eq ] | inj₁ (v'' , rs') | [ eq' ] | inj₂ rs'' | [ eq'' ] rewrite (sym (eval≡interp c₁ v)) | eq | (sym (eval≡interp c₂ v')) | eq' with deterministic* ((↦₃ ∷ ◾) ++↦ appendκ↦* rs (λ ()) (λ ()) refl (☐⨾ c₂ • ☐) ++↦ (↦₇ ∷ ◾) ++↦ appendκ↦* rs' (λ ()) (λ ()) refl (c₁ ⨾☐• ☐) ++↦ (↦₁₀ ∷ ◾)) rs'' (λ ()) (λ ())
... | ()
eval≡interp (c₁ ⨾ c₂) v | inj₁ (v' , rs) | [ eq ] | inj₂ rs' | [ eq' ] with ev {κ = ☐} (c₁ ⨾ c₂) v | inspect (ev {κ = ☐} (c₁ ⨾ c₂)) v
eval≡interp (c₁ ⨾ c₂) v | inj₁ (v' , rs) | [ eq ] | inj₂ rs' | [ eq' ] | inj₁ (u , rs'') | [ eq'' ] rewrite (sym (eval≡interp c₁ v)) | eq | (sym (eval≡interp c₂ v')) | eq' with deterministic* ((↦₃ ∷ ◾) ++↦ appendκ↦* rs (λ ()) (λ ()) refl (☐⨾ c₂ • ☐) ++↦ (↦₇ ∷ ◾) ++↦ appendκ↦*⊠ rs' (λ ()) (c₁ ⨾☐• ☐)) rs'' (λ ()) (λ ())
... | ()
eval≡interp (c₁ ⨾ c₂) v | inj₁ (v' , rs) | [ eq ] | inj₂ rs' | [ eq' ] | inj₂ rs'' | [ eq'' ] rewrite (sym (eval≡interp c₁ v)) | eq | (sym (eval≡interp c₂ v')) | eq' = refl
eval≡interp (c₁ ⨾ c₂) v | inj₂ rs | [ eq ] with ev {κ = ☐} (c₁ ⨾ c₂) v | inspect (ev {κ = ☐} (c₁ ⨾ c₂)) v
eval≡interp (c₁ ⨾ c₂) v | inj₂ rs | [ eq ] | inj₁ (v'' , rs') | [ eq' ] with deterministic* ((↦₃ ∷ ◾) ++↦ appendκ↦*⊠ rs (λ ()) (☐⨾ c₂ • ☐)) rs' (λ ()) (λ ())
... | ()
eval≡interp (c₁ ⨾ c₂) v | inj₂ rs | [ eq ] | inj₂ rs' | [ eq' ] rewrite (sym (eval≡interp c₁ v)) | eq = refl
eval≡interp (c₁ ⊕ c₂) (inj₁ x) with ev {κ = ☐} c₁ x | inspect (ev {κ = ☐} c₁) x
eval≡interp (c₁ ⊕ c₂) (inj₁ x) | inj₁ (x' , rs) | [ eq ] with ev {κ = ☐} (c₁ ⊕ c₂) (inj₁ x) | inspect (ev {κ = ☐} (c₁ ⊕ c₂)) (inj₁ x)
eval≡interp (c₁ ⊕ c₂) (inj₁ x) | inj₁ (x' , rs) | [ eq ] | inj₁ (x'' , rs') | [ eq' ] rewrite (sym (eval≡interp c₁ x)) | eq with deterministic* ((↦₄ ∷ ◾) ++↦ appendκ↦* rs (λ ()) (λ ()) refl (☐⊕ c₂ • ☐) ++↦ (↦₁₁ ∷ ◾)) rs' (λ ()) (λ ())
... | refl = refl
eval≡interp (c₁ ⊕ c₂) (inj₁ x) | inj₁ (x' , rs) | [ eq ] | inj₂ rs' | [ eq' ] rewrite (sym (eval≡interp c₁ x)) | eq with deterministic* ((↦₄ ∷ ◾) ++↦ appendκ↦* rs (λ ()) (λ ()) refl (☐⊕ c₂ • ☐) ++↦ (↦₁₁ ∷ ◾)) rs' (λ ()) (λ ())
... | ()
eval≡interp (c₁ ⊕ c₂) (inj₁ x) | inj₂ rs | [ eq ] with ev {κ = ☐} (c₁ ⊕ c₂) (inj₁ x) | inspect (ev {κ = ☐} (c₁ ⊕ c₂)) (inj₁ x)
eval≡interp (c₁ ⊕ c₂) (inj₁ x) | inj₂ rs | [ eq ] | inj₁ (x'' , rs') | [ eq' ] rewrite (sym (eval≡interp c₁ x)) | eq with deterministic* ((↦₄ ∷ ◾) ++↦ appendκ↦*⊠ rs (λ ()) (☐⊕ c₂ • ☐)) rs' (λ ()) (λ ())
... | ()
eval≡interp (c₁ ⊕ c₂) (inj₁ x) | inj₂ rs | [ eq ] | inj₂ rs' | [ eq' ] rewrite (sym (eval≡interp c₁ x)) | eq = refl
eval≡interp (c₁ ⊕ c₂) (inj₂ y) with ev {κ = ☐} c₂ y | inspect (ev {κ = ☐} c₂) y
eval≡interp (c₁ ⊕ c₂) (inj₂ y) | inj₁ (y' , rs) | [ eq ] with ev {κ = ☐} (c₁ ⊕ c₂) (inj₂ y) | inspect (ev {κ = ☐} (c₁ ⊕ c₂)) (inj₂ y)
eval≡interp (c₁ ⊕ c₂) (inj₂ y) | inj₁ (y' , rs) | [ eq ] | inj₁ (y'' , rs') | [ eq' ] rewrite (sym (eval≡interp c₂ y)) | eq with deterministic* ((↦₅ ∷ ◾) ++↦ appendκ↦* rs (λ ()) (λ ()) refl (c₁ ⊕☐• ☐) ++↦ (↦₁₂ ∷ ◾)) rs' (λ ()) (λ ())
... | refl = refl
eval≡interp (c₁ ⊕ c₂) (inj₂ y) | inj₁ (y' , rs) | [ eq ] | inj₂ rs'         | [ eq' ] rewrite (sym (eval≡interp c₂ y)) | eq with deterministic* ((↦₅ ∷ ◾) ++↦ appendκ↦* rs (λ ()) (λ ()) refl (c₁ ⊕☐• ☐) ++↦ (↦₁₂ ∷ ◾)) rs' (λ ()) (λ ())
... | ()
eval≡interp (c₁ ⊕ c₂) (inj₂ y) | inj₂ rs        | [ eq ] with ev {κ = ☐} (c₁ ⊕ c₂) (inj₂ y) | inspect (ev {κ = ☐} (c₁ ⊕ c₂)) (inj₂ y)
eval≡interp (c₁ ⊕ c₂) (inj₂ y) | inj₂ rs        | [ eq ] | inj₁ (y'' , rs') | [ eq' ] rewrite (sym (eval≡interp c₂ y)) | eq with deterministic* ((↦₅ ∷ ◾) ++↦ appendκ↦*⊠ rs (λ ()) (c₁ ⊕☐• ☐)) rs' (λ ()) (λ ())
... | ()
eval≡interp (c₁ ⊕ c₂) (inj₂ y) | inj₂ rs        | [ eq ] | inj₂ rs'         | [ eq' ] rewrite (sym (eval≡interp c₂ y)) | eq = refl
eval≡interp (c₁ ⊗ c₂) (x , y) with ev {κ = ☐} c₁ x | inspect (ev {κ = ☐} c₁) x
eval≡interp (c₁ ⊗ c₂) (x , y) | inj₁ (x' , rs) | [ eq ] with ev {κ = ☐} c₂ y | inspect (ev {κ = ☐} c₂) y
eval≡interp (c₁ ⊗ c₂) (x , y) | inj₁ (x' , rs) | [ eq ] | inj₁ (y' , rs') | [ eq' ] with ev {κ = ☐} (c₁ ⊗ c₂) (x , y) | inspect (ev {κ = ☐} (c₁ ⊗ c₂)) (x , y)
eval≡interp (c₁ ⊗ c₂) (x , y) | inj₁ (x' , rs) | [ eq ] | inj₁ (y' , rs') | [ eq' ] | inj₁ (_ , rs'') | [ eq'' ] rewrite (sym (eval≡interp c₁ x)) | eq | (sym (eval≡interp c₂ y)) | eq' with deterministic* (((↦₆ ∷ ◾) ++↦ appendκ↦* rs (λ ()) (λ ()) refl (☐⊗[ c₂ , y ]• ☐)) ++↦ (↦₈ ∷ ◾) ++↦ appendκ↦* rs' (λ ()) (λ ()) refl ([ c₁ , x' ]⊗☐• ☐) ++↦ (↦₉ ∷ ◾)) rs'' (λ ()) (λ ())
... | refl = refl
eval≡interp (c₁ ⊗ c₂) (x , y) | inj₁ (x' , rs) | [ eq ] | inj₁ (y' , rs') | [ eq' ] | inj₂ rs''       | [ eq'' ] rewrite (sym (eval≡interp c₁ x)) | eq | (sym (eval≡interp c₂ y)) | eq' with deterministic* (((↦₆ ∷ ◾) ++↦ appendκ↦* rs (λ ()) (λ ()) refl (☐⊗[ c₂ , y ]• ☐)) ++↦ (↦₈ ∷ ◾) ++↦ appendκ↦* rs' (λ ()) (λ ()) refl ([ c₁ , x' ]⊗☐• ☐) ++↦ (↦₉ ∷ ◾)) rs'' (λ ()) (λ ())
... | ()
eval≡interp (c₁ ⊗ c₂) (x , y) | inj₁ (x' , rs) | [ eq ] | inj₂ rs'        | [ eq' ] with ev {κ = ☐} (c₁ ⊗ c₂) (x , y) | inspect (ev {κ = ☐} (c₁ ⊗ c₂)) (x , y)
eval≡interp (c₁ ⊗ c₂) (x , y) | inj₁ (x' , rs) | [ eq ] | inj₂ rs'        | [ eq' ] | inj₁ (y' , rs'') | [ eq'' ] rewrite (sym (eval≡interp c₁ x)) | eq | (sym (eval≡interp c₂ y)) | eq' with deterministic* (((↦₆ ∷ ◾) ++↦ appendκ↦* rs (λ ()) (λ ()) refl (☐⊗[ c₂ , y ]• ☐)) ++↦ (↦₈ ∷ ◾) ++↦ appendκ↦*⊠ rs' (λ ()) ([ c₁ , x' ]⊗☐• ☐)) rs'' (λ ()) (λ ())
... | ()
eval≡interp (c₁ ⊗ c₂) (x , y) | inj₁ (x' , rs) | [ eq ] | inj₂ rs'        | [ eq' ] | inj₂ rs''        | [ eq'' ] rewrite (sym (eval≡interp c₁ x)) | eq | (sym (eval≡interp c₂ y)) | eq' = refl
eval≡interp (c₁ ⊗ c₂) (x , y) | inj₂ rs        | [ eq ] with ev {κ = ☐} (c₁ ⊗ c₂) (x , y) | inspect (ev {κ = ☐} (c₁ ⊗ c₂)) (x , y)
eval≡interp (c₁ ⊗ c₂) (x , y) | inj₂ rs        | [ eq ] | inj₁ (_ , rs') | [ eq' ] rewrite (sym (eval≡interp c₁ x)) | eq with deterministic* ((↦₆ ∷ ◾) ++↦ appendκ↦*⊠ rs (λ ()) (☐⊗[ c₂ , y ]• ☐)) rs' (λ ()) (λ ())
... | ()
eval≡interp (c₁ ⊗ c₂) (x , y) | inj₂ rs        | [ eq ] | inj₂ rs''      | [ eq' ] rewrite (sym (eval≡interp c₁ x)) | eq = refl
eval≡interp (ηₓ v) tt = refl
eval≡interp (εₓ v) (v' , ↻) with v ≟ v'
... | yes refl = refl
... | no  _    = refl

-- !c is the inverse computation of c
interp! : ∀ {A B} (c : A ↔ B) (a : ⟦ A ⟧) (b : ⟦ B ⟧) → interp c a ≡ just b → interp (! c) b ≡ just a
interp! unite₊l (inj₂ y) .y refl = refl
interp! uniti₊l y .(inj₂ y) refl = refl
interp! swap₊ (inj₁ x) .(inj₂ x) refl = refl
interp! swap₊ (inj₂ y) .(inj₁ y) refl = refl
interp! assocl₊ (inj₁ x) .(inj₁ (inj₁ x)) refl = refl
interp! assocl₊ (inj₂ (inj₁ y)) .(inj₁ (inj₂ y)) refl = refl
interp! assocl₊ (inj₂ (inj₂ z)) .(inj₂ z) refl = refl
interp! assocr₊ (inj₁ (inj₁ x)) .(inj₁ x) refl = refl
interp! assocr₊ (inj₁ (inj₂ y)) .(inj₂ (inj₁ y)) refl = refl
interp! assocr₊ (inj₂ z) .(inj₂ (inj₂ z)) refl = refl
interp! unite⋆l (tt , v) .v refl = refl
interp! uniti⋆l v .(tt , v) refl = refl
interp! swap⋆ (x , y) .(y , x) refl = refl
interp! assocl⋆ (x , y , z) .((x , y) , z) refl = refl
interp! assocr⋆ ((x , y) , z) .(x , y , z) refl = refl
interp! dist (inj₁ x , z) .(inj₁ (x , z)) refl = refl
interp! dist (inj₂ y , z) .(inj₂ (y , z)) refl = refl
interp! factor (inj₁ (x , z)) .(inj₁ x , z) refl = refl
interp! factor (inj₂ (y , z)) .(inj₂ y , z) refl = refl
interp! id↔ v .v refl = refl
interp! (c₁ ⨾ c₂) a c eq with interp c₁ a | inspect (interp c₁) a
... | just b  | [ eq₁ ] with interp c₂ b | inspect (interp c₂) b
... | just c' | [ eq₂ ] with eq
... | refl rewrite interp! c₂ b c eq₂ | interp! c₁ a b eq₁ = refl
interp! (c₁ ⊕ c₂) (inj₁ x) b eq with interp c₁ x | inspect (interp c₁) x
... | just x' | [ eqx ] with b
... | inj₁ _ with eq
... | refl rewrite interp! c₁ x x' eqx = refl
interp! (c₁ ⊕ c₂) (inj₂ y) b eq with interp c₂ y | inspect (interp c₂) y
... | just y' | [ eqy ] with b
... | inj₂ _ with eq
... | refl rewrite interp! c₂ y y' eqy = refl
interp! (c₁ ⊗ c₂) (x , y) (x' , y') eq with interp c₁ x | inspect (interp c₁) x | interp c₂ y | inspect (interp c₂) y
... | just x'' | [ eqx ] | just y'' | [ eqy ] with eq
... | refl rewrite interp! c₁ x x' eqx | interp! c₂ y y' eqy = refl
interp! (ηₓ v) tt .(v , ↻) refl with v ≟ v
... | yes refl = refl
... | no  neq  = ⊥-elim (neq refl)
interp! (εₓ v) (v' , ↻) b eq with v ≟ v'
... | yes refl = refl
interp! (εₓ _) (v' , ↻) b () | no neq
