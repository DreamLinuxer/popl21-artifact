module Pi-.Eval where
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.Core
open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties
open import Data.List as L hiding (_∷_)
open import Function using (_∘_)
open import Pi-.Syntax
open import Pi-.Opsem
open import Pi-.NoRepeat
open import Pi-.Invariants

infix 100 _⃗
infix 100 _⃖

-- Stuck states must be either of the form ［ c ∣ v ∣ ☐ ］ or ［ c ∣ v ∣ ☐ ］▷
Stuck : ∀ {st} → is-stuck st
      → (Σ[ A ∈ 𝕌 ] Σ[ B ∈ 𝕌 ] Σ[ c ∈ A ↔ B ] Σ[ v ∈ ⟦ A ⟧ ] st ≡ ⟨ c ∣ v ∣ ☐ ⟩◁)
      ⊎ (Σ[ A ∈ 𝕌 ] Σ[ B ∈ 𝕌 ] Σ[ c ∈ A ↔ B ] Σ[ v ∈ ⟦ B ⟧ ] st ≡ ［ c ∣ v ∣ ☐ ］▷)
Stuck {⟨ unite₊l ∣ v          ∣ κ ⟩▷} stuck = ⊥-elim (stuck (_ , ↦⃗₁))
Stuck {⟨ uniti₊l ∣ v          ∣ κ ⟩▷} stuck = ⊥-elim (stuck (_ , ↦⃗₁))
Stuck {⟨ swap₊   ∣ v          ∣ κ ⟩▷} stuck = ⊥-elim (stuck (_ , ↦⃗₁))
Stuck {⟨ assocl₊ ∣ v          ∣ κ ⟩▷} stuck = ⊥-elim (stuck (_ , ↦⃗₁))
Stuck {⟨ assocr₊ ∣ v          ∣ κ ⟩▷} stuck = ⊥-elim (stuck (_ , ↦⃗₁))
Stuck {⟨ unite⋆l ∣ v          ∣ κ ⟩▷} stuck = ⊥-elim (stuck (_ , ↦⃗₁))
Stuck {⟨ uniti⋆l ∣ v          ∣ κ ⟩▷} stuck = ⊥-elim (stuck (_ , ↦⃗₁))
Stuck {⟨ swap⋆   ∣ v          ∣ κ ⟩▷} stuck = ⊥-elim (stuck (_ , ↦⃗₁))
Stuck {⟨ assocl⋆ ∣ v          ∣ κ ⟩▷} stuck = ⊥-elim (stuck (_ , ↦⃗₁))
Stuck {⟨ assocr⋆ ∣ v          ∣ κ ⟩▷} stuck = ⊥-elim (stuck (_ , ↦⃗₁))
Stuck {⟨ dist    ∣ v          ∣ κ ⟩▷} stuck = ⊥-elim (stuck (_ , ↦⃗₁))
Stuck {⟨ factor  ∣ v          ∣ κ ⟩▷} stuck = ⊥-elim (stuck (_ , ↦⃗₁))
Stuck {⟨ id↔     ∣ v          ∣ κ ⟩▷} stuck = ⊥-elim (stuck (_ , ↦⃗₂))
Stuck {⟨ c₁ ⨾ c₂ ∣ v          ∣ κ ⟩▷} stuck = ⊥-elim (stuck (_ , ↦⃗₃))
Stuck {⟨ c₁ ⊕ c₂ ∣ inj₁ x     ∣ κ ⟩▷} stuck = ⊥-elim (stuck (_ , ↦⃗₄))
Stuck {⟨ c₁ ⊕ c₂ ∣ inj₂ y     ∣ κ ⟩▷} stuck = ⊥-elim (stuck (_ , ↦⃗₅))
Stuck {⟨ c₁ ⊗ c₂ ∣ (x , y)    ∣ κ ⟩▷} stuck = ⊥-elim (stuck (_ , ↦⃗₆))
Stuck {⟨ ε₊      ∣ inj₁ x     ∣ κ ⟩▷} stuck = ⊥-elim (stuck (_ , ↦ε₁))
Stuck {⟨ ε₊      ∣ inj₂ (- x) ∣ κ ⟩▷} stuck = ⊥-elim (stuck (_ , ↦ε₂))
Stuck {［ c ∣ v ∣ ☐ ］▷}               stuck = inj₂ (_ , _ , c , v , refl)
Stuck {［ c₁ ∣ v ∣ ☐⨾ c₂ • κ ］▷}      stuck = ⊥-elim (stuck (_ , ↦⃗₇))
Stuck {［ c ∣ v ∣ c₁ ⨾☐• κ ］▷}        stuck = ⊥-elim (stuck (_ , ↦⃗₁₀))
Stuck {［ c ∣ v ∣ ☐⊕ c₂ • κ ］▷}       stuck = ⊥-elim (stuck (_ , ↦⃗₁₁))
Stuck {［ c ∣ v ∣ c₁ ⊕☐• κ ］▷}        stuck = ⊥-elim (stuck (_ , ↦⃗₁₂))
Stuck {［ c ∣ v ∣ ☐⊗[ c₂ , x ]• κ ］▷} stuck = ⊥-elim (stuck (_ , ↦⃗₈))
Stuck {［ c ∣ v ∣ [ c₁ , x ]⊗☐• κ ］▷} stuck = ⊥-elim (stuck (_ , ↦⃗₉))
Stuck {⟨ c  ∣ v ∣ ☐ ⟩◁}                stuck = inj₁ (_ , _ , c , v , refl)
Stuck {⟨ c₁ ∣ v ∣ ☐⨾ c₂ • κ ⟩◁}        stuck = ⊥-elim (stuck (_ , ↦⃖₃))
Stuck {⟨ c₂ ∣ v ∣ c₁ ⨾☐• κ ⟩◁}         stuck = ⊥-elim (stuck (_ , ↦⃖₇))
Stuck {⟨ c₁ ∣ v ∣ ☐⊕ c₂ • κ ⟩◁}        stuck = ⊥-elim (stuck (_ , ↦⃖₄))
Stuck {⟨ c₂ ∣ v ∣ c₁ ⊕☐• κ ⟩◁}         stuck = ⊥-elim (stuck (_ , ↦⃖₅))
Stuck {⟨ c₁ ∣ x ∣ ☐⊗[ c₂ , y ]• κ ⟩◁}  stuck = ⊥-elim (stuck (_ , ↦⃖₆))
Stuck {⟨ c₂ ∣ y ∣ [ c₁ , x ]⊗☐• κ ⟩◁}  stuck = ⊥-elim (stuck (_ , ↦⃖₈))
Stuck {［ unite₊l ∣ v ∣ κ ］◁}             stuck = ⊥-elim (stuck (⟨ _ ∣ inj₂ v ∣ _ ⟩◁ , ↦⃖₁))
Stuck {［ uniti₊l ∣ inj₂ y ∣ κ ］◁}        stuck = ⊥-elim (stuck (⟨ _ ∣ y ∣ _ ⟩◁ , ↦⃖₁))
Stuck {［ swap₊ ∣ inj₁ x ∣ κ ］◁}          stuck = ⊥-elim (stuck (⟨ _ ∣ inj₂ x ∣ _ ⟩◁ , ↦⃖₁))
Stuck {［ swap₊ ∣ inj₂ y ∣ κ ］◁}          stuck = ⊥-elim (stuck (⟨ _ ∣ inj₁ y ∣ _ ⟩◁ , ↦⃖₁))
Stuck {［ assocl₊ ∣ inj₁ (inj₁ x) ∣ κ ］◁} stuck = ⊥-elim (stuck (⟨ _ ∣ inj₁ x ∣ _ ⟩◁ , ↦⃖₁))
Stuck {［ assocl₊ ∣ inj₁ (inj₂ y) ∣ κ ］◁} stuck = ⊥-elim (stuck (⟨ _ ∣ inj₂ (inj₁ y) ∣ _ ⟩◁ , ↦⃖₁))
Stuck {［ assocl₊ ∣ inj₂ y ∣ κ ］◁}        stuck = ⊥-elim (stuck (⟨ _ ∣ inj₂ (inj₂ y) ∣ _ ⟩◁ , ↦⃖₁))
Stuck {［ assocr₊ ∣ inj₁ x ∣ κ ］◁}        stuck = ⊥-elim (stuck (⟨ _ ∣ inj₁ (inj₁ x) ∣ _ ⟩◁ , ↦⃖₁))
Stuck {［ assocr₊ ∣ inj₂ (inj₁ x) ∣ κ ］◁} stuck = ⊥-elim (stuck (⟨ _ ∣ inj₁ (inj₂ x) ∣ _ ⟩◁ , ↦⃖₁))
Stuck {［ assocr₊ ∣ inj₂ (inj₂ y) ∣ κ ］◁} stuck = ⊥-elim (stuck (⟨ _ ∣ (inj₂ y) ∣ _ ⟩◁ , ↦⃖₁))
Stuck {［ unite⋆l ∣ v ∣ κ ］◁}             stuck = ⊥-elim (stuck (⟨ _ ∣ (tt , v) ∣ _ ⟩◁ , ↦⃖₁))
Stuck {［ uniti⋆l ∣ (tt , v) ∣ κ ］◁}      stuck = ⊥-elim (stuck (⟨ _ ∣ v ∣ _ ⟩◁ , ↦⃖₁))
Stuck {［ swap⋆ ∣ (x , y) ∣ κ ］◁}         stuck = ⊥-elim (stuck (⟨ _ ∣ (y , x) ∣ _ ⟩◁ , ↦⃖₁))
Stuck {［ assocl⋆ ∣ (x , y) , z ∣ κ ］◁}   stuck = ⊥-elim (stuck (⟨ _ ∣ x , (y , z) ∣ _ ⟩◁ , ↦⃖₁))
Stuck {［ assocr⋆ ∣ x , (y , z) ∣ κ ］◁}   stuck = ⊥-elim (stuck (⟨ _ ∣ (x , y) , z ∣ _ ⟩◁ , ↦⃖₁))
Stuck {［ dist ∣ inj₁ (x , z) ∣ κ ］◁}     stuck = ⊥-elim (stuck (⟨ _ ∣ inj₁ x , z ∣ _ ⟩◁ , ↦⃖₁))
Stuck {［ dist ∣ inj₂ (y , z) ∣ κ ］◁}     stuck = ⊥-elim (stuck (⟨ _ ∣ inj₂ y , z ∣ _ ⟩◁ , ↦⃖₁))
Stuck {［ factor ∣ inj₁ x , z ∣ κ ］◁}     stuck = ⊥-elim (stuck (⟨ _ ∣ inj₁ (x , z) ∣ _ ⟩◁ , ↦⃖₁))
Stuck {［ factor ∣ inj₂ y , z ∣ κ ］◁}     stuck = ⊥-elim (stuck (⟨ _ ∣ inj₂ (y , z) ∣ _ ⟩◁ , ↦⃖₁))
Stuck {［ id↔     ∣ v ∣ κ ］◁}             stuck = ⊥-elim (stuck (_ , ↦⃖₂))
Stuck {［ c₁ ⨾ c₂ ∣ v ∣ κ ］◁}             stuck = ⊥-elim (stuck (_ , ↦⃖₁₀))
Stuck {［ c₁ ⊕ c₂ ∣ inj₁ x ∣ κ ］◁}        stuck = ⊥-elim (stuck (_ , ↦⃖₁₁))
Stuck {［ c₁ ⊕ c₂ ∣ inj₂ y ∣ κ ］◁}        stuck = ⊥-elim (stuck (_ , ↦⃖₁₂))
Stuck {［ c₁ ⊗ c₂ ∣ (x , y) ∣ κ ］◁}       stuck = ⊥-elim (stuck (_ , ↦⃖₉))
Stuck {［ η₊      ∣ inj₁ x ∣ κ ］◁}        stuck = ⊥-elim (stuck (_ , ↦η₁))
Stuck {［ η₊      ∣ inj₂ (- x) ∣ κ ］◁}    stuck = ⊥-elim (stuck (_ , ↦η₂))

-- Find next step of given the state
step : (st : State) → ∃[ st' ] (st ↦ st') ⊎ is-stuck st
step ⟨ unite₊l ∣ v ∣ κ ⟩▷ = inj₁ (_ , ↦⃗₁)
step ⟨ uniti₊l ∣ v ∣ κ ⟩▷ = inj₁ (_ , ↦⃗₁)
step ⟨ swap₊   ∣ v ∣ κ ⟩▷ = inj₁ (_ , ↦⃗₁)
step ⟨ assocl₊ ∣ v ∣ κ ⟩▷ = inj₁ (_ , ↦⃗₁)
step ⟨ assocr₊ ∣ v ∣ κ ⟩▷ = inj₁ (_ , ↦⃗₁)
step ⟨ unite⋆l ∣ v ∣ κ ⟩▷ = inj₁ (_ , ↦⃗₁)
step ⟨ uniti⋆l ∣ v ∣ κ ⟩▷ = inj₁ (_ , ↦⃗₁)
step ⟨ swap⋆   ∣ v ∣ κ ⟩▷ = inj₁ (_ , ↦⃗₁)
step ⟨ assocl⋆ ∣ v ∣ κ ⟩▷ = inj₁ (_ , ↦⃗₁)
step ⟨ assocr⋆ ∣ v ∣ κ ⟩▷ = inj₁ (_ , ↦⃗₁)
step ⟨ dist    ∣ v ∣ κ ⟩▷ = inj₁ (_ , ↦⃗₁)
step ⟨ factor  ∣ v ∣ κ ⟩▷ = inj₁ (_ , ↦⃗₁)
step ⟨ id↔     ∣ v ∣ κ ⟩▷ = inj₁ (_ , ↦⃗₂)
step ⟨ c₁ ⨾ c₂ ∣ v ∣ κ ⟩▷ = inj₁ (⟨ c₁ ∣ v ∣ ☐⨾ c₂ • κ ⟩▷ , ↦⃗₃)
step ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ κ ⟩▷ = inj₁ (_ , ↦⃗₄)
step ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ κ ⟩▷ = inj₁ (_ , ↦⃗₅)
step ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ κ ⟩▷ = inj₁ (_ , ↦⃗₆)
step ⟨ ε₊      ∣ inj₁ x ∣ κ ⟩▷ = inj₁ (_ , ↦ε₁)
step ⟨ ε₊      ∣ inj₂ (- x) ∣ κ ⟩▷ = inj₁ (_ , ↦ε₂)
step ［ c  ∣ v ∣ ☐ ］▷               = inj₂ (λ ())
step ［ c₁ ∣ v ∣ ☐⨾ c₂ • κ ］▷       = inj₁ (_ , ↦⃗₇)
step ［ c₂ ∣ v ∣ c₁ ⨾☐• κ ］▷        = inj₁ (_ , ↦⃗₁₀)
step ［ c₁ ∣ v ∣ ☐⊕ c₂ • κ ］▷       = inj₁ (_ , ↦⃗₁₁)
step ［ c₂ ∣ v ∣ c₁ ⊕☐• κ ］▷        = inj₁ (_ , ↦⃗₁₂)
step ［ c₁ ∣ v ∣ ☐⊗[ c₂ , x ]• κ ］▷ = inj₁ (_ , ↦⃗₈)
step ［ c₂ ∣ v ∣ [ c₁ , x ]⊗☐• κ ］▷ = inj₁ (_ , ↦⃗₉)
step ⟨ c ∣ v ∣ ☐ ⟩◁                = inj₂ (λ ())
step ⟨ c₁ ∣ v ∣ ☐⨾ c₂ • κ ⟩◁       = inj₁ (_ , ↦⃖₃)
step ⟨ c₂ ∣ v ∣ c₁ ⨾☐• κ ⟩◁        = inj₁ (_ , ↦⃖₇)
step ⟨ c₁ ∣ v ∣ ☐⊕ c₂ • κ ⟩◁       = inj₁ (_ , ↦⃖₄)
step ⟨ c₂ ∣ v ∣ c₁ ⊕☐• κ ⟩◁        = inj₁ (_ , ↦⃖₅)
step ⟨ c₁ ∣ v ∣ ☐⊗[ c₂ , x ]• κ ⟩◁ = inj₁ (_ , ↦⃖₆)
step ⟨ c₂ ∣ v ∣ [ c₁ , x ]⊗☐• κ ⟩◁ = inj₁ (_ , ↦⃖₈)
step ［ unite₊l ∣ v             ∣ κ ］◁ = inj₁ (⟨ _ ∣ inj₂ v ∣ _ ⟩◁ , ↦⃖₁)
step ［ uniti₊l ∣ inj₂ v        ∣ κ ］◁ = inj₁ (⟨ _ ∣ v ∣ _ ⟩◁ , ↦⃖₁)
step ［ swap₊   ∣ inj₁ x        ∣ κ ］◁ = inj₁ (⟨ _ ∣ inj₂ x ∣ _ ⟩◁ , ↦⃖₁)
step ［ swap₊   ∣ inj₂ y        ∣ κ ］◁ = inj₁ (⟨ _ ∣ inj₁ y ∣ _ ⟩◁ , ↦⃖₁)
step ［ assocl₊ ∣ inj₁ (inj₁ x) ∣ κ ］◁ = inj₁ (⟨ _ ∣ inj₁ x ∣ _ ⟩◁ , ↦⃖₁)
step ［ assocl₊ ∣ inj₁ (inj₂ y) ∣ κ ］◁ = inj₁ (⟨ _ ∣ inj₂ (inj₁ y) ∣ _ ⟩◁ , ↦⃖₁)
step ［ assocl₊ ∣ inj₂ z        ∣ κ ］◁ = inj₁ (⟨ _ ∣ inj₂ (inj₂ z) ∣ _ ⟩◁ , ↦⃖₁)
step ［ assocr₊ ∣ inj₁ x        ∣ κ ］◁ = inj₁ (⟨ _ ∣ inj₁ (inj₁ x) ∣ _ ⟩◁ , ↦⃖₁)
step ［ assocr₊ ∣ inj₂ (inj₁ y) ∣ κ ］◁ = inj₁ (⟨ _ ∣ inj₁ (inj₂ y) ∣ _ ⟩◁ , ↦⃖₁)
step ［ assocr₊ ∣ inj₂ (inj₂ z) ∣ κ ］◁ = inj₁ (⟨ _ ∣ inj₂ z ∣ _ ⟩◁ , ↦⃖₁)
step ［ unite⋆l ∣ v             ∣ κ ］◁ = inj₁ (⟨ _ ∣ tt , v ∣ _ ⟩◁ , ↦⃖₁)
step ［ uniti⋆l ∣ (tt , v)      ∣ κ ］◁ = inj₁ (⟨ _ ∣ v ∣ _ ⟩◁ , ↦⃖₁)
step ［ swap⋆   ∣ (x , y)       ∣ κ ］◁ = inj₁ (⟨ _ ∣ (y , x) ∣ _ ⟩◁ , ↦⃖₁)
step ［ assocl⋆ ∣ (x , y) , z   ∣ κ ］◁ = inj₁ (⟨ _ ∣ x , (y , z) ∣ _ ⟩◁ , ↦⃖₁)
step ［ assocr⋆ ∣ x , (y , z)   ∣ κ ］◁ = inj₁ (⟨ _ ∣ (x , y) , z ∣ _ ⟩◁ , ↦⃖₁)
step ［ dist    ∣ inj₁ (x , z)  ∣ κ ］◁ = inj₁ (⟨ _ ∣ inj₁ x , z ∣ _ ⟩◁ , ↦⃖₁)
step ［ dist    ∣ inj₂ (y , z)  ∣ κ ］◁ = inj₁ (⟨ _ ∣ inj₂ y , z ∣ _ ⟩◁ , ↦⃖₁)
step ［ factor  ∣ inj₁ x , z    ∣ κ ］◁ = inj₁ (⟨ _ ∣ inj₁ (x , z) ∣ _ ⟩◁ , ↦⃖₁)
step ［ factor  ∣ inj₂ y , z    ∣ κ ］◁ = inj₁ (⟨ _ ∣ inj₂ (y , z) ∣ _ ⟩◁ , ↦⃖₁)
step ［ id↔     ∣ v             ∣ κ ］◁ = inj₁ (_ , ↦⃖₂)
step ［ c₁ ⨾ c₂ ∣ v             ∣ κ ］◁ = inj₁ (_ , ↦⃖₁₀)
step ［ c₁ ⊕ c₂ ∣ inj₁ x        ∣ κ ］◁ = inj₁ (_ , ↦⃖₁₁)
step ［ c₁ ⊕ c₂ ∣ inj₂ y        ∣ κ ］◁ = inj₁ (_ , ↦⃖₁₂)
step ［ c₁ ⊗ c₂ ∣ (x , y)       ∣ κ ］◁ = inj₁ (_ , ↦⃖₉)
step ［ η₊ ∣ inj₁ x             ∣ κ ］◁ = inj₁ (_ , ↦η₁)
step ［ η₊ ∣ inj₂ (- x)         ∣ κ ］◁ = inj₁ (_ , ↦η₂)

-- Values tagged with direction
data Val (A B : 𝕌) : Set where
  _⃗ : ⟦ A ⟧ → Val A B
  _⃖ : ⟦ B ⟧ → Val A B

-- Termination is guaranteed by Pi-.NoRepeat and the finiteness of states
{-# TERMINATING #-}
run : (st₀ : State) → is-initial st₀ → let (A , B , c) = getℂ st₀
                                       in  (Σ[ v ∈ ⟦ A ⟧ ] st₀ ↦* ⟨ c ∣ v ∣ ☐ ⟩◁)
                                        ⊎  (Σ[ v ∈ ⟦ B ⟧ ] st₀ ↦* ［ c ∣ v ∣ ☐ ］▷)
run st₀ init = run' st₀ ◾
  where
    run' : (st : State) → st₀ ↦* st → let (A , B , c) = getℂ st₀
                                      in (Σ[ v ∈ ⟦ A ⟧ ] st₀ ↦* ⟨ c ∣ v ∣ ☐ ⟩◁)
                                       ⊎ (Σ[ v ∈ ⟦ B ⟧ ] st₀ ↦* ［ c ∣ v ∣ ☐ ］▷)
    run' st rs with step st
    ... | inj₁ (st' , r) = run' st' (rs ++↦ (r ∷ ◾))
    ... | inj₂ stuck     with Stuck stuck
    ... | inj₁ (A , B , c , v , refl) with ℂInvariant* rs
    ... | refl = inj₁ (v , rs)
    run' st rs | inj₂ stuck | inj₂ (A , B , c , v , refl) with ℂInvariant* rs
    ... | refl = inj₂ (v , rs)

-- Forward evaluator of Pi-
eval : ∀ {A B} → (A ↔ B) → Val A B → Val B A
eval c (v ⃗) = [ _⃖ ∘ proj₁ , _⃗ ∘ proj₁ ]′ (run ⟨ c ∣ v ∣ ☐ ⟩▷ (λ ()))
eval c (v ⃖) = [ _⃖ ∘ proj₁ , _⃗ ∘ proj₁ ]′ (run ［ c ∣ v ∣ ☐ ］◁ (λ ()))

-- Backward evaluator of Pi-
evalᵣₑᵥ : ∀ {A B} → (A ↔ B) → Val B A → Val A B
evalᵣₑᵥ c (v ⃖) = [ _⃗ ∘ proj₁ , _⃖ ∘ proj₁ ]′ (run ⟨ c ∣ v ∣ ☐ ⟩▷ (λ ()))
evalᵣₑᵥ c (v ⃗) = [ _⃗ ∘ proj₁ , _⃖ ∘ proj₁ ]′ (run ［ c ∣ v ∣ ☐ ］◁ (λ ()))

-- Evaluator which generate execution traces
convert↦ : ∀ {st st'} → st ↦* st' → List State
convert↦ (◾ {st}) = st L.∷ []
convert↦ (_∷_ {st} r rs) = st L.∷ convert↦ rs

evalₜᵣ : ∀ {A B} → (A ↔ B) → ⟦ A ⟧ → List State
evalₜᵣ c v with (run ⟨ c ∣ v ∣ ☐ ⟩▷ (λ ()))
... | inj₁ (_ , rs) = convert↦ rs
... | inj₂ (_ , rs) = convert↦ rs

-- Faster evaluator which does not carry the reduction trace.
-- Returns the result and the number of steps it takes
{-# TERMINATING #-}
eval' : ∀ {A B} → (A ↔ B) → ⟦ A ⟧ → (Σ[ t ∈ 𝕌 ] ⟦ t ⟧) × ℕ
eval' c v = run' ⟨ c ∣ v ∣ ☐ ⟩▷ 0
  where
  getV : State → Σ[ t ∈ 𝕌 ] ⟦ t ⟧
  getV ⟨ _ ∣ v ∣ _ ⟩▷ = _ , v
  getV ［ _ ∣ v ∣ _ ］▷ = _ , v
  getV ⟨ _ ∣ v ∣ _ ⟩◁ = _ , v
  getV ［ _ ∣ v ∣ _ ］◁ = _ , v

  run' : State → ℕ → (Σ[ t ∈ 𝕌 ] ⟦ t ⟧) × ℕ
  run' st n with step st
  ... | inj₁ (st' , _) = run' st' (suc n)
  ... | inj₂ stuck     = getV st , n
