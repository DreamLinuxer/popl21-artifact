module Pi-.Properties where
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
open import Function using (_∘_)
open import Base
open import Pi-.Syntax
open import Pi-.Opsem
open import Pi-.NoRepeat
open import Pi-.Invariants
open import Pi-.Eval
open import Pi-.Interp

-- Change the direction of the given state
flip : State → State
flip ⟨ c ∣ v ∣ κ ⟩▷ = ⟨ c ∣ v ∣ κ ⟩◁
flip ［ c ∣ v ∣ κ ］▷ = ［ c ∣ v ∣ κ ］◁
flip ⟨ c ∣ v ∣ κ ⟩◁ = ⟨ c ∣ v ∣ κ ⟩▷
flip ［ c ∣ v ∣ κ ］◁ = ［ c ∣ v ∣ κ ］▷

Rev : ∀ {st st'} → st ↦ st' → flip st' ↦ flip st
Rev ↦⃗₁ = ↦⃖₁
Rev ↦⃗₂ = ↦⃖₂
Rev ↦⃗₃ = ↦⃖₃
Rev ↦⃗₄ = ↦⃖₄
Rev ↦⃗₅ = ↦⃖₅
Rev ↦⃗₆ = ↦⃖₆
Rev ↦⃗₇ = ↦⃖₇
Rev ↦⃗₈ = ↦⃖₈
Rev ↦⃗₉ = ↦⃖₉
Rev ↦⃗₁₀ = ↦⃖₁₀
Rev ↦⃗₁₁ = ↦⃖₁₁
Rev ↦⃗₁₂ = ↦⃖₁₂
Rev ↦⃖₁ = ↦⃗₁
Rev ↦⃖₂ = ↦⃗₂
Rev ↦⃖₃ = ↦⃗₃
Rev ↦⃖₄ = ↦⃗₄
Rev ↦⃖₅ = ↦⃗₅
Rev ↦⃖₆ = ↦⃗₆
Rev ↦⃖₇ = ↦⃗₇
Rev ↦⃖₈ = ↦⃗₈
Rev ↦⃖₉ = ↦⃗₉
Rev ↦⃖₁₀ = ↦⃗₁₀
Rev ↦⃖₁₁ = ↦⃗₁₁
Rev ↦⃖₁₂ = ↦⃗₁₂
Rev ↦η₁ = ↦η₂
Rev ↦η₂ = ↦η₁
Rev ↦ε₁ = ↦ε₂
Rev ↦ε₂ = ↦ε₁

Rev* : ∀ {st st'} → st ↦* st' → flip st' ↦* flip st
Rev* ◾ = ◾
Rev* (r ∷ rs) = Rev* rs ++↦ (Rev r ∷ ◾)

-- Helper function
inspect⊎ : ∀ {ℓ ℓ' ℓ''} {P : Set ℓ} {Q : Set ℓ'} {R : Set ℓ''}
         → (f : P → Q ⊎ R) → (p : P) → (∃[ q ] (inj₁ q ≡ f p)) ⊎ (∃[ r ] (inj₂ r ≡ f p))
inspect⊎ f p with f p
... | inj₁ q = inj₁ (q , refl)
... | inj₂ r = inj₂ (r , refl)

-- Forward evaluator is reversible
evalisRev : ∀ {A B} → (c : A ↔ B) → (v : Val A B) → evalᵣₑᵥ c (eval c v) ≡ v
evalisRev c (v ⃖) with inspect⊎ (run ［ c ∣ v ∣ ☐ ］◁) (λ ())
evalisRev c (v ⃖) | inj₁ ((v' , rs) , eq) with inspect⊎ (run ⟨ c ∣ v' ∣ ☐ ⟩▷) (λ ())
evalisRev c (v ⃖) | inj₁ ((v' , rs) , eq) | inj₁ ((_ , rs') , eq') with deterministic* (Rev* rs) rs' (λ ()) (λ ())
... | ()
evalisRev c (v ⃖) | inj₁ ((v' , rs) , eq) | inj₂ ((_ , rs') , eq') with deterministic* (Rev* rs) rs' (λ ()) (λ ())
... | refl = subst (λ x → evalᵣₑᵥ c ([ _⃖ ∘ proj₁ , _⃗ ∘ proj₁ ]′ x) ≡ (v ⃖)) eq
                   (subst (λ x → [ _⃗ ∘ proj₁ , _⃖ ∘ proj₁ ]′ x ≡ (v ⃖)) eq' refl)
evalisRev c (v ⃖) | inj₂ ((v' , rs) , eq) with inspect⊎ (run ［ c ∣ v' ∣ ☐ ］◁) (λ ())
evalisRev c (v ⃖) | inj₂ ((v' , rs) , eq) | inj₁ ((_ , rs') , eq') with deterministic* (Rev* rs) rs' (λ ()) (λ ())
... | ()
evalisRev c (v ⃖) | inj₂ ((v' , rs) , eq) | inj₂ ((_ , rs') , eq') with deterministic* (Rev* rs) rs' (λ ()) (λ ())
... | refl = subst (λ x → evalᵣₑᵥ c ([ _⃖ ∘ proj₁ , _⃗ ∘ proj₁ ]′ x) ≡ (v ⃖)) eq
                   (subst (λ x → [ _⃗ ∘ proj₁ , _⃖ ∘ proj₁ ]′ x ≡ (v ⃖)) eq' refl)
evalisRev c (v ⃗) with inspect⊎ (run ⟨ c ∣ v ∣ ☐ ⟩▷) (λ ())
evalisRev c (v ⃗) | inj₁ ((v' , rs) , eq) with inspect⊎ (run ⟨ c ∣ v' ∣ ☐ ⟩▷) (λ ())
evalisRev c (v ⃗) | inj₁ ((v' , rs) , eq) | inj₁ ((_ , rs') , eq') with deterministic* (Rev* rs) rs' (λ ()) (λ ())
... | refl = subst (λ x → evalᵣₑᵥ c ([ _⃖ ∘ proj₁ , _⃗ ∘ proj₁ ]′ x) ≡ (v ⃗)) eq
                   (subst (λ x → [ _⃗ ∘ proj₁ , _⃖ ∘ proj₁ ]′ x ≡ (v ⃗)) eq' refl)
evalisRev c (v ⃗) | inj₁ ((v' , rs) , eq) | inj₂ ((_ , rs') , eq') with deterministic* (Rev* rs) rs' (λ ()) (λ ())
... | ()
evalisRev c (v ⃗) | inj₂ ((v' , rs) , eq) with inspect⊎ (run ［ c ∣ v' ∣ ☐ ］◁) (λ ())
evalisRev c (v ⃗) | inj₂ ((v' , rs) , eq) | inj₁ ((_ , rs') , eq') with deterministic* (Rev* rs) rs' (λ ()) (λ ())
... | refl = subst (λ x → evalᵣₑᵥ c ([ _⃖ ∘ proj₁ , _⃗ ∘ proj₁ ]′ x) ≡ (v ⃗)) eq
                   (subst (λ x → [ _⃗ ∘ proj₁ , _⃖ ∘ proj₁ ]′ x ≡ (v ⃗)) eq' refl)
evalisRev c (v ⃗) | inj₂ ((v' , rs) , eq) | inj₂ ((_ , rs') , eq') with deterministic* (Rev* rs) rs' (λ ()) (λ ())
... | ()

-- Backward evaluator is reversible
evalᵣₑᵥisRev : ∀ {A B} → (c : A ↔ B) → (v : Val B A) → eval c (evalᵣₑᵥ c v) ≡ v
evalᵣₑᵥisRev c (v ⃖) with inspect⊎ (run ⟨ c ∣ v ∣ ☐ ⟩▷) (λ ())
evalᵣₑᵥisRev c (v ⃖) | inj₁ ((v' , rs) , eq) with inspect⊎ (run ⟨ c ∣ v' ∣ ☐ ⟩▷) (λ ())
evalᵣₑᵥisRev c (v ⃖) | inj₁ ((v' , rs) , eq) | inj₁ ((_ , rs') , eq') with deterministic* (Rev* rs) rs' (λ ()) (λ ())
... | refl = subst (λ x → eval c ([ _⃗ ∘ proj₁ , _⃖ ∘ proj₁ ]′ x) ≡ (v ⃖)) eq
                   (subst (λ x → [ _⃖ ∘ proj₁ , _⃗ ∘ proj₁ ]′ x ≡ (v ⃖)) eq' refl)
evalᵣₑᵥisRev c (v ⃖) | inj₁ ((v' , rs) , eq) | inj₂ ((_ , rs') , eq') with deterministic* (Rev* rs) rs' (λ ()) (λ ())
... | ()
evalᵣₑᵥisRev c (v ⃖) | inj₂ ((v' , rs) , eq) with inspect⊎ (run ［ c ∣ v' ∣ ☐ ］◁) (λ ())
evalᵣₑᵥisRev c (v ⃖) | inj₂ ((v' , rs) , eq) | inj₁ ((_ , rs') , eq') with deterministic* (Rev* rs) rs' (λ ()) (λ ())
... | refl = subst (λ x → eval c ([ _⃗ ∘ proj₁ , _⃖ ∘ proj₁ ]′ x) ≡ (v ⃖)) eq
                   (subst (λ x → [ _⃖ ∘ proj₁ , _⃗ ∘ proj₁ ]′ x ≡ (v ⃖)) eq' refl)
evalᵣₑᵥisRev c (v ⃖) | inj₂ ((v' , rs) , eq) | inj₂ ((_ , rs') , eq') with deterministic* (Rev* rs) rs' (λ ()) (λ ())
... | ()
evalᵣₑᵥisRev c (v ⃗) with inspect⊎ (run ［ c ∣ v ∣ ☐ ］◁) (λ ())
evalᵣₑᵥisRev c (v ⃗) | inj₁ ((v' , rs) , eq) with inspect⊎ (run ⟨ c ∣ v' ∣ ☐ ⟩▷) (λ ())
evalᵣₑᵥisRev c (v ⃗) | inj₁ ((v' , rs) , eq) | inj₁ ((_ , rs') , eq') with deterministic* (Rev* rs) rs' (λ ()) (λ ())
... | ()
evalᵣₑᵥisRev c (v ⃗) | inj₁ ((v' , rs) , eq) | inj₂ ((_ , rs') , eq') with deterministic* (Rev* rs) rs' (λ ()) (λ ())
... | refl = subst (λ x → eval c ([ _⃗ ∘ proj₁ , _⃖ ∘ proj₁ ]′ x) ≡ (v ⃗)) eq
                   (subst (λ x → [ _⃖ ∘ proj₁ , _⃗ ∘ proj₁ ]′ x ≡ (v ⃗)) eq' refl)
evalᵣₑᵥisRev c (v ⃗) | inj₂ ((v' , rs) , eq) with inspect⊎ (run ［ c ∣ v' ∣ ☐ ］◁) (λ ())
evalᵣₑᵥisRev c (v ⃗) | inj₂ ((v' , rs) , eq) | inj₁ ((_ , rs') , eq') with deterministic* (Rev* rs) rs' (λ ()) (λ ())
... | ()
evalᵣₑᵥisRev c (v ⃗) | inj₂ ((v' , rs) , eq) | inj₂ ((_ , rs') , eq') with deterministic* (Rev* rs) rs' (λ ()) (λ ())
... | refl = subst (λ x → eval c ([ _⃗ ∘ proj₁ , _⃖ ∘ proj₁ ]′ x) ≡ (v ⃗)) eq
                   (subst (λ x → [ _⃖ ∘ proj₁ , _⃗ ∘ proj₁ ]′ x ≡ (v ⃗)) eq' refl)

getₜᵣ⃗ : ∀ {A B} → (c : A ↔ B) → {v : ⟦ A ⟧} {v' : Val B A} → eval c (v ⃗) ≡ v'
       → let tr : Val B A → Set _
             tr = (λ {(w ⃖) → ⟨ c ∣ v ∣ ☐ ⟩▷ ↦*  ⟨ c ∣ w ∣ ☐ ⟩◁ ;
                      (w ⃗) → ⟨ c ∣ v ∣ ☐ ⟩▷ ↦* ［ c ∣ w ∣ ☐ ］▷})
         in  tr v'
getₜᵣ⃗ c {v} {v'} eq with inspect⊎ (run ⟨ c ∣ v ∣ ☐ ⟩▷) (λ ())
getₜᵣ⃗ c {v} {v' ⃗} eq | inj₁ ((v'' , rs) , eq') with trans (subst (λ x → (v'' ⃖) ≡ [ _⃖ ∘ proj₁ ,  _⃗ ∘ proj₁ ]′ x) eq' refl) eq
... | ()
getₜᵣ⃗ c {v} {v' ⃖} eq | inj₁ ((v'' , rs) , eq') with trans (subst (λ x → (v'' ⃖) ≡ [ _⃖ ∘ proj₁ ,  _⃗ ∘ proj₁ ]′ x) eq' refl) eq
... | refl = rs
getₜᵣ⃗ c {v} {v' ⃗} eq | inj₂ ((v'' , rs) , eq') with trans (subst (λ x → (v'' ⃗) ≡ [ _⃖ ∘ proj₁ ,  _⃗ ∘ proj₁ ]′ x) eq' refl) eq
... | refl = rs
getₜᵣ⃗ c {v} {v' ⃖} eq | inj₂ ((v'' , rs) , eq') with trans (subst (λ x → (v'' ⃗) ≡ [ _⃖ ∘ proj₁ ,  _⃗ ∘ proj₁ ]′ x) eq' refl) eq
... | ()

getₜᵣ⃖ : ∀ {A B} → (c : A ↔ B) → {v : ⟦ B ⟧} {v' : Val B A} → eval c (v ⃖) ≡ v'
       → let tr : Val B A → Set _
             tr = (λ {(w ⃖) → ［ c ∣ v ∣ ☐ ］◁ ↦*  ⟨ c ∣ w ∣ ☐ ⟩◁ ;
                      (w ⃗) → ［ c ∣ v ∣ ☐ ］◁ ↦* ［ c ∣ w ∣ ☐ ］▷ })
         in  tr v'
getₜᵣ⃖ c {v} {v'} eq with inspect⊎ (run ［ c ∣ v ∣ ☐ ］◁) (λ ())
getₜᵣ⃖ c {v} {v' ⃗} eq | inj₁ ((v'' , rs) , eq') with trans (subst (λ x → (v'' ⃖) ≡ [ _⃖ ∘ proj₁ ,  _⃗ ∘ proj₁ ]′ x) eq' refl) eq
... | ()
getₜᵣ⃖ c {v} {v' ⃖} eq | inj₁ ((v'' , rs) , eq') with trans (subst (λ x → (v'' ⃖) ≡ [ _⃖ ∘ proj₁ ,  _⃗ ∘ proj₁ ]′ x) eq' refl) eq
... | refl = rs
getₜᵣ⃖ c {v} {v' ⃗} eq | inj₂ ((v'' , rs) , eq') with trans (subst (λ x → (v'' ⃗) ≡ [ _⃖ ∘ proj₁ ,  _⃗ ∘ proj₁ ]′ x) eq' refl) eq
... | refl = rs
getₜᵣ⃖ c {v} {v' ⃖} eq | inj₂ ((v'' , rs) , eq') with trans (subst (λ x → (v'' ⃗) ≡ [ _⃖ ∘ proj₁ ,  _⃗ ∘ proj₁ ]′ x) eq' refl) eq
... | ()

toState : ∀ {A B} → (c : A ↔ B) → Val B A → State
toState c (b ⃗) = ［ c ∣ b ∣ ☐ ］▷
toState c (a ⃖) = ⟨ c ∣ a ∣ ☐ ⟩◁

is-stuck-toState : ∀ {A B} → (c : A ↔ B) → (v : Val B A) → is-stuck (toState c v)
is-stuck-toState c (b ⃗) = λ ()
is-stuck-toState c (a ⃖) = λ ()

toStateEq₁ : ∀ {A B b} → (c : A ↔ B) → (x : Val B A) → ［ c ∣ b ∣ ☐ ］▷ ≡ toState c x → b ⃗ ≡ x
toStateEq₁ c (x ⃗) refl = refl

toStateEq₂ : ∀ {A B a} → (c : A ↔ B) → (x : Val B A) → ⟨ c ∣ a ∣ ☐ ⟩◁ ≡ toState c x → a ⃖ ≡ x
toStateEq₂ c (x ⃖) refl = refl

eval-toState₁ : ∀ {A B a x} {c : A ↔ B} → ⟨ c ∣ a ∣ ☐ ⟩▷ ↦* (toState c x) → eval c (a ⃗) ≡ x
eval-toState₁ {a = a} {b ⃗} {c} rs with inspect⊎ (run ⟨ c ∣ a ∣ ☐ ⟩▷) (λ ())
eval-toState₁ {a = a} {b ⃗} {c} rs | inj₁ ((a' , rs') , eq) with deterministic* rs rs' (λ ()) (λ ())
... | ()
eval-toState₁ {a = a} {b ⃗} {c} rs | inj₂ ((b' , rs') , eq) with deterministic* rs rs' (λ ()) (λ ())
... | refl = subst (λ x → [  _⃖ ∘ proj₁ ,  _⃗ ∘ proj₁ ]′ x ≡ b ⃗) eq refl
eval-toState₁ {a = a} {a' ⃖} {c} rs with inspect⊎ (run ⟨ c ∣ a ∣ ☐ ⟩▷) (λ ())
eval-toState₁ {a = a} {a' ⃖} {c} rs | inj₁ ((a'' , rs') , eq) with deterministic* rs rs' (λ ()) (λ ())
... | refl = subst (λ x → [  _⃖ ∘ proj₁ ,  _⃗ ∘ proj₁ ]′ x ≡ a'' ⃖) eq refl
eval-toState₁ {a = a} {a' ⃖} {c} rs | inj₂ ((b' , rs') , eq) with deterministic* rs rs' (λ ()) (λ ())
... | ()

eval-toState₂ : ∀ {A B b x} {c : A ↔ B} → ［ c ∣ b ∣ ☐ ］◁ ↦* (toState c x) → eval c (b ⃖) ≡ x
eval-toState₂ {b = b} {b' ⃗} {c} rs with inspect⊎ (run ［ c ∣ b ∣ ☐ ］◁) (λ ())
eval-toState₂ {b = b} {b' ⃗} {c} rs | inj₁ ((a' , rs') , eq) with deterministic* rs rs' (λ ()) (λ ())
... | ()
eval-toState₂ {b = b} {b' ⃗} {c} rs | inj₂ ((b'' , rs') , eq) with deterministic* rs rs' (λ ()) (λ ())
... | refl = subst (λ x → [  _⃖ ∘ proj₁ ,  _⃗ ∘ proj₁ ]′ x ≡ b'' ⃗) eq refl
eval-toState₂ {b = b} {a ⃖} {c} rs with inspect⊎ (run ［ c ∣ b ∣ ☐ ］◁) (λ ())
eval-toState₂ {b = b} {a ⃖} {c} rs | inj₁ ((a' , rs') , eq) with deterministic* rs rs' (λ ()) (λ ())
... | refl = subst (λ x → [  _⃖ ∘ proj₁ ,  _⃗ ∘ proj₁ ]′ x ≡ a' ⃖) eq refl
eval-toState₂ {b = b} {a ⃖} {c} rs | inj₂ ((b'' , rs') , eq) with deterministic* rs rs' (λ ()) (λ ())
... | ()

-- The abstract machine semantics is equivalent to the big-step semantics
module eval≡interp where
  mutual
    eval≡interp : ∀ {A B} → (c : A ↔ B) → (v : Val A B) → eval c v ≡ interp c v
    eval≡interp unite₊l (inj₂ v ⃗) = refl
    eval≡interp unite₊l (v ⃖) = refl
    eval≡interp uniti₊l (v ⃗) = refl
    eval≡interp uniti₊l (inj₂ v ⃖) = refl
    eval≡interp swap₊ (inj₁ x ⃗) = refl
    eval≡interp swap₊ (inj₂ y ⃗) = refl
    eval≡interp swap₊ (inj₁ x ⃖) = refl
    eval≡interp swap₊ (inj₂ y ⃖) = refl
    eval≡interp assocl₊ (inj₁ x ⃗) = refl
    eval≡interp assocl₊ (inj₂ (inj₁ y) ⃗) = refl
    eval≡interp assocl₊ (inj₂ (inj₂ z) ⃗) = refl
    eval≡interp assocl₊ (inj₁ (inj₁ x) ⃖) = refl
    eval≡interp assocl₊ (inj₁ (inj₂ y) ⃖) = refl
    eval≡interp assocl₊ (inj₂ z ⃖) = refl
    eval≡interp assocr₊ (inj₁ (inj₁ x) ⃗) = refl
    eval≡interp assocr₊ (inj₁ (inj₂ y) ⃗) = refl
    eval≡interp assocr₊ (inj₂ z ⃗) = refl
    eval≡interp assocr₊ (inj₁ x ⃖) = refl
    eval≡interp assocr₊ (inj₂ (inj₁ y) ⃖) = refl
    eval≡interp assocr₊ (inj₂ (inj₂ z) ⃖) = refl
    eval≡interp unite⋆l ((tt , v) ⃗) = refl
    eval≡interp unite⋆l (v ⃖) = refl
    eval≡interp uniti⋆l (v ⃗) = refl
    eval≡interp uniti⋆l ((tt , v) ⃖) = refl
    eval≡interp swap⋆ ((x , y) ⃗) = refl
    eval≡interp swap⋆ ((y , x) ⃖) = refl
    eval≡interp assocl⋆ ((x , (y , z)) ⃗) = refl
    eval≡interp assocl⋆ (((x , y) , z) ⃖) = refl
    eval≡interp assocr⋆ (((x , y) , z) ⃗) = refl
    eval≡interp assocr⋆ ((x , (y , z)) ⃖) = refl
    eval≡interp absorbr (() ⃗)
    eval≡interp absorbr (() ⃖)
    eval≡interp factorzl (() ⃗)
    eval≡interp factorzl (() ⃖)
    eval≡interp dist ((inj₁ x , z) ⃗) = refl
    eval≡interp dist ((inj₂ y , z) ⃗) = refl
    eval≡interp dist (inj₁ (x , z) ⃖) = refl
    eval≡interp dist (inj₂ (y , z) ⃖) = refl
    eval≡interp factor (inj₁ (x , z) ⃗) = refl
    eval≡interp factor (inj₂ (y , z) ⃗) = refl
    eval≡interp factor ((inj₁ x , z) ⃖) = refl
    eval≡interp factor ((inj₂ y , z) ⃖) = refl
    eval≡interp id↔ (v ⃗) = refl
    eval≡interp id↔ (v ⃖) = refl
    eval≡interp (c₁ ⨾ c₂) (a ⃗) with inspect⊎ (run ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩▷) (λ ()) | interp c₁ (a ⃗) | inspect (interp c₁) (a ⃗)
    eval≡interp (c₁ ⨾ c₂) (a ⃗) | inj₁ ((a' , rs) , eq) | b ⃗   | [ eq' ] = lem
      where
      rs' : ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩▷ ↦* (toState (c₁ ⨾ c₂) (c₁ ⨾[ b ⃗]⨾ c₂))
      rs' = loop₁⃗ c₁ b c₂ (↦⃗₃ ∷ appendκ↦* ((getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (a ⃗)) eq'))) refl (☐⨾ c₂ • ☐))

      lem : eval (c₁ ⨾ c₂) (a ⃗) ≡ (c₁ ⨾[ b ⃗]⨾ c₂)
      lem with deterministic* rs rs' (λ ()) (is-stuck-toState _ _)
      ... | eq' = subst (λ x → [  _⃖ ∘ proj₁ ,  _⃗ ∘ proj₁ ]′ x ≡ (c₁ ⨾[ b ⃗]⨾ c₂)) eq (toStateEq₂ (c₁ ⨾ c₂) (c₁ ⨾[ b ⃗]⨾ c₂) eq')
    eval≡interp (c₁ ⨾ c₂) (a ⃗) | inj₁ ((a' , rs) , eq) | a'' ⃖ | [ eq' ] = lem
      where
      rs' : ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⨾ c₂ ∣ a'' ∣ ☐ ⟩◁
      rs' = ↦⃗₃ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (a ⃗)) eq')) refl (☐⨾ c₂ • ☐) ++↦ ↦⃖₃ ∷ ◾

      lem : eval (c₁ ⨾ c₂) (a ⃗) ≡ a'' ⃖
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | refl = subst (λ x → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ x ≡ a' ⃖) eq refl
    eval≡interp (c₁ ⨾ c₂) (a ⃗) | inj₂ ((c , rs) , eq) | b ⃗  | [ eq' ] = lem
      where
      rs' : ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩▷ ↦* (toState (c₁ ⨾ c₂) (c₁ ⨾[ b ⃗]⨾ c₂))
      rs' = loop₁⃗ c₁ b c₂ (↦⃗₃ ∷ appendκ↦* ((getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (a ⃗)) eq'))) refl (☐⨾ c₂ • ☐))

      lem : eval (c₁ ⨾ c₂) (a ⃗) ≡ (c₁ ⨾[ b ⃗]⨾ c₂)
      lem with deterministic* rs rs' (λ ()) (is-stuck-toState _ _)
      ... | eq' = subst (λ x → [  _⃖ ∘ proj₁ , _⃗ ∘ proj₁ ]′ x ≡ (c₁ ⨾[ b ⃗]⨾ c₂)) eq (toStateEq₁ (c₁ ⨾ c₂) (c₁ ⨾[ b ⃗]⨾ c₂) eq')
    eval≡interp (c₁ ⨾ c₂) (a ⃗) | inj₂ ((c , rs) , eq) | a' ⃖ | [ eq' ] = lem
      where
      rs' : ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⨾ c₂ ∣ a' ∣ ☐ ⟩◁
      rs' = ↦⃗₃ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (a ⃗)) eq')) refl (☐⨾ c₂ • ☐) ++↦ ↦⃖₃ ∷ ◾

      lem : eval (c₁ ⨾ c₂) (a ⃗) ≡ a' ⃖
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | ()
    eval≡interp (c₁ ⨾ c₂) (c ⃖) with inspect⊎ (run ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］◁) (λ ()) | interp c₂ (c ⃖) | inspect (interp c₂) (c ⃖)
    eval≡interp (c₁ ⨾ c₂) (c ⃖) | inj₁ ((c' , rs) , eq) | (b ⃖)   | [ eq' ] = lem
      where
      rs' : ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］◁ ↦* (toState (c₁ ⨾ c₂) (c₁ ⨾[ b ⃖]⨾ c₂))
      rs' = loop₂⃖ c₁ b c₂ (↦⃖₁₀ ∷ appendκ↦* ((getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (c ⃖)) eq'))) refl (c₁ ⨾☐• ☐) ++↦ ↦⃖₇ ∷ ◾)

      lem : eval (c₁ ⨾ c₂) (c ⃖) ≡ (c₁ ⨾[ b ⃖]⨾ c₂)
      lem with deterministic* rs rs' (λ ()) (is-stuck-toState _ _)
      ... | eq' = subst (λ x → [ _⃖ ∘ proj₁ , _⃗ ∘ proj₁ ]′ x ≡ (c₁ ⨾[ b ⃖]⨾ c₂)) eq (toStateEq₂ (c₁ ⨾ c₂) (c₁ ⨾[ b ⃖]⨾ c₂) eq')
    eval≡interp (c₁ ⨾ c₂) (c ⃖) | inj₁ ((c' , rs) , eq) | (c'' ⃗) | [ eq' ] = lem
      where
      rs' : ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］◁ ↦* ［ c₁ ⨾ c₂ ∣ c'' ∣ ☐ ］▷
      rs' = ↦⃖₁₀ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (c ⃖)) eq')) refl (c₁ ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾

      lem : eval (c₁ ⨾ c₂) (c ⃖) ≡ c'' ⃗
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | ()
    eval≡interp (c₁ ⨾ c₂) (c ⃖) | inj₂ ((a  , rs) , eq) | (c' ⃗) | [ eq' ] = lem
      where
      rs' : ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］◁ ↦* ［ c₁ ⨾ c₂ ∣ c' ∣ ☐ ］▷
      rs' = ↦⃖₁₀ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (c ⃖)) eq')) refl (c₁ ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾

      lem : eval (c₁ ⨾ c₂) (c ⃖) ≡ c' ⃗
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | refl = subst (λ z → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ z ≡ c' ⃗) eq refl
    eval≡interp (c₁ ⨾ c₂) (c ⃖) | inj₂ ((a  , rs) , eq) | (b ⃖)  | [ eq' ] = lem
      where
      rs' : ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］◁ ↦* (toState (c₁ ⨾ c₂) (c₁ ⨾[ b ⃖]⨾ c₂))
      rs' = loop₂⃖ c₁ b c₂ (↦⃖₁₀ ∷ appendκ↦* ((getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (c ⃖)) eq'))) refl (c₁ ⨾☐• ☐) ++↦ ↦⃖₇ ∷ ◾)

      lem : eval (c₁ ⨾ c₂) (c ⃖) ≡ (c₁ ⨾[ b ⃖]⨾ c₂)
      lem with deterministic* rs rs' (λ ()) (is-stuck-toState _ _)
      ... | eq' = subst (λ x → [ _⃖ ∘ proj₁ , _⃗ ∘ proj₁ ]′ x ≡ (c₁ ⨾[ b ⃖]⨾ c₂)) eq (toStateEq₁ (c₁ ⨾ c₂) (c₁ ⨾[ b ⃖]⨾ c₂) eq')
    eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) with inspect⊎ (run ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷) (λ ()) | interp c₁ (x ⃗) | inspect (interp c₁) (x ⃗)
    eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) | inj₁ ((x' , rs) , eq) | x₁ ⃗ | [ eq' ] = lem
      where
      rs' : ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷ ↦* ［ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ］▷
      rs' = ↦⃗₄ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq')) refl (☐⊕ c₂ • ☐) ++↦ ↦⃗₁₁ ∷ ◾

      lem : eval (c₁ ⊕ c₂) (inj₁ x ⃗) ≡ inj₁ x₁ ⃗
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | ()
    eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) | inj₁ ((x' , rs) , eq) | x₁ ⃖ | [ eq' ] = lem
      where
      rs' : ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ⟩◁
      rs' = ↦⃗₄ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq')) refl (☐⊕ c₂ • ☐) ++↦ ↦⃖₄ ∷ ◾

      lem : eval (c₁ ⊕ c₂) (inj₁ x ⃗) ≡ inj₁ x₁ ⃖
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | refl = subst (λ x → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ x ≡ inj₁ x₁ ⃖) eq refl
    eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) | inj₂ ((x' , rs) , eq) | x₁ ⃗ | [ eq' ] = lem
      where
      rs' : ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷ ↦* ［ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ］▷
      rs' = ↦⃗₄ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq')) refl (☐⊕ c₂ • ☐) ++↦ ↦⃗₁₁ ∷ ◾

      lem : eval (c₁ ⊕ c₂) (inj₁ x ⃗) ≡ inj₁ x₁ ⃗
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | refl = subst (λ x → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ x ≡ inj₁ x₁ ⃗) eq refl
    eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) | inj₂ ((x' , rs) , eq) | x₁ ⃖ | [ eq' ] = lem
      where
      rs' : ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ⟩◁
      rs' = ↦⃗₄ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq')) refl (☐⊕ c₂ • ☐) ++↦ ↦⃖₄ ∷ ◾

      lem : eval (c₁ ⊕ c₂) (inj₁ x ⃗) ≡ inj₁ x₁ ⃖
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | ()
    eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) with inspect⊎ (run ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷) (λ ()) | interp c₂ (y ⃗) | inspect (interp c₂) (y ⃗)
    eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) | inj₁ ((y' , rs) , eq) | y₁ ⃗ | [ eq' ] = lem
      where
      rs' : ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷ ↦* ［ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ］▷
      rs' = ↦⃗₅ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq')) refl (c₁ ⊕☐• ☐) ++↦ ↦⃗₁₂ ∷ ◾

      lem : eval (c₁ ⊕ c₂) (inj₂ y ⃗) ≡ inj₂ y₁ ⃗
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | ()
    eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) | inj₁ ((y' , rs) , eq) | y₁ ⃖ | [ eq' ] = lem
      where
      rs' : ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ⟩◁
      rs' = ↦⃗₅ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq')) refl (c₁ ⊕☐• ☐) ++↦ ↦⃖₅ ∷ ◾

      lem : eval (c₁ ⊕ c₂) (inj₂ y ⃗) ≡ inj₂ y₁ ⃖
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | refl = subst (λ x → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ x ≡ inj₂ y₁ ⃖) eq refl
    eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) | inj₂ ((y' , rs) , eq) | y₁ ⃗ | [ eq' ] = lem
      where
      rs' : ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷ ↦* ［ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ］▷
      rs' = ↦⃗₅ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq')) refl (c₁ ⊕☐• ☐) ++↦ ↦⃗₁₂ ∷ ◾

      lem : eval (c₁ ⊕ c₂) (inj₂ y ⃗) ≡ inj₂ y₁ ⃗
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | refl = subst (λ x → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ x ≡ inj₂ y₁ ⃗) eq refl
    eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) | inj₂ ((y' , rs) , eq) | y₁ ⃖ | [ eq' ] = lem
      where
      rs' : ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ⟩◁
      rs' = ↦⃗₅ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq')) refl (c₁ ⊕☐• ☐) ++↦ ↦⃖₅ ∷ ◾

      lem : eval (c₁ ⊕ c₂) (inj₂ y ⃗) ≡ inj₂ y₁ ⃖
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | ()
    eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) with inspect⊎ (run ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁) (λ ()) | interp c₁ (x ⃖) | inspect (interp c₁) (x ⃖)
    eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) | inj₁ ((x' , rs) , eq) | x₁ ⃗ | [ eq' ] = lem
      where
      rs' : ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁ ↦* ［ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ］▷
      rs' = ↦⃖₁₁ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq')) refl (☐⊕ c₂ • ☐) ++↦ ↦⃗₁₁ ∷ ◾

      lem : eval (c₁ ⊕ c₂) (inj₁ x ⃖) ≡ inj₁ x₁ ⃗
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | ()
    eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) | inj₁ ((x' , rs) , eq) | x₁ ⃖ | [ eq' ] = lem
      where
      rs' : ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ⟩◁
      rs' = ↦⃖₁₁ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq')) refl (☐⊕ c₂ • ☐) ++↦ ↦⃖₄ ∷ ◾

      lem : eval (c₁ ⊕ c₂) (inj₁ x ⃖) ≡ inj₁ x₁ ⃖
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | refl = subst (λ x → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ x ≡ inj₁ x₁ ⃖) eq refl
    eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) | inj₂ ((x' , rs) , eq) | x₁ ⃗ | [ eq' ] = lem
      where
      rs' : ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁ ↦* ［ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ］▷
      rs' = ↦⃖₁₁ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq')) refl (☐⊕ c₂ • ☐) ++↦ ↦⃗₁₁ ∷ ◾

      lem : eval (c₁ ⊕ c₂) (inj₁ x ⃖) ≡ inj₁ x₁ ⃗
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | refl = subst (λ x → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ x ≡ inj₁ x₁ ⃗) eq refl
    eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) | inj₂ ((x' , rs) , eq) | x₁ ⃖ | [ eq' ] = lem
      where
      rs' : ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ⟩◁
      rs' = ↦⃖₁₁ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq')) refl (☐⊕ c₂ • ☐) ++↦ ↦⃖₄ ∷ ◾

      lem : eval (c₁ ⊕ c₂) (inj₁ x ⃖) ≡ inj₁ x₁ ⃖
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | ()
    eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) with inspect⊎ (run ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁) (λ ()) | interp c₂ (y ⃖) | inspect (interp c₂) (y ⃖)
    eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) | inj₁ ((y' , rs) , eq) | y₁ ⃖ | [ eq' ] = lem
      where
      rs' : ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ⟩◁
      rs' = ↦⃖₁₂ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq')) refl (c₁ ⊕☐• ☐) ++↦ ↦⃖₅ ∷ ◾

      lem : eval (c₁ ⊕ c₂) (inj₂ y ⃖) ≡ inj₂ y₁ ⃖
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | refl = subst (λ x → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ x ≡ inj₂ y₁ ⃖) eq refl
    eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) | inj₁ ((y' , rs) , eq) | y₁ ⃗ | [ eq' ] = lem
      where
      rs' : ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁ ↦* ［ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ］▷
      rs' = ↦⃖₁₂ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq')) refl (c₁ ⊕☐• ☐) ++↦ ↦⃗₁₂ ∷ ◾

      lem : eval (c₁ ⊕ c₂) (inj₂ y ⃖) ≡ inj₂ y₁ ⃗
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | ()
    eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) | inj₂ ((y' , rs) , eq) | y₁ ⃖ | [ eq' ] = lem
      where
      rs' : ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ⟩◁
      rs' = ↦⃖₁₂ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq')) refl (c₁ ⊕☐• ☐) ++↦ ↦⃖₅ ∷ ◾

      lem : eval (c₁ ⊕ c₂) (inj₂ y ⃖) ≡ inj₂ y₁ ⃖
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | ()
    eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) | inj₂ ((y' , rs) , eq) | y₁ ⃗ | [ eq' ] = lem
      where
      rs' : ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁ ↦* ［ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ］▷
      rs' = ↦⃖₁₂ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq')) refl (c₁ ⊕☐• ☐) ++↦ ↦⃗₁₂ ∷ ◾

      lem : eval (c₁ ⊕ c₂) (inj₂ y ⃖) ≡ inj₂ y₁ ⃗
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | refl = subst (λ x → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ x ≡ inj₂ y₁ ⃗) eq refl
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) with inspect⊎ (run ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷) (λ ()) | interp c₁ (x ⃗) | inspect (interp c₁) (x ⃗)
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₁ (((x' , y') , rs) , eq) | x₁ ⃗ | [ eq₁ ] with interp c₂ (y ⃗) | inspect (interp c₂) (y ⃗)
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₁ (((x' , y') , rs) , eq) | x₁ ⃗ | [ eq₁ ] | y₁ ⃗ | [ eq₂ ] = lem
      where
      rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ［ c₁ ⊗ c₂ ∣ (x₁ , y₁) ∣ ☐ ］▷
      rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) refl (☐⊗[ c₂ , y ]• ☐) ++↦
            ↦⃗₈ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₂)) refl ([ c₁ , x₁ ]⊗☐• ☐) ++↦ ↦⃗₉ ∷ ◾

      lem : eval (c₁ ⊗ c₂) ((x , y) ⃗) ≡ (x₁ , y₁) ⃗
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | ()
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₁ (((x' , y') , rs) , eq) | x₁ ⃗ | [ eq₁ ] | y₁ ⃖ | [ eq₂ ] = lem
      where
      rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊗ c₂ ∣ (x , y₁) ∣ ☐ ⟩◁
      rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) refl (☐⊗[ c₂ , y ]• ☐) ++↦
            ↦⃗₈ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₂)) refl ([ c₁ , x₁ ]⊗☐• ☐) ++↦
            ↦⃖₈ ∷ Rev* (appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) refl (☐⊗[ c₂ , y₁ ]• ☐)) ++↦ ↦⃖₆ ∷ ◾

      lem : eval (c₁ ⊗ c₂) ((x , y) ⃗) ≡ (x , y₁) ⃖
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | refl = subst (λ z → [ _⃖ ∘ proj₁ , _⃗ ∘ proj₁ ]′ z ≡ (x , y₁) ⃖) eq refl
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₁ (((x' , y') , rs) , eq) | x₁ ⃖ | [ eq₁ ] = lem
      where
      rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊗ c₂ ∣ (x₁ , y) ∣ ☐ ⟩◁
      rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) refl (☐⊗[ c₂ , y ]• ☐) ++↦ ↦⃖₆ ∷ ◾

      lem : eval (c₁ ⊗ c₂) ((x , y) ⃗) ≡ (x₁ , y) ⃖
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | refl = subst (λ x → [ _⃖ ∘ proj₁ , _⃗ ∘ proj₁ ]′ x ≡ (x₁ , y) ⃖) eq refl
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₂ (((x' , y') , rs) , eq) | x₁ ⃗ | [ eq₁ ] with interp c₂ (y ⃗) | inspect (interp c₂) (y ⃗)
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₂ (((x' , y') , rs) , eq) | x₁ ⃗ | [ eq₁ ] | y₁ ⃗ | [ eq₂ ] = lem
      where
      rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ［ c₁ ⊗ c₂ ∣ (x₁ , y₁) ∣ ☐ ］▷
      rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) refl (☐⊗[ c₂ , y ]• ☐) ++↦
            ↦⃗₈ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₂)) refl ([ c₁ , x₁ ]⊗☐• ☐) ++↦ ↦⃗₉ ∷ ◾

      lem : eval (c₁ ⊗ c₂) ((x , y) ⃗) ≡ (x₁ , y₁) ⃗
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | refl = subst (λ z → [ _⃖ ∘ proj₁ , _⃗ ∘ proj₁ ]′ z ≡ (x₁ , y₁) ⃗) eq refl
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₂ (((x' , y') , rs) , eq) | x₁ ⃗ | [ eq₁ ] | y₁ ⃖ | [ eq₂ ] = lem
      where
      rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊗ c₂ ∣ (x , y₁) ∣ ☐ ⟩◁
      rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) refl (☐⊗[ c₂ , y ]• ☐) ++↦
            ↦⃗₈ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₂)) refl ([ c₁ , x₁ ]⊗☐• ☐) ++↦
            ↦⃖₈ ∷ Rev* (appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) refl (☐⊗[ c₂ , y₁ ]• ☐)) ++↦ ↦⃖₆ ∷ ◾

      lem : eval (c₁ ⊗ c₂) ((x , y) ⃗) ≡ (x , y₁) ⃖
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | ()
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₂ (((x' , y') , rs) , eq) | x₁ ⃖ | [ eq₁ ] = lem
      where
      rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊗ c₂ ∣ (x₁ , y) ∣ ☐ ⟩◁
      rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) refl (☐⊗[ c₂ , y ]• ☐) ++↦ ↦⃖₆ ∷ ◾

      lem : eval (c₁ ⊗ c₂) ((x , y) ⃗) ≡ (x₁ , y) ⃖
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | ()
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) with inspect⊎ (run ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁) (λ ()) | interp c₂ (y ⃖) | inspect (interp c₂) (y ⃖)
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₁ (((x' , y') , rs) , eq) | y₁ ⃗ | [ eq₂ ] = lem
      where
      rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ［ c₁ ⊗ c₂ ∣ (x , y₁) ∣ ☐ ］▷
      rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) refl ([ c₁ , x ]⊗☐• ☐) ++↦ ↦⃗₉ ∷ ◾

      lem : eval (c₁ ⊗ c₂) ((x , y) ⃖) ≡ (x , y₁) ⃗
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | ()
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₁ (((x' , y') , rs) , eq) | y₁ ⃖ | [ eq₂ ] with interp c₁ (x ⃖) | inspect (interp c₁) (x ⃖)
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₁ (((x' , y') , rs) , eq) | y₁ ⃖ | [ eq₂ ] | x₁ ⃗ | [ eq₁ ] = lem
      where
      rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ［ c₁ ⊗ c₂ ∣ (x₁ , y) ∣ ☐ ］▷
      rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) refl ([ c₁ , x ]⊗☐• ☐) ++↦
            ↦⃖₈ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) refl (☐⊗[ c₂ , y₁ ]• ☐) ++↦
            ↦⃗₈ ∷ Rev* (appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) refl ([ c₁ , x₁ ]⊗☐• ☐)) ++↦ ↦⃗₉ ∷ ◾

      lem : eval (c₁ ⊗ c₂) ((x , y) ⃖) ≡ (x₁ , y) ⃗
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | ()
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₁ (((x' , y') , rs) , eq) | y₁ ⃖ | [ eq₂ ] | x₁ ⃖ | [ eq₁ ] = lem
      where
      rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ⟨ c₁ ⊗ c₂ ∣ (x₁ , y₁) ∣ ☐ ⟩◁
      rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) refl ([ c₁ , x ]⊗☐• ☐) ++↦
            ↦⃖₈ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) refl (☐⊗[ c₂ , y₁ ]• ☐) ++↦ ↦⃖₆ ∷ ◾

      lem : eval (c₁ ⊗ c₂) ((x , y) ⃖) ≡ (x₁ , y₁) ⃖
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | refl = subst (λ z → [ _⃖ ∘ proj₁ , _⃗ ∘ proj₁ ]′ z ≡ (x₁ , y₁) ⃖) eq refl
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₂ (((x' , y') , rs) , eq) | y₁ ⃗ | [ eq₂ ] = lem
      where
      rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ［ c₁ ⊗ c₂ ∣ (x , y₁) ∣ ☐ ］▷
      rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) refl ([ c₁ , x ]⊗☐• ☐) ++↦ ↦⃗₉ ∷ ◾

      lem : eval (c₁ ⊗ c₂) ((x , y) ⃖) ≡ (x , y₁) ⃗
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | refl = subst (λ z → [ _⃖ ∘ proj₁ , _⃗ ∘ proj₁ ]′ z ≡ (x , y₁) ⃗) eq refl
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₂ (((x' , y') , rs) , eq) | y₁ ⃖ | [ eq₂ ] with interp c₁ (x ⃖) | inspect (interp c₁) (x ⃖)
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₂ (((x' , y') , rs) , eq) | y₁ ⃖ | [ eq₂ ] | x₁ ⃗ | [ eq₁ ] = lem
      where
      rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ［ c₁ ⊗ c₂ ∣ (x₁ , y) ∣ ☐ ］▷
      rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) refl ([ c₁ , x ]⊗☐• ☐) ++↦
            ↦⃖₈ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) refl (☐⊗[ c₂ , y₁ ]• ☐) ++↦
            ↦⃗₈ ∷ Rev* (appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) refl ([ c₁ , x₁ ]⊗☐• ☐)) ++↦ ↦⃗₉ ∷ ◾

      lem : eval (c₁ ⊗ c₂) ((x , y) ⃖) ≡ (x₁ , y) ⃗
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | refl = subst (λ z → [ _⃖ ∘ proj₁ , _⃗ ∘ proj₁ ]′ z ≡ (x₁ , y) ⃗) eq refl
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₂ (((x' , y') , rs) , eq) | y₁ ⃖ | [ eq₂ ] | x₁ ⃖ | [ eq₁ ] = lem
      where
      rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ⟨ c₁ ⊗ c₂ ∣ (x₁ , y₁) ∣ ☐ ⟩◁
      rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) refl ([ c₁ , x ]⊗☐• ☐) ++↦
            ↦⃖₈ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) refl (☐⊗[ c₂ , y₁ ]• ☐) ++↦ ↦⃖₆ ∷ ◾

      lem : eval (c₁ ⊗ c₂) ((x , y) ⃖) ≡ (x₁ , y₁) ⃖
      lem with deterministic* rs rs' (λ ()) (λ ())
      ... | ()
    eval≡interp η₊ (inj₁ x ⃖) = refl
    eval≡interp η₊ (inj₂ (- x) ⃖) = refl
    eval≡interp ε₊ (inj₁ x ⃗) = refl
    eval≡interp ε₊ (inj₂ (- x) ⃗) = refl

    -- Termination is guarantee by Pi-.NoRepeat:
    -- The execution trace in the argument will grow in every mutual recursive call, but it can only has finite length.
    private
      {-# TERMINATING #-}
      loop₁⃗ : ∀ {A B C a₀} → (c₁ : A ↔ B) → (b : ⟦ B ⟧) → (c₂ : B ↔ C)
             → ⟨ c₁ ⨾ c₂ ∣ a₀ ∣ ☐ ⟩▷ ↦* ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷
             → ⟨ c₁ ⨾ c₂ ∣ a₀ ∣ ☐ ⟩▷ ↦* (toState (c₁ ⨾ c₂) (c₁ ⨾[ b ⃗]⨾ c₂))
      loop₁⃗ c₁ b c₂ rsₐ with interp c₂ (b ⃗) | inspect (interp c₂) (b ⃗)
      loop₁⃗ c₁ b c₂ rsₐ | c ⃗  | [ eq ] = rsₐ ++↦ (↦⃗₇ ∷ ◾) ++↦ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (b ⃗)) eq)) refl (c₁ ⨾☐• ☐) ++↦ (↦⃗₁₀ ∷ ◾)
      loop₁⃗ c₁ b c₂ rsₐ | b' ⃖ | [ eq ] = loop₂⃗ c₁ b' c₂ (rsₐ ++↦ (↦⃗₇ ∷ ◾) ++↦ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (b ⃗)) eq)) refl (c₁ ⨾☐• ☐) ++↦ (↦⃖₇ ∷ ◾))

      loop₂⃗ : ∀ {A B C a₀} → (c₁ : A ↔ B) → (b : ⟦ B ⟧) → (c₂ : B ↔ C)
            → ⟨ c₁ ⨾ c₂ ∣ a₀ ∣ ☐ ⟩▷ ↦* ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］◁
            → ⟨ c₁ ⨾ c₂ ∣ a₀ ∣ ☐ ⟩▷ ↦* (toState (c₁ ⨾ c₂) (c₁ ⨾[ b ⃖]⨾ c₂))
      loop₂⃗ c₁ b c₂ rsₐ with interp c₁ (b ⃖) | inspect (interp c₁) (b ⃖)
      loop₂⃗ c₁ b c₂ rsₐ | b' ⃗ | [ eq ] = loop₁⃗ c₁ b' c₂ (rsₐ ++↦ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (b ⃖)) eq)) refl (☐⨾ c₂ • ☐))
      loop₂⃗ c₁ b c₂ rsₐ | a' ⃖ | [ eq ] = rsₐ ++↦ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (b ⃖)) eq)) refl (☐⨾ c₂ • ☐) ++↦ (↦⃖₃ ∷ ◾)

      loop₁⃖ : ∀ {A B C c₀} → (c₁ : A ↔ B) → (b : ⟦ B ⟧) → (c₂ : B ↔ C)
             → ［ c₁ ⨾ c₂ ∣ c₀ ∣ ☐ ］◁ ↦* ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷
             → ［ c₁ ⨾ c₂ ∣ c₀ ∣ ☐ ］◁ ↦* (toState (c₁ ⨾ c₂) (c₁ ⨾[ b ⃗]⨾ c₂))
      loop₁⃖ c₁ b c₂ rsₐ with interp c₂ (b ⃗) | inspect (interp c₂) (b ⃗)
      loop₁⃖ c₁ b c₂ rsₐ | c ⃗  | [ eq ] = rsₐ ++↦ (↦⃗₇ ∷ ◾) ++↦ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (b ⃗)) eq)) refl (c₁ ⨾☐• ☐) ++↦ (↦⃗₁₀ ∷ ◾)
      loop₁⃖ c₁ b c₂ rsₐ | b' ⃖ | [ eq ] = loop₂⃖ c₁ b' c₂ (rsₐ ++↦ (↦⃗₇ ∷ ◾) ++↦ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (b ⃗)) eq)) refl (c₁ ⨾☐• ☐) ++↦ (↦⃖₇ ∷ ◾))

      loop₂⃖ : ∀ {A B C c₀} → (c₁ : A ↔ B) → (b : ⟦ B ⟧) → (c₂ : B ↔ C)
            → ［ c₁ ⨾ c₂ ∣ c₀ ∣ ☐ ］◁ ↦* ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］◁
            → ［ c₁ ⨾ c₂ ∣ c₀ ∣ ☐ ］◁ ↦* (toState (c₁ ⨾ c₂) (c₁ ⨾[ b ⃖]⨾ c₂))
      loop₂⃖ c₁ b c₂ rsₐ with interp c₁ (b ⃖) | inspect (interp c₁) (b ⃖)
      loop₂⃖ c₁ b c₂ rsₐ | b' ⃗  | [ eq ] = loop₁⃖ c₁ b' c₂ (rsₐ ++↦ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (b ⃖)) eq)) refl (☐⨾ c₂ • ☐))
      loop₂⃖ c₁ b c₂ rsₐ | a' ⃖  | [ eq ] = rsₐ ++↦ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (b ⃖)) eq)) refl (☐⨾ c₂ • ☐) ++↦ (↦⃖₃ ∷ ◾)

open eval≡interp public

module ∘-resp-≈ {A B C : 𝕌} {g i : B ↔ C} {f h : A ↔ B} (g~i : eval g ∼ eval i) (f~h : eval f ∼ eval h) where
  mutual
    ∘-resp-≈ : eval (f ⨾ g) ∼ eval (h ⨾ i)
    ∘-resp-≈ (a ⃗) with inspect⊎ (run ⟨ f ∣ a ∣ ☐ ⟩▷) (λ ())
    ∘-resp-≈ (a ⃗) | inj₁ ((a₁ , rs₁) , eq₁) = lem
      where
      eq : eval h (a ⃗) ≡ (a₁ ⃖)
      eq = trans (sym (f~h (a ⃗))) (subst (λ z → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ z ≡ (a₁ ⃖)) eq₁ refl)

      rs₁' : ⟨ f ⨾ g ∣ a ∣ ☐ ⟩▷ ↦* ⟨ f ⨾ g ∣ a₁ ∣ ☐ ⟩◁
      rs₁' = ↦⃗₃ ∷ appendκ↦* rs₁ refl (☐⨾ g • ☐) ++↦ ↦⃖₃ ∷ ◾

      rs₂' : ⟨ h ⨾ i ∣ a ∣ ☐ ⟩▷ ↦* ⟨ h ⨾ i ∣ a₁ ∣ ☐ ⟩◁
      rs₂' = ↦⃗₃ ∷ appendκ↦* (getₜᵣ⃗ h eq) refl (☐⨾ i • ☐) ++↦ ↦⃖₃ ∷ ◾

      lem : eval (f ⨾ g) (a ⃗) ≡ eval (h ⨾ i) (a ⃗)
      lem rewrite eval-toState₁ rs₁' | eval-toState₁ rs₂' | eq = refl
    ∘-resp-≈ (a ⃗) | inj₂ ((b₁ , rs₁) , eq₁) = lem
      where
      eq : eval h (a ⃗) ≡ (b₁ ⃗)
      eq = trans (sym (f~h (a ⃗))) (subst (λ z → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ z ≡ (b₁ ⃗)) eq₁ refl)

      rs₁' : ⟨ f ⨾ g ∣ a ∣ ☐ ⟩▷ ↦* ［ f ∣ b₁ ∣ ☐⨾ g • ☐ ］▷
      rs₁' = ↦⃗₃ ∷ appendκ↦* rs₁ refl (☐⨾ g • ☐)

      rs₂' : ⟨ h ⨾ i ∣ a ∣ ☐ ⟩▷ ↦* ［ h ∣ b₁ ∣ ☐⨾ i • ☐ ］▷
      rs₂' = ↦⃗₃ ∷ appendκ↦* (getₜᵣ⃗ h eq) refl (☐⨾ i • ☐)

      lem : eval (f ⨾ g) (a ⃗) ≡ eval (h ⨾ i) (a ⃗)
      lem with Loop₁⃗ (rs₁' , rs₂')
      ... | (x , rs₁'' , rs₂'') rewrite eval-toState₁ rs₁'' | eval-toState₁ rs₂'' = refl
    ∘-resp-≈ (c ⃖) with inspect⊎ (run ［ g ∣ c ∣ ☐ ］◁) (λ ())
    ∘-resp-≈ (c ⃖) | inj₁ ((b₁ , rs₁) , eq₁) = lem
      where
      eq : eval i (c ⃖) ≡ (b₁ ⃖)
      eq = trans (sym (g~i (c ⃖))) (subst (λ z → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ z ≡ (b₁ ⃖)) eq₁ refl)

      rs₁' : ［ f ⨾ g ∣ c ∣ ☐ ］◁ ↦* ［ f ∣ b₁ ∣ ☐⨾ g • ☐ ］◁
      rs₁' = ↦⃖₁₀ ∷ appendκ↦* rs₁ refl (f ⨾☐• ☐) ++↦ ↦⃖₇ ∷ ◾

      rs₂' : ［ h ⨾ i ∣ c ∣ ☐ ］◁ ↦* ［ h ∣ b₁ ∣ ☐⨾ i • ☐ ］◁
      rs₂' = ↦⃖₁₀ ∷ appendκ↦* (getₜᵣ⃖ i eq) refl (h ⨾☐• ☐) ++↦ ↦⃖₇ ∷ ◾

      lem : eval (f ⨾ g) (c ⃖) ≡ eval (h ⨾ i) (c ⃖)
      lem with Loop₁⃖ (rs₁' , rs₂')
      ... | (x , rs₁'' , rs₂'') rewrite eval-toState₂ rs₁'' | eval-toState₂ rs₂'' = refl
    ∘-resp-≈ (c ⃖) | inj₂ ((c₁ , rs₁) , eq₁) = lem
      where
      eq : eval i (c ⃖) ≡ (c₁ ⃗)
      eq = trans (sym (g~i (c ⃖))) (subst (λ z → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ z ≡ (c₁ ⃗)) eq₁ refl)

      rs₁' : ［ f ⨾ g ∣ c ∣ ☐ ］◁ ↦* ［ f ⨾ g ∣ c₁ ∣ ☐ ］▷
      rs₁' = ↦⃖₁₀ ∷ appendκ↦* rs₁ refl (f ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾

      rs₂' : ［ h ⨾ i ∣ c ∣ ☐ ］◁ ↦* ［ h ⨾ i ∣ c₁ ∣ ☐ ］▷
      rs₂' = ↦⃖₁₀ ∷ appendκ↦* (getₜᵣ⃖ i eq) refl (h ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾

      lem : eval (f ⨾ g) (c ⃖) ≡ eval (h ⨾ i) (c ⃖)
      lem rewrite eval-toState₂ rs₁' | eval-toState₂ rs₂' | eq = refl

    private
      {-# TERMINATING #-}
      Loop₁⃗ : {a₀ : ⟦ A ⟧} {b : ⟦ B ⟧}
             → ⟨ f ⨾ g ∣ a₀ ∣ ☐ ⟩▷ ↦* ［ f ∣ b ∣ ☐⨾ g • ☐ ］▷
             × ⟨ h ⨾ i ∣ a₀ ∣ ☐ ⟩▷ ↦* ［ h ∣ b ∣ ☐⨾ i • ☐ ］▷
             → Σ[ x ∈ Val C A ]
               ⟨ f ⨾ g ∣ a₀ ∣ ☐ ⟩▷ ↦* toState (f ⨾ g) x
             × ⟨ h ⨾ i ∣ a₀ ∣ ☐ ⟩▷ ↦* toState (h ⨾ i) x
      Loop₁⃗ {a₀} {b} (ts₁ , ts₂) with inspect⊎ (run ⟨ g ∣ b ∣ ☐ ⟩▷) (λ ())
      Loop₁⃗ {a₀} {b} (ts₁ , ts₂) | inj₁ ((b₁ , rs₁) , eq₁) = Loop₂⃗ ( ts₁ ++↦ ↦⃗₇ ∷ appendκ↦* rs₁ refl (f ⨾☐• ☐) ++↦ ↦⃖₇ ∷ ◾
                                                                     , ts₂ ++↦ ↦⃗₇ ∷ appendκ↦* rs₂ refl (h ⨾☐• ☐) ++↦ ↦⃖₇ ∷ ◾)
        where
        eq : eval i (b ⃗) ≡ (b₁ ⃖)
        eq = trans (sym (g~i (b ⃗))) (subst (λ z → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ z ≡ (b₁ ⃖)) eq₁ refl)

        rs₂ : ⟨ i ∣ b ∣ ☐ ⟩▷ ↦* ⟨ i ∣ b₁ ∣ ☐ ⟩◁
        rs₂ = getₜᵣ⃗ i eq
      Loop₁⃗ {a₀} {b} (ts₁ , ts₂) | inj₂ ((c₁ , rs₁) , eq₁) = c₁ ⃗ , ts₁ ++↦ ↦⃗₇ ∷ appendκ↦* rs₁ refl (f ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾
                                                                   , ts₂ ++↦ ↦⃗₇ ∷ appendκ↦* rs₂ refl (h ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾
        where
        eq : eval i (b ⃗) ≡ (c₁ ⃗)
        eq = trans (sym (g~i (b ⃗))) (subst (λ z → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ z ≡ (c₁ ⃗)) eq₁ refl)

        rs₂ : ⟨ i ∣ b ∣ ☐ ⟩▷ ↦* ［ i ∣ c₁ ∣ ☐ ］▷
        rs₂ = getₜᵣ⃗ i eq

      Loop₂⃗ : {a₀ : ⟦ A ⟧} {b : ⟦ B ⟧}
             → ⟨ f ⨾ g ∣ a₀ ∣ ☐ ⟩▷ ↦* ［ f ∣ b ∣ ☐⨾ g • ☐ ］◁
             × ⟨ h ⨾ i ∣ a₀ ∣ ☐ ⟩▷ ↦* ［ h ∣ b ∣ ☐⨾ i • ☐ ］◁
             → Σ[ x ∈ Val C A ]
               ⟨ f ⨾ g ∣ a₀ ∣ ☐ ⟩▷ ↦* toState (f ⨾ g) x
             × ⟨ h ⨾ i ∣ a₀ ∣ ☐ ⟩▷ ↦* toState (h ⨾ i) x
      Loop₂⃗ {a₀} {b} (ts₁ , ts₂) with inspect⊎ (run ［ f ∣ b ∣ ☐ ］◁) (λ ())
      Loop₂⃗ {a₀} {b} (ts₁ , ts₂) | inj₁ ((a₁ , rs₁) , eq₁) = a₁ ⃖ , ts₁ ++↦ appendκ↦* rs₁ refl (☐⨾ g • ☐) ++↦ ↦⃖₃ ∷ ◾
                                                                   , ts₂ ++↦ appendκ↦* rs₂ refl (☐⨾ i • ☐) ++↦ ↦⃖₃ ∷ ◾
        where
        eq : eval h (b ⃖) ≡ (a₁ ⃖)
        eq = trans (sym (f~h (b ⃖))) (subst (λ z → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ z ≡ (a₁ ⃖)) eq₁ refl)

        rs₂ : ［ h ∣ b ∣ ☐ ］◁ ↦* ⟨ h ∣ a₁ ∣ ☐ ⟩◁
        rs₂ = getₜᵣ⃖ h eq
      Loop₂⃗ {a₀} {b} (ts₁ , ts₂) | inj₂ ((b₁ , rs₁) , eq₁) = Loop₁⃗ ( ts₁ ++↦ appendκ↦* rs₁ refl (☐⨾ g • ☐)
                                                                     , ts₂ ++↦ appendκ↦* rs₂ refl (☐⨾ i • ☐))
        where
        eq : eval h (b ⃖) ≡ (b₁ ⃗)
        eq = trans (sym (f~h (b ⃖))) (subst (λ z → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ z ≡ (b₁ ⃗)) eq₁ refl)

        rs₂ : ［ h ∣ b ∣ ☐ ］◁ ↦* ［ h ∣ b₁ ∣ ☐ ］▷
        rs₂ = getₜᵣ⃖ h eq

      Loop₁⃖ : {c₀ : ⟦ C ⟧} {b : ⟦ B ⟧}
             → ［ f ⨾ g ∣ c₀ ∣ ☐ ］◁ ↦* ［ f ∣ b ∣ ☐⨾ g • ☐ ］◁
             × ［ h ⨾ i ∣ c₀ ∣ ☐ ］◁ ↦* ［ h ∣ b ∣ ☐⨾ i • ☐ ］◁
             → Σ[ x ∈ Val C A ]
               ［ f ⨾ g ∣ c₀ ∣ ☐ ］◁ ↦* toState (f ⨾ g) x
             × ［ h ⨾ i ∣ c₀ ∣ ☐ ］◁ ↦* toState (h ⨾ i) x
      Loop₁⃖ {c₀} {b} (ts₁ , ts₂) with inspect⊎ (run ［ f ∣ b ∣ ☐ ］◁) (λ ())
      Loop₁⃖ {c₀} {b} (ts₁ , ts₂) | inj₁ ((a₁ , rs₁) , eq₁) = a₁ ⃖ , ts₁ ++↦ appendκ↦* rs₁ refl (☐⨾ g • ☐) ++↦ ↦⃖₃ ∷ ◾
                                                                   , ts₂ ++↦ appendκ↦* rs₂ refl (☐⨾ i • ☐) ++↦ ↦⃖₃ ∷ ◾
        where
        eq : eval h (b ⃖) ≡ (a₁ ⃖)
        eq = trans (sym (f~h (b ⃖))) (subst (λ z → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ z ≡ (a₁ ⃖)) eq₁ refl)
        
        rs₂ : ［ h ∣ b ∣ ☐ ］◁ ↦* ⟨ h ∣ a₁ ∣ ☐ ⟩◁
        rs₂ = getₜᵣ⃖ h eq
      Loop₁⃖ {c₀} {b} (ts₁ , ts₂) | inj₂ ((b₁ , rs₁) , eq₁) = Loop₂⃖ ( ts₁ ++↦ appendκ↦* rs₁ refl (☐⨾ g • ☐)
                                                                     , ts₂ ++↦ appendκ↦* rs₂ refl (☐⨾ i • ☐))
        where
        eq : eval h (b ⃖) ≡ (b₁ ⃗)
        eq = trans (sym (f~h (b ⃖))) (subst (λ z → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ z ≡ (b₁ ⃗)) eq₁ refl)
        
        rs₂ : ［ h ∣ b ∣ ☐ ］◁ ↦* ［ h ∣ b₁ ∣ ☐ ］▷
        rs₂ = getₜᵣ⃖ h eq

      Loop₂⃖ : {c₀ : ⟦ C ⟧} {b : ⟦ B ⟧}
             → ［ f ⨾ g ∣ c₀ ∣ ☐ ］◁ ↦* ［ f ∣ b ∣ ☐⨾ g • ☐ ］▷
             × ［ h ⨾ i ∣ c₀ ∣ ☐ ］◁ ↦* ［ h ∣ b ∣ ☐⨾ i • ☐ ］▷
             → Σ[ x ∈ Val C A ]
               ［ f ⨾ g ∣ c₀ ∣ ☐ ］◁ ↦* toState (f ⨾ g) x
             × ［ h ⨾ i ∣ c₀ ∣ ☐ ］◁ ↦* toState (h ⨾ i) x
      Loop₂⃖ {c₀} {b} (ts₁ , ts₂) with inspect⊎ (run ⟨ g ∣ b ∣ ☐ ⟩▷) (λ ())
      Loop₂⃖ {c₀} {b} (ts₁ , ts₂) | inj₁ ((b₁ , rs₁) , eq₁) = Loop₁⃖ ( ts₁ ++↦ ↦⃗₇ ∷ appendκ↦* rs₁ refl (f ⨾☐• ☐) ++↦ ↦⃖₇ ∷ ◾
                                                                     , ts₂ ++↦ ↦⃗₇ ∷ appendκ↦* rs₂ refl (h ⨾☐• ☐) ++↦ ↦⃖₇ ∷ ◾)
        where
        eq : eval i (b ⃗) ≡ (b₁ ⃖)
        eq = trans (sym (g~i (b ⃗))) (subst (λ z → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ z ≡ (b₁ ⃖)) eq₁ refl)

        rs₂ : ⟨ i ∣ b ∣ ☐ ⟩▷ ↦* ⟨ i ∣ b₁ ∣ ☐ ⟩◁
        rs₂ = getₜᵣ⃗ i eq
      Loop₂⃖ {c₀} {b} (ts₁ , ts₂) | inj₂ ((c₁ , rs₁) , eq₁) = c₁ ⃗ , ts₁ ++↦ ↦⃗₇ ∷ appendκ↦* rs₁ refl (f ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾
                                                                   , ts₂ ++↦ ↦⃗₇ ∷ appendκ↦* rs₂ refl (h ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾
        where
        eq : eval i (b ⃗) ≡ (c₁ ⃗)
        eq = trans (sym (g~i (b ⃗))) (subst (λ z → [ (λ x → proj₁ x ⃖) , (λ x → proj₁ x ⃗) ]′ z ≡ (c₁ ⃗)) eq₁ refl)

        rs₂ : ⟨ i ∣ b ∣ ☐ ⟩▷ ↦* ［ i ∣ c₁ ∣ ☐ ］▷
        rs₂ = getₜᵣ⃗ i eq

open ∘-resp-≈ public

module ∘-resp-≈ᵢ {A B C : 𝕌} {g i : B ↔ C} {f h : A ↔ B} (g~i : interp g ∼ interp i) (f~h : interp f ∼ interp h) where
  ∘-resp-≈ᵢ : interp (f ⨾ g) ∼ interp (h ⨾ i)
  ∘-resp-≈ᵢ x = trans  (sym (eval≡interp (f ⨾ g) x))
                (trans (∘-resp-≈ (λ z → trans (eval≡interp g z) (trans (g~i z) (sym (eval≡interp i z))))
                                 (λ z → trans (eval≡interp f z) (trans (f~h z) (sym (eval≡interp h z)))) x)
                       (eval≡interp (h ⨾ i) x))
open ∘-resp-≈ᵢ public

module assoc {A B C D : 𝕌} {f : A ↔ B} {g : B ↔ C} {h : C ↔ D} where
  mutual
    assoc : eval (f ⨾ g ⨾ h) ∼ eval ((f ⨾ g) ⨾ h)
    assoc (a ⃗) with inspect⊎ (run ⟨ f ∣ a ∣ ☐ ⟩▷) (λ ())
    assoc (a ⃗) | inj₁ ((a₁ , rs₁) , eq₁) = lem
      where
      rs₁' : ⟨ f ⨾ (g ⨾ h) ∣ a ∣ ☐ ⟩▷ ↦* ⟨ f ⨾ (g ⨾ h) ∣ a₁ ∣ ☐ ⟩◁
      rs₁' = ↦⃗₃ ∷ appendκ↦* rs₁ refl (☐⨾ g ⨾ h • ☐) ++↦ ↦⃖₃ ∷ ◾

      rs₂' : ⟨ (f ⨾ g) ⨾ h ∣ a ∣ ☐ ⟩▷ ↦* ⟨ (f ⨾ g) ⨾ h ∣ a₁ ∣ ☐ ⟩◁
      rs₂' = (↦⃗₃ ∷ ↦⃗₃ ∷ ◾) ++↦ appendκ↦* rs₁ refl (☐⨾ g • ☐⨾ h • ☐) ++↦ ↦⃖₃ ∷ ↦⃖₃ ∷ ◾

      lem : eval (f ⨾ g ⨾ h) (a ⃗) ≡ eval ((f ⨾ g) ⨾ h) (a ⃗)
      lem rewrite eval-toState₁ rs₁' | eval-toState₁ rs₂' = refl
    assoc (a ⃗) | inj₂ ((b₁ , rs₁) , eq₁) = lem
      where
      rs₁' : ⟨ f ⨾ (g ⨾ h) ∣ a ∣ ☐ ⟩▷ ↦* ［ f ∣ b₁ ∣ ☐⨾ g ⨾ h • ☐ ］▷
      rs₁' = ↦⃗₃ ∷ appendκ↦* rs₁ refl (☐⨾ g ⨾ h • ☐)

      rs₂' : ⟨ (f ⨾ g) ⨾ h ∣ a ∣ ☐ ⟩▷ ↦* ［ f ∣ b₁ ∣ ☐⨾ g • ☐⨾ h • ☐ ］▷
      rs₂' = (↦⃗₃ ∷ ↦⃗₃ ∷ ◾) ++↦ appendκ↦* rs₁ refl (☐⨾ g • ☐⨾ h • ☐)

      lem : eval (f ⨾ g ⨾ h) (a ⃗) ≡ eval ((f ⨾ g) ⨾ h) (a ⃗)
      lem with Loop₁⃗ (rs₂' , rs₁')
      ... | (x , rs₁'' , rs₂'') rewrite eval-toState₁ rs₁'' | eval-toState₁ rs₂'' = refl
    assoc (d ⃖) with inspect⊎ (run ［ h ∣ d ∣ ☐ ］◁) (λ ())
    assoc (d ⃖) | inj₁ ((c₁ , rs₁) , eq₁) = lem
      where
      rs₁' : ［ f ⨾ (g ⨾ h) ∣ d ∣ ☐ ］◁ ↦* ［ g ∣ c₁ ∣ ☐⨾ h • (f ⨾☐• ☐) ］◁
      rs₁' = (↦⃖₁₀ ∷ ↦⃖₁₀ ∷ ◾) ++↦ appendκ↦* rs₁ refl (g ⨾☐• (f ⨾☐• ☐)) ++↦ ↦⃖₇ ∷ ◾

      rs₂' : ［ (f ⨾ g) ⨾ h ∣ d ∣ ☐ ］◁ ↦* ［ g ∣ c₁ ∣ f ⨾☐• (☐⨾ h • ☐) ］◁
      rs₂' = (↦⃖₁₀ ∷ ◾) ++↦ appendκ↦* rs₁ refl ((f ⨾ g) ⨾☐• ☐) ++↦ ↦⃖₇ ∷ ↦⃖₁₀ ∷ ◾

      lem : eval (f ⨾ g ⨾ h) (d ⃖) ≡ eval ((f ⨾ g) ⨾ h) (d ⃖)
      lem with Loop₄⃖ (rs₂' , rs₁')
      ... | (x , rs₁'' , rs₂'') rewrite eval-toState₂ rs₁'' | eval-toState₂ rs₂'' = refl
    assoc (d ⃖) | inj₂ ((d₁ , rs₁) , eq₁) = lem
      where
      rs₁' : ［ f ⨾ (g ⨾ h) ∣ d ∣ ☐ ］◁ ↦* ［ f ⨾ (g ⨾ h) ∣ d₁ ∣ ☐ ］▷
      rs₁' = (↦⃖₁₀ ∷ ↦⃖₁₀ ∷ ◾) ++↦ appendκ↦* rs₁ refl (g ⨾☐• (f ⨾☐• ☐)) ++↦ ↦⃗₁₀ ∷ ↦⃗₁₀ ∷ ◾

      rs₂' : ［ (f ⨾ g) ⨾ h ∣ d ∣ ☐ ］◁ ↦* ［ (f ⨾ g) ⨾ h ∣ d₁ ∣ ☐ ］▷
      rs₂' = (↦⃖₁₀ ∷ ◾) ++↦ appendκ↦* rs₁ refl ((f ⨾ g) ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾

      lem : eval (f ⨾ g ⨾ h) (d ⃖) ≡ eval ((f ⨾ g) ⨾ h) (d ⃖)
      lem rewrite eval-toState₂ rs₁' | eval-toState₂ rs₂' = refl

    private
      {-# TERMINATING #-}
      Loop₁⃗ : {a₀ : ⟦ A ⟧} {b : ⟦ B ⟧}
             → ⟨ (f ⨾ g) ⨾ h ∣ a₀ ∣ ☐ ⟩▷ ↦* ［ f ∣ b ∣ ☐⨾ g • ☐⨾ h • ☐ ］▷
             × ⟨ f ⨾ (g ⨾ h) ∣ a₀ ∣ ☐ ⟩▷ ↦* ［ f ∣ b ∣ ☐⨾ g ⨾ h • ☐ ］▷
             → Σ[ x ∈ Val D A ]
               ⟨ (f ⨾ g) ⨾ h ∣ a₀ ∣ ☐ ⟩▷ ↦* toState ((f ⨾ g) ⨾ h) x
             × ⟨ f ⨾ (g ⨾ h) ∣ a₀ ∣ ☐ ⟩▷ ↦* toState (f ⨾ (g ⨾ h)) x
      Loop₁⃗ {a₀} {b} (ts₁ , ts₂) with inspect⊎ (run ⟨ g ∣ b ∣ ☐ ⟩▷) (λ ())
      Loop₁⃗ {a₀} {b} (ts₁ , ts₂) | inj₁ ((b₁ , rs₁) , eq₁) = Loop₂⃗ (ts₁ ++↦ rs₁' , ts₂ ++↦ rs₂')
        where
        rs₁' : ［ f ∣ b ∣ ☐⨾ g • ☐⨾ h • ☐ ］▷ ↦* ［ f ∣ b₁ ∣ ☐⨾ g • ☐⨾ h • ☐ ］◁
        rs₁' = ↦⃗₇ ∷ appendκ↦* rs₁ refl (f ⨾☐• (☐⨾ h • ☐)) ++↦ ↦⃖₇ ∷ ◾

        rs₂' : ［ f ∣ b ∣ ☐⨾ g ⨾ h • ☐ ］▷ ↦* ［ f ∣ b₁ ∣ ☐⨾ g ⨾ h • ☐ ］◁
        rs₂' = (↦⃗₇ ∷ ↦⃗₃ ∷ ◾) ++↦ appendκ↦* rs₁ refl (☐⨾ h • (f ⨾☐• ☐)) ++↦ ↦⃖₃ ∷ ↦⃖₇ ∷ ◾
      Loop₁⃗ {a₀} {b} (ts₁ , ts₂) | inj₂ ((c₁ , rs₁) , eq₁) = Loop₃⃗ (ts₁ ++↦ rs₁' , ts₂ ++↦ rs₂')
        where
        rs₁' : ［ f ∣ b ∣ ☐⨾ g • ☐⨾ h • ☐ ］▷ ↦* ［ g ∣ c₁ ∣ f ⨾☐• (☐⨾ h • ☐) ］▷
        rs₁' = ↦⃗₇ ∷ appendκ↦* rs₁ refl (f ⨾☐• (☐⨾ h • ☐))

        rs₂' : ［ f ∣ b ∣ ☐⨾ g ⨾ h • ☐ ］▷ ↦* ［ g ∣ c₁ ∣ ☐⨾ h • (f ⨾☐• ☐) ］▷
        rs₂' = (↦⃗₇ ∷ ↦⃗₃ ∷ ◾) ++↦ appendκ↦* rs₁ refl (☐⨾ h • (f ⨾☐• ☐))

      Loop₂⃗ : {a₀ : ⟦ A ⟧} {b : ⟦ B ⟧}
             → ⟨ (f ⨾ g) ⨾ h ∣ a₀ ∣ ☐ ⟩▷ ↦* ［ f ∣ b ∣ ☐⨾ g • ☐⨾ h • ☐ ］◁
             × ⟨ f ⨾ (g ⨾ h) ∣ a₀ ∣ ☐ ⟩▷ ↦* ［ f ∣ b ∣ ☐⨾ g ⨾ h • ☐ ］◁
             → Σ[ x ∈ Val D A ]
               ⟨ (f ⨾ g) ⨾ h ∣ a₀ ∣ ☐ ⟩▷ ↦* toState ((f ⨾ g) ⨾ h) x
             × ⟨ f ⨾ (g ⨾ h) ∣ a₀ ∣ ☐ ⟩▷ ↦* toState (f ⨾ (g ⨾ h)) x
      Loop₂⃗ {a₀} {b} (ts₁ , ts₂) with inspect⊎ (run ［ f ∣ b ∣ ☐ ］◁) (λ ())
      Loop₂⃗ {a₀} {b} (ts₁ , ts₂) | inj₁ ((a₁ , rs₁) , eq₁) = a₁ ⃖ , ts₁ ++↦ rs₁' , ts₂ ++↦ rs₂'
        where
        rs₁' : ［ f ∣ b ∣ ☐⨾ g • ☐⨾ h • ☐ ］◁ ↦* ⟨ (f ⨾ g) ⨾ h ∣ a₁ ∣ ☐ ⟩◁
        rs₁' = appendκ↦* rs₁ refl (☐⨾ g • ☐⨾ h • ☐) ++↦ ↦⃖₃ ∷ ↦⃖₃ ∷ ◾

        rs₂' : ［ f ∣ b ∣ ☐⨾ g ⨾ h • ☐ ］◁ ↦* ⟨ f ⨾ (g ⨾ h) ∣ a₁ ∣ ☐ ⟩◁
        rs₂' = appendκ↦* rs₁ refl (☐⨾ g ⨾ h • ☐) ++↦ ↦⃖₃ ∷ ◾
      Loop₂⃗ {a₀} {b} (ts₁ , ts₂) | inj₂ ((b₁ , rs₁) , eq₁) = Loop₁⃗ (ts₁ ++↦ rs₁' , ts₂ ++↦ rs₂')
        where
        rs₁' : ［ f ∣ b ∣ ☐⨾ g • (☐⨾ h • ☐) ］◁ ↦* ［ f ∣ b₁ ∣ ☐⨾ g • (☐⨾ h • ☐) ］▷
        rs₁' = appendκ↦* rs₁ refl (☐⨾ g • ☐⨾ h • ☐)

        rs₂' : ［ f ∣ b ∣ ☐⨾ g ⨾ h • ☐ ］◁ ↦* ［ f ∣ b₁ ∣ ☐⨾ g ⨾ h • ☐ ］▷
        rs₂' = appendκ↦* rs₁ refl (☐⨾ g ⨾ h • ☐)

      Loop₃⃗ : {a₀ : ⟦ A ⟧} {c : ⟦ C ⟧}
             → ⟨ (f ⨾ g) ⨾ h ∣ a₀ ∣ ☐ ⟩▷ ↦* ［ g ∣ c ∣ f ⨾☐• (☐⨾ h • ☐) ］▷
             × ⟨ f ⨾ (g ⨾ h) ∣ a₀ ∣ ☐ ⟩▷ ↦* ［ g ∣ c ∣ ☐⨾ h • (f ⨾☐• ☐) ］▷
             → Σ[ x ∈ Val D A ]
               ⟨ (f ⨾ g) ⨾ h ∣ a₀ ∣ ☐ ⟩▷ ↦* toState ((f ⨾ g) ⨾ h) x
             × ⟨ f ⨾ (g ⨾ h) ∣ a₀ ∣ ☐ ⟩▷ ↦* toState (f ⨾ (g ⨾ h)) x
      Loop₃⃗ {a₀} {c} (ts₁ , ts₂) with inspect⊎ (run ⟨ h ∣ c ∣ ☐ ⟩▷) (λ ())
      Loop₃⃗ {a₀} {c} (ts₁ , ts₂) | inj₁ ((c₁ , rs₁) , eq₁) = Loop₄⃗ (ts₁ ++↦ rs₁' , ts₂ ++↦ rs₂')
        where
        rs₁' : ［ g ∣ c ∣ f ⨾☐• (☐⨾ h • ☐) ］▷ ↦* ［ g ∣ c₁ ∣ f ⨾☐• (☐⨾ h • ☐) ］◁
        rs₁' = (↦⃗₁₀ ∷ ↦⃗₇ ∷ ◾) ++↦ appendκ↦* rs₁ refl (f ⨾ g ⨾☐• ☐) ++↦ ↦⃖₇ ∷ ↦⃖₁₀ ∷ ◾

        rs₂' : ［ g ∣ c ∣ ☐⨾ h • (f ⨾☐• ☐) ］▷ ↦* ［ g ∣ c₁ ∣ ☐⨾ h • (f ⨾☐• ☐) ］◁
        rs₂' = ↦⃗₇ ∷ appendκ↦* rs₁ refl (g ⨾☐• (f ⨾☐• ☐)) ++↦ ↦⃖₇ ∷ ◾
      Loop₃⃗ {a₀} {c} (ts₁ , ts₂) | inj₂ ((d₁ , rs₁) , eq₁) = d₁ ⃗ , ts₁ ++↦ rs₁' , ts₂ ++↦ rs₂'
        where
        rs₁' : ［ g ∣ c ∣ f ⨾☐• (☐⨾ h • ☐) ］▷ ↦* ［ (f ⨾ g) ⨾ h ∣ d₁ ∣ ☐ ］▷
        rs₁' = (↦⃗₁₀ ∷ ↦⃗₇ ∷ ◾) ++↦ appendκ↦* rs₁ refl (f ⨾ g ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾

        rs₂' : ［ g ∣ c ∣ ☐⨾ h • (f ⨾☐• ☐) ］▷ ↦* ［ f ⨾ g ⨾ h ∣ d₁ ∣ ☐ ］▷
        rs₂' = ↦⃗₇ ∷ appendκ↦* rs₁ refl (g ⨾☐• (f ⨾☐• ☐)) ++↦ ↦⃗₁₀ ∷ ↦⃗₁₀ ∷ ◾

      Loop₄⃗ : {a₀ : ⟦ A ⟧} {c : ⟦ C ⟧}
             → ⟨ (f ⨾ g) ⨾ h ∣ a₀ ∣ ☐ ⟩▷ ↦* ［ g ∣ c ∣ f ⨾☐• (☐⨾ h • ☐) ］◁
             × ⟨ f ⨾ (g ⨾ h) ∣ a₀ ∣ ☐ ⟩▷ ↦* ［ g ∣ c ∣ ☐⨾ h • (f ⨾☐• ☐) ］◁
             → Σ[ x ∈ Val D A ]
               ⟨ (f ⨾ g) ⨾ h ∣ a₀ ∣ ☐ ⟩▷ ↦* toState ((f ⨾ g) ⨾ h) x
             × ⟨ f ⨾ (g ⨾ h) ∣ a₀ ∣ ☐ ⟩▷ ↦* toState (f ⨾ (g ⨾ h)) x
      Loop₄⃗ {a₀} {c} (ts₁ , ts₂) with inspect⊎ (run ［ g ∣ c ∣ ☐ ］◁) (λ ())
      Loop₄⃗ {a₀} {c} (ts₁ , ts₂) | inj₁ ((b₁ , rs₁) , eq₁) = Loop₂⃗ (ts₁ ++↦ rs₁' , ts₂ ++↦ rs₂')
        where
        rs₁' : ［ g ∣ c ∣ f ⨾☐• (☐⨾ h • ☐) ］◁ ↦* ［ f ∣ b₁ ∣ ☐⨾ g • (☐⨾ h • ☐) ］◁
        rs₁' = appendκ↦* rs₁ refl (f ⨾☐• (☐⨾ h • ☐)) ++↦ ↦⃖₇ ∷ ◾

        rs₂' : ［ g ∣ c ∣ ☐⨾ h • (f ⨾☐• ☐) ］◁ ↦* ［ f ∣ b₁ ∣ ☐⨾ g ⨾ h • ☐ ］◁
        rs₂' = appendκ↦* rs₁ refl (☐⨾ h • (f ⨾☐• ☐)) ++↦ ↦⃖₃ ∷ ↦⃖₇ ∷ ◾
      Loop₄⃗ {a₀} {c} (ts₁ , ts₂) | inj₂ ((c₁ , rs₁) , eq₁) = Loop₃⃗ (ts₁ ++↦ rs₁' , ts₂ ++↦ rs₂')
        where
        rs₁' : ［ g ∣ c ∣ f ⨾☐• (☐⨾ h • ☐) ］◁ ↦* ［ g ∣ c₁ ∣ f ⨾☐• (☐⨾ h • ☐) ］▷
        rs₁' = appendκ↦* rs₁ refl (f ⨾☐• (☐⨾ h • ☐))

        rs₂' : ［ g ∣ c ∣ ☐⨾ h • (f ⨾☐• ☐) ］◁ ↦* ［ g ∣ c₁ ∣ ☐⨾ h • (f ⨾☐• ☐) ］▷
        rs₂' = appendκ↦* rs₁ refl (☐⨾ h • (f ⨾☐• ☐))

      Loop₁⃖ : {d₀ : ⟦ D ⟧} {b : ⟦ B ⟧}
             → ［ (f ⨾ g) ⨾ h ∣ d₀ ∣ ☐ ］◁ ↦* ［ f ∣ b ∣ ☐⨾ g • ☐⨾ h • ☐ ］▷
             × ［ f ⨾ (g ⨾ h) ∣ d₀ ∣ ☐ ］◁ ↦* ［ f ∣ b ∣ ☐⨾ g ⨾ h • ☐ ］▷
             → Σ[ x ∈ Val D A ]
               ［ (f ⨾ g) ⨾ h ∣ d₀ ∣ ☐ ］◁ ↦* toState ((f ⨾ g) ⨾ h) x
             × ［ f ⨾ (g ⨾ h) ∣ d₀ ∣ ☐ ］◁ ↦* toState (f ⨾ (g ⨾ h)) x
      Loop₁⃖ {d₀} {b} (ts₁ , ts₂) with inspect⊎ (run ⟨ g ∣ b ∣ ☐ ⟩▷) (λ ())
      Loop₁⃖ {d₀} {b} (ts₁ , ts₂) | inj₁ ((b₁ , rs₁) , eq₁) = Loop₂⃖ (ts₁ ++↦ rs₁' , ts₂ ++↦ rs₂')
        where
        rs₁' : ［ f ∣ b ∣ ☐⨾ g • ☐⨾ h • ☐ ］▷ ↦* ［ f ∣ b₁ ∣ ☐⨾ g • ☐⨾ h • ☐ ］◁
        rs₁' = ↦⃗₇ ∷ appendκ↦* rs₁ refl (f ⨾☐• (☐⨾ h • ☐)) ++↦ ↦⃖₇ ∷ ◾

        rs₂' : ［ f ∣ b ∣ ☐⨾ g ⨾ h • ☐ ］▷ ↦* ［ f ∣ b₁ ∣ ☐⨾ g ⨾ h • ☐ ］◁
        rs₂' = (↦⃗₇ ∷ ↦⃗₃ ∷ ◾) ++↦ appendκ↦* rs₁ refl (☐⨾ h • (f ⨾☐• ☐)) ++↦ ↦⃖₃ ∷ ↦⃖₇ ∷ ◾
      Loop₁⃖ {d₀} {b} (ts₁ , ts₂) | inj₂ ((c₁ , rs₁) , eq₁) = Loop₃⃖ (ts₁ ++↦ rs₁' , ts₂ ++↦ rs₂')
        where
        rs₁' : ［ f ∣ b ∣ ☐⨾ g • ☐⨾ h • ☐ ］▷ ↦* ［ g ∣ c₁ ∣ f ⨾☐• (☐⨾ h • ☐) ］▷
        rs₁' = ↦⃗₇ ∷ appendκ↦* rs₁ refl (f ⨾☐• (☐⨾ h • ☐))

        rs₂' : ［ f ∣ b ∣ ☐⨾ g ⨾ h • ☐ ］▷ ↦* ［ g ∣ c₁ ∣ ☐⨾ h • (f ⨾☐• ☐) ］▷
        rs₂' = (↦⃗₇ ∷ ↦⃗₃ ∷ ◾) ++↦ appendκ↦* rs₁ refl (☐⨾ h • (f ⨾☐• ☐))

      Loop₂⃖ : {d₀ : ⟦ D ⟧} {b : ⟦ B ⟧}
             → ［ (f ⨾ g) ⨾ h ∣ d₀ ∣ ☐ ］◁ ↦* ［ f ∣ b ∣ ☐⨾ g • ☐⨾ h • ☐ ］◁
             × ［ f ⨾ (g ⨾ h) ∣ d₀ ∣ ☐ ］◁ ↦* ［ f ∣ b ∣ ☐⨾ g ⨾ h • ☐ ］◁
             → Σ[ x ∈ Val D A ]
               ［ (f ⨾ g) ⨾ h ∣ d₀ ∣ ☐ ］◁ ↦* toState ((f ⨾ g) ⨾ h) x
             × ［ f ⨾ (g ⨾ h) ∣ d₀ ∣ ☐ ］◁ ↦* toState (f ⨾ (g ⨾ h)) x
      Loop₂⃖ {d₀} {b} (ts₁ , ts₂) with inspect⊎ (run ［ f ∣ b ∣ ☐ ］◁) (λ ())
      Loop₂⃖ {d₀} {b} (ts₁ , ts₂) | inj₁ ((a₁ , rs₁) , eq₁) = a₁ ⃖ , ts₁ ++↦ rs₁' , ts₂ ++↦ rs₂'
        where
        rs₁' : ［ f ∣ b ∣ ☐⨾ g • ☐⨾ h • ☐ ］◁ ↦* ⟨ (f ⨾ g) ⨾ h ∣ a₁ ∣ ☐ ⟩◁
        rs₁' = appendκ↦* rs₁ refl (☐⨾ g • ☐⨾ h • ☐) ++↦ ↦⃖₃ ∷ ↦⃖₃ ∷ ◾

        rs₂' : ［ f ∣ b ∣ ☐⨾ g ⨾ h • ☐ ］◁ ↦* ⟨ f ⨾ (g ⨾ h) ∣ a₁ ∣ ☐ ⟩◁
        rs₂' = appendκ↦* rs₁ refl (☐⨾ g ⨾ h • ☐) ++↦ ↦⃖₃ ∷ ◾
      Loop₂⃖ {d₀} {b} (ts₁ , ts₂) | inj₂ ((b₁ , rs₁) , eq₁) = Loop₁⃖ (ts₁ ++↦ rs₁' , ts₂ ++↦ rs₂')
        where
        rs₁' : ［ f ∣ b ∣ ☐⨾ g • (☐⨾ h • ☐) ］◁ ↦* ［ f ∣ b₁ ∣ ☐⨾ g • (☐⨾ h • ☐) ］▷
        rs₁' = appendκ↦* rs₁ refl (☐⨾ g • ☐⨾ h • ☐)

        rs₂' : ［ f ∣ b ∣ ☐⨾ g ⨾ h • ☐ ］◁ ↦* ［ f ∣ b₁ ∣ ☐⨾ g ⨾ h • ☐ ］▷
        rs₂' = appendκ↦* rs₁ refl (☐⨾ g ⨾ h • ☐)

      Loop₃⃖ : {d₀ : ⟦ D ⟧} {c : ⟦ C ⟧}
             → ［ (f ⨾ g) ⨾ h ∣ d₀ ∣ ☐ ］◁ ↦* ［ g ∣ c ∣ f ⨾☐• (☐⨾ h • ☐) ］▷
             × ［ f ⨾ (g ⨾ h) ∣ d₀ ∣ ☐ ］◁ ↦* ［ g ∣ c ∣ ☐⨾ h • (f ⨾☐• ☐) ］▷
             → Σ[ x ∈ Val D A ]
               ［ (f ⨾ g) ⨾ h ∣ d₀ ∣ ☐ ］◁ ↦* toState ((f ⨾ g) ⨾ h) x
             × ［ f ⨾ (g ⨾ h) ∣ d₀ ∣ ☐ ］◁ ↦* toState (f ⨾ (g ⨾ h)) x
      Loop₃⃖ {d₀} {c} (ts₁ , ts₂) with inspect⊎ (run ⟨ h ∣ c ∣ ☐ ⟩▷) (λ ())
      Loop₃⃖ {d₀} {c} (ts₁ , ts₂) | inj₁ ((c₁ , rs₁) , eq₁) = Loop₄⃖ (ts₁ ++↦ rs₁' , ts₂ ++↦ rs₂')
        where
        rs₁' : ［ g ∣ c ∣ f ⨾☐• (☐⨾ h • ☐) ］▷ ↦* ［ g ∣ c₁ ∣ f ⨾☐• (☐⨾ h • ☐) ］◁
        rs₁' = (↦⃗₁₀ ∷ ↦⃗₇ ∷ ◾) ++↦ appendκ↦* rs₁ refl (f ⨾ g ⨾☐• ☐) ++↦ ↦⃖₇ ∷ ↦⃖₁₀ ∷ ◾

        rs₂' : ［ g ∣ c ∣ ☐⨾ h • (f ⨾☐• ☐) ］▷ ↦* ［ g ∣ c₁ ∣ ☐⨾ h • (f ⨾☐• ☐) ］◁
        rs₂' = ↦⃗₇ ∷ appendκ↦* rs₁ refl (g ⨾☐• (f ⨾☐• ☐)) ++↦ ↦⃖₇ ∷ ◾
      Loop₃⃖ {d₀} {c} (ts₁ , ts₂) | inj₂ ((d₁ , rs₁) , eq₁) = d₁ ⃗ , ts₁ ++↦ rs₁' , ts₂ ++↦ rs₂'
        where
        rs₁' : ［ g ∣ c ∣ f ⨾☐• (☐⨾ h • ☐) ］▷ ↦* ［ (f ⨾ g) ⨾ h ∣ d₁ ∣ ☐ ］▷
        rs₁' = (↦⃗₁₀ ∷ ↦⃗₇ ∷ ◾) ++↦ appendκ↦* rs₁ refl (f ⨾ g ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾

        rs₂' : ［ g ∣ c ∣ ☐⨾ h • (f ⨾☐• ☐) ］▷ ↦* ［ f ⨾ g ⨾ h ∣ d₁ ∣ ☐ ］▷
        rs₂' = ↦⃗₇ ∷ appendκ↦* rs₁ refl (g ⨾☐• (f ⨾☐• ☐)) ++↦ ↦⃗₁₀ ∷ ↦⃗₁₀ ∷ ◾

      Loop₄⃖ : {d₀ : ⟦ D ⟧} {c : ⟦ C ⟧}
             → ［ (f ⨾ g) ⨾ h ∣ d₀ ∣ ☐ ］◁ ↦* ［ g ∣ c ∣ f ⨾☐• (☐⨾ h • ☐) ］◁
             × ［ f ⨾ (g ⨾ h) ∣ d₀ ∣ ☐ ］◁ ↦* ［ g ∣ c ∣ ☐⨾ h • (f ⨾☐• ☐) ］◁
             → Σ[ x ∈ Val D A ]
               ［ (f ⨾ g) ⨾ h ∣ d₀ ∣ ☐ ］◁ ↦* toState ((f ⨾ g) ⨾ h) x
             × ［ f ⨾ (g ⨾ h) ∣ d₀ ∣ ☐ ］◁ ↦* toState (f ⨾ (g ⨾ h)) x
      Loop₄⃖ {d₀} {c} (ts₁ , ts₂) with inspect⊎ (run ［ g ∣ c ∣ ☐ ］◁) (λ ())
      Loop₄⃖ {d₀} {c} (ts₁ , ts₂) | inj₁ ((b₁ , rs₁) , eq₁) = Loop₂⃖ (ts₁ ++↦ rs₁' , ts₂ ++↦ rs₂')
        where
        rs₁' : ［ g ∣ c ∣ f ⨾☐• (☐⨾ h • ☐) ］◁ ↦* ［ f ∣ b₁ ∣ ☐⨾ g • (☐⨾ h • ☐) ］◁
        rs₁' = appendκ↦* rs₁ refl (f ⨾☐• (☐⨾ h • ☐)) ++↦ ↦⃖₇ ∷ ◾

        rs₂' : ［ g ∣ c ∣ ☐⨾ h • (f ⨾☐• ☐) ］◁ ↦* ［ f ∣ b₁ ∣ ☐⨾ g ⨾ h • ☐ ］◁
        rs₂' = appendκ↦* rs₁ refl (☐⨾ h • (f ⨾☐• ☐)) ++↦ ↦⃖₃ ∷ ↦⃖₇ ∷ ◾
      Loop₄⃖ {d₀} {c} (ts₁ , ts₂) | inj₂ ((c₁ , rs₁) , eq₁) = Loop₃⃖ (ts₁ ++↦ rs₁' , ts₂ ++↦ rs₂')
        where
        rs₁' : ［ g ∣ c ∣ f ⨾☐• (☐⨾ h • ☐) ］◁ ↦* ［ g ∣ c₁ ∣ f ⨾☐• (☐⨾ h • ☐) ］▷
        rs₁' = appendκ↦* rs₁ refl (f ⨾☐• (☐⨾ h • ☐))

        rs₂' : ［ g ∣ c ∣ ☐⨾ h • (f ⨾☐• ☐) ］◁ ↦* ［ g ∣ c₁ ∣ ☐⨾ h • (f ⨾☐• ☐) ］▷
        rs₂' = appendκ↦* rs₁ refl (☐⨾ h • (f ⨾☐• ☐))

open assoc public

module homomorphism {A₁ B₁ A₂ B₂ A₃ B₃} {f : A₁ ↔ A₂}  {g : B₁ ↔ B₂} {h : A₂ ↔ A₃} {i : B₂ ↔ B₃} where
  mutual
    homomorphism : eval ((f ⨾ h) ⊕ (g ⨾ i)) ∼ eval (f ⊕ g ⨾ h ⊕ i)
    homomorphism (inj₁ a ⃗) with inspect⊎ (run ⟨ f ∣ a ∣ ☐ ⟩▷) (λ ())
    homomorphism (inj₁ a ⃗) | inj₁ ((a₁ , rs) , eq) = lem
      where
      rs₁' : ⟨ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₁ a ∣ ☐ ⟩▷ ↦* ⟨ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₁ a₁ ∣ ☐ ⟩◁
      rs₁' = (↦⃗₄ ∷ ↦⃗₃ ∷ ◾) ++↦ appendκ↦* rs refl (☐⨾ h • (☐⊕ g ⨾ i • ☐)) ++↦ ↦⃖₃ ∷ ↦⃖₄ ∷ ◾

      rs₂' : ⟨ f ⊕ g ⨾ h ⊕ i ∣ inj₁ a ∣ ☐ ⟩▷ ↦* ⟨ f ⊕ g ⨾ h ⊕ i ∣ inj₁ a₁ ∣ ☐ ⟩◁
      rs₂' = (↦⃗₃ ∷ ↦⃗₄ ∷ ◾) ++↦ appendκ↦* rs refl (☐⊕ g • (☐⨾ h ⊕ i • ☐)) ++↦ ↦⃖₄ ∷ ↦⃖₃ ∷ ◾
      
      lem : eval ((f ⨾ h) ⊕ (g ⨾ i)) (inj₁ a ⃗) ≡ eval (f ⊕ g ⨾ h ⊕ i) (inj₁ a ⃗)
      lem rewrite eval-toState₁ rs₁' | eval-toState₁ rs₂' = refl
    homomorphism (inj₁ a ⃗) | inj₂ ((a₂ , rs) , eq) = lem
      where
      rs₁' : ⟨ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₁ a ∣ ☐ ⟩▷ ↦* ［ f ∣ a₂ ∣ ☐⨾ h • (☐⊕ g ⨾ i • ☐) ］▷
      rs₁' = (↦⃗₄ ∷ ↦⃗₃ ∷ ◾) ++↦ appendκ↦* rs refl (☐⨾ h • (☐⊕ g ⨾ i • ☐))

      rs₂' : ⟨ f ⊕ g ⨾ h ⊕ i ∣ inj₁ a ∣ ☐ ⟩▷ ↦* ［ f ⊕ g ∣ inj₁ a₂ ∣ ☐⨾ h ⊕ i • ☐ ］▷
      rs₂' = (↦⃗₃ ∷ ↦⃗₄ ∷ ◾) ++↦ appendκ↦* rs refl (☐⊕ g • (☐⨾ h ⊕ i • ☐)) ++↦ ↦⃗₁₁ ∷ ◾
      
      lem : eval ((f ⨾ h) ⊕ (g ⨾ i)) (inj₁ a ⃗) ≡ eval (f ⊕ g ⨾ h ⊕ i) (inj₁ a ⃗)
      lem with Loop₁⃗ (rs₁' , rs₂')
      ... | (x , rs₁'' , rs₂'') rewrite eval-toState₁ rs₁'' | eval-toState₁ rs₂'' = refl
    homomorphism (inj₂ b ⃗) with inspect⊎ (run ⟨ g ∣ b ∣ ☐ ⟩▷) (λ ())
    homomorphism (inj₂ b ⃗) | inj₁ ((b₁ , rs) , eq) = lem
      where
      rs₁' : ⟨ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₂ b ∣ ☐ ⟩▷ ↦* ⟨ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₂ b₁ ∣ ☐ ⟩◁
      rs₁' = (↦⃗₅ ∷ ↦⃗₃ ∷ ◾) ++↦ appendκ↦* rs refl (☐⨾ i • (f ⨾ h ⊕☐• ☐)) ++↦ ↦⃖₃ ∷ ↦⃖₅ ∷ ◾

      rs₂' : ⟨ f ⊕ g ⨾ h ⊕ i ∣ inj₂ b ∣ ☐ ⟩▷ ↦* ⟨ f ⊕ g ⨾ h ⊕ i ∣ inj₂ b₁ ∣ ☐ ⟩◁
      rs₂' = (↦⃗₃ ∷ ↦⃗₅ ∷ ◾) ++↦ appendκ↦* rs refl (f ⊕☐• (☐⨾ h ⊕ i • ☐)) ++↦ ↦⃖₅ ∷ ↦⃖₃ ∷ ◾
      
      lem : eval ((f ⨾ h) ⊕ (g ⨾ i)) (inj₂ b ⃗) ≡ eval (f ⊕ g ⨾ h ⊕ i) (inj₂ b ⃗)
      lem rewrite eval-toState₁ rs₁' | eval-toState₁ rs₂' = refl
    homomorphism (inj₂ b ⃗) | inj₂ ((b₂ , rs) , eq) = lem
      where
      rs₁' : ⟨ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₂ b ∣ ☐ ⟩▷ ↦* ［ g ∣ b₂ ∣ ☐⨾ i • (f ⨾ h ⊕☐• ☐) ］▷
      rs₁' = (↦⃗₅ ∷ ↦⃗₃ ∷ ◾) ++↦ appendκ↦* rs refl (☐⨾ i • (f ⨾ h ⊕☐• ☐))

      rs₂' : ⟨ f ⊕ g ⨾ h ⊕ i ∣ inj₂ b ∣ ☐ ⟩▷ ↦* ［ f ⊕ g ∣ inj₂ b₂ ∣ ☐⨾ h ⊕ i • ☐ ］▷
      rs₂' = (↦⃗₃ ∷ ↦⃗₅ ∷ ◾) ++↦ appendκ↦* rs refl (f ⊕☐• (☐⨾ h ⊕ i • ☐)) ++↦ ↦⃗₁₂ ∷ ◾
      
      lem : eval ((f ⨾ h) ⊕ (g ⨾ i)) (inj₂ b ⃗) ≡ eval (f ⊕ g ⨾ h ⊕ i) (inj₂ b ⃗)
      lem with Loop₃⃗ (rs₁' , rs₂')
      ... | (x , rs₁'' , rs₂'') rewrite eval-toState₁ rs₁'' | eval-toState₁ rs₂'' = refl
    homomorphism (inj₁ a ⃖) with inspect⊎ (run ［ h ∣ a ∣ ☐ ］◁) (λ ())
    homomorphism (inj₁ a ⃖) | inj₁ ((a₂ , rs) , eq) = lem
      where
      rs₁' : ［ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₁ a ∣ ☐ ］◁ ↦* ［ f ∣ a₂ ∣ ☐⨾ h • (☐⊕ g ⨾ i • ☐) ］◁
      rs₁' = (↦⃖₁₁ ∷ ↦⃖₁₀ ∷ ◾) ++↦ appendκ↦* rs refl (f ⨾☐• (☐⊕ g ⨾ i • ☐)) ++↦ ↦⃖₇ ∷ ◾

      rs₂' : ［ f ⊕ g ⨾ h ⊕ i ∣ inj₁ a ∣ ☐ ］◁ ↦* ［ f ⊕ g ∣ inj₁ a₂ ∣ ☐⨾ h ⊕ i • ☐ ］◁
      rs₂' = (↦⃖₁₀ ∷ ↦⃖₁₁ ∷ ◾) ++↦ appendκ↦* rs refl (☐⊕ i • (f ⊕ g ⨾☐• ☐)) ++↦ ↦⃖₄ ∷ ↦⃖₇ ∷ ◾

      lem : eval ((f ⨾ h) ⊕ (g ⨾ i)) (inj₁ a ⃖) ≡ eval (f ⊕ g ⨾ h ⊕ i) (inj₁ a ⃖)
      lem with Loop₂⃖ (rs₁' , rs₂')
      ... | (x , rs₁'' , rs₂'') rewrite eval-toState₂ rs₁'' | eval-toState₂ rs₂'' = refl
    homomorphism (inj₁ a ⃖) | inj₂ ((a₃ , rs) , eq) = lem
      where
      rs₁' : ［ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₁ a ∣ ☐ ］◁ ↦* ［ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₁ a₃ ∣ ☐ ］▷
      rs₁' = (↦⃖₁₁ ∷ ↦⃖₁₀ ∷ ◾) ++↦ appendκ↦* rs refl (f ⨾☐• (☐⊕ g ⨾ i • ☐)) ++↦ ↦⃗₁₀ ∷ ↦⃗₁₁ ∷ ◾

      rs₂' : ［ f ⊕ g ⨾ h ⊕ i ∣ inj₁ a ∣ ☐ ］◁ ↦* ［ f ⊕ g ⨾ h ⊕ i ∣ inj₁ a₃ ∣ ☐ ］▷
      rs₂' = (↦⃖₁₀ ∷ ↦⃖₁₁ ∷ ◾) ++↦ appendκ↦* rs refl (☐⊕ i • (f ⊕ g ⨾☐• ☐)) ++↦ ↦⃗₁₁ ∷ ↦⃗₁₀ ∷ ◾
      
      lem : eval ((f ⨾ h) ⊕ (g ⨾ i)) (inj₁ a ⃖) ≡ eval (f ⊕ g ⨾ h ⊕ i) (inj₁ a ⃖)
      lem rewrite eval-toState₂ rs₁' | eval-toState₂ rs₂' = refl
    homomorphism (inj₂ b ⃖) with inspect⊎ (run ［ i ∣ b ∣ ☐ ］◁) (λ ())
    homomorphism (inj₂ b ⃖) | inj₁ ((b₂ , rs) , eq) = lem
      where
      rs₁' : ［ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₂ b ∣ ☐ ］◁ ↦* ［ g ∣ b₂ ∣ ☐⨾ i • (f ⨾ h ⊕☐• ☐) ］◁
      rs₁' = (↦⃖₁₂ ∷ ↦⃖₁₀ ∷ ◾) ++↦ appendκ↦* rs refl (g ⨾☐• (f ⨾ h ⊕☐• ☐)) ++↦ ↦⃖₇ ∷ ◾

      rs₂' : ［ f ⊕ g ⨾ h ⊕ i ∣ inj₂ b ∣ ☐ ］◁ ↦* ［ f ⊕ g ∣ inj₂ b₂ ∣ ☐⨾ h ⊕ i • ☐ ］◁
      rs₂' = (↦⃖₁₀ ∷ ↦⃖₁₂ ∷ ◾) ++↦ appendκ↦* rs refl (h ⊕☐• (f ⊕ g ⨾☐• ☐)) ++↦ ↦⃖₅ ∷ ↦⃖₇ ∷ ◾

      lem : eval ((f ⨾ h) ⊕ (g ⨾ i)) (inj₂ b ⃖) ≡ eval (f ⊕ g ⨾ h ⊕ i) (inj₂ b ⃖)
      lem with Loop₄⃖ (rs₁' , rs₂')
      ... | (x , rs₁'' , rs₂'') rewrite eval-toState₂ rs₁'' | eval-toState₂ rs₂'' = refl
    homomorphism (inj₂ b ⃖) | inj₂ ((b₃ , rs) , eq) = lem
      where
      rs₁' : ［ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₂ b ∣ ☐ ］◁ ↦* ［ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₂ b₃ ∣ ☐ ］▷
      rs₁' = (↦⃖₁₂ ∷ ↦⃖₁₀ ∷ ◾) ++↦ appendκ↦* rs refl (g ⨾☐• (f ⨾ h ⊕☐• ☐)) ++↦ ↦⃗₁₀ ∷ ↦⃗₁₂ ∷ ◾

      rs₂' : ［ f ⊕ g ⨾ h ⊕ i ∣ inj₂ b ∣ ☐ ］◁ ↦* ［ f ⊕ g ⨾ h ⊕ i ∣ inj₂ b₃ ∣ ☐ ］▷
      rs₂' = (↦⃖₁₀ ∷ ↦⃖₁₂ ∷ ◾) ++↦ appendκ↦* rs refl (h ⊕☐• (f ⊕ g ⨾☐• ☐)) ++↦ ↦⃗₁₂ ∷ ↦⃗₁₀ ∷ ◾

      lem : eval ((f ⨾ h) ⊕ (g ⨾ i)) (inj₂ b ⃖) ≡ eval (f ⊕ g ⨾ h ⊕ i) (inj₂ b ⃖)
      lem rewrite eval-toState₂ rs₁' | eval-toState₂ rs₂' = refl

    private
      {-# TERMINATING #-}
      Loop₁⃗ : {a₁ : ⟦ A₁ ⟧} {a₂ : ⟦ A₂ ⟧}
             → ⟨ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₁ a₁ ∣ ☐ ⟩▷ ↦* ［ f ∣ a₂ ∣ ☐⨾ h • (☐⊕ g ⨾ i • ☐) ］▷
             × ⟨ f ⊕ g ⨾ h ⊕ i ∣ inj₁ a₁ ∣ ☐ ⟩▷ ↦* ［ f ⊕ g ∣ inj₁ a₂ ∣ ☐⨾ h ⊕ i • ☐ ］▷
             → Σ[ x ∈ Val (A₃ +ᵤ B₃) (A₁ +ᵤ B₁) ]
               ⟨ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₁ a₁ ∣ ☐ ⟩▷ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) x
             × ⟨ f ⊕ g ⨾ h ⊕ i ∣ inj₁ a₁ ∣ ☐ ⟩▷ ↦* toState (f ⊕ g ⨾ h ⊕ i) x
      Loop₁⃗ {a₁} {a₂} (ts₁ , ts₂) with inspect⊎ (run ⟨ h ∣ a₂ ∣ ☐ ⟩▷) (λ ())
      Loop₁⃗ {a₁} {a₂} (ts₁ , ts₂) | inj₁ ((a₂' , rs) , eq) =
             Loop₂⃗ ( ts₁ ++↦ ↦⃗₇ ∷ appendκ↦* rs refl (f ⨾☐• (☐⊕ g ⨾ i • ☐)) ++↦ ↦⃖₇ ∷ ◾
                    , ts₂ ++↦ (↦⃗₇ ∷ ↦⃗₄ ∷ ◾) ++↦ appendκ↦* rs refl (☐⊕ i • (f ⊕ g ⨾☐• ☐)) ++↦ ↦⃖₄ ∷ ↦⃖₇ ∷ ◾)
      Loop₁⃗ {a₁} {a₂} (ts₁ , ts₂) | inj₂ ((a₃  , rs) , eq) =
             inj₁ a₃ ⃗ , ts₁ ++↦ ↦⃗₇ ∷ appendκ↦* rs refl (f ⨾☐• (☐⊕ g ⨾ i • ☐)) ++↦ ↦⃗₁₀ ∷ ↦⃗₁₁ ∷ ◾
                       , ts₂ ++↦ (↦⃗₇ ∷ ↦⃗₄ ∷ ◾) ++↦ appendκ↦* rs refl (☐⊕ i • (f ⊕ g ⨾☐• ☐)) ++↦ ↦⃗₁₁ ∷ ↦⃗₁₀ ∷ ◾

      Loop₂⃗ : {a₁ : ⟦ A₁ ⟧} {a₂ : ⟦ A₂ ⟧}
             → ⟨ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₁ a₁ ∣ ☐ ⟩▷ ↦* ［ f ∣ a₂ ∣ ☐⨾ h • (☐⊕ g ⨾ i • ☐) ］◁
             × ⟨ f ⊕ g ⨾ h ⊕ i ∣ inj₁ a₁ ∣ ☐ ⟩▷ ↦* ［ f ⊕ g ∣ inj₁ a₂ ∣ ☐⨾ h ⊕ i • ☐ ］◁
             → Σ[ x ∈ Val (A₃ +ᵤ B₃) (A₁ +ᵤ B₁) ]
               ⟨ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₁ a₁ ∣ ☐ ⟩▷ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) x
             × ⟨ f ⊕ g ⨾ h ⊕ i ∣ inj₁ a₁ ∣ ☐ ⟩▷ ↦* toState (f ⊕ g ⨾ h ⊕ i) x
      Loop₂⃗ {a₁} {a₂} (ts₁ , ts₂) with inspect⊎ (run ［ f ∣ a₂ ∣ ☐ ］◁) (λ ())
      Loop₂⃗ {a₁} {a₂} (ts₁ , ts₂) | inj₁ ((a₁' , rs) , eq) =
             inj₁ a₁' ⃖ , ts₁ ++↦ appendκ↦* rs refl (☐⨾ h • (☐⊕ g ⨾ i • ☐)) ++↦ ↦⃖₃ ∷ ↦⃖₄ ∷ ◾
                        , ts₂ ++↦ ↦⃖₁₁ ∷ appendκ↦* rs refl (☐⊕ g • (☐⨾ h ⊕ i • ☐)) ++↦ ↦⃖₄ ∷ ↦⃖₃ ∷ ◾
      Loop₂⃗ {a₁} {a₂} (ts₁ , ts₂) | inj₂ ((a₂' , rs) , eq) =
             Loop₁⃗ ( ts₁ ++↦ appendκ↦* rs refl (☐⨾ h • (☐⊕ g ⨾ i • ☐))
                    , ts₂ ++↦ ↦⃖₁₁ ∷ appendκ↦* rs refl (☐⊕ g • (☐⨾ h ⊕ i • ☐)) ++↦ ↦⃗₁₁ ∷ ◾)

      Loop₃⃗ : {b₁ : ⟦ B₁ ⟧} {b₂ : ⟦ B₂ ⟧}
             → ⟨ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₂ b₁ ∣ ☐ ⟩▷ ↦* ［ g ∣ b₂ ∣ ☐⨾ i • (f ⨾ h ⊕☐• ☐) ］▷
             × ⟨ f ⊕ g ⨾ h ⊕ i ∣ inj₂ b₁ ∣ ☐ ⟩▷ ↦* ［ f ⊕ g ∣ inj₂ b₂ ∣ ☐⨾ h ⊕ i • ☐ ］▷
             → Σ[ x ∈ Val (A₃ +ᵤ B₃) (A₁ +ᵤ B₁) ]
               ⟨ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₂ b₁ ∣ ☐ ⟩▷ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) x
             × ⟨ f ⊕ g ⨾ h ⊕ i ∣ inj₂ b₁ ∣ ☐ ⟩▷ ↦* toState (f ⊕ g ⨾ h ⊕ i) x
      Loop₃⃗ {b₁} {b₂} (ts₁ , ts₂) with inspect⊎ (run ⟨ i ∣ b₂ ∣ ☐ ⟩▷) (λ ())
      Loop₃⃗ {b₁} {b₂} (ts₁ , ts₂) | inj₁ ((b₂' , rs) , eq) =
             Loop₄⃗ ( ts₁ ++↦ ↦⃗₇ ∷ appendκ↦* rs refl (g ⨾☐• (f ⨾ h ⊕☐• ☐)) ++↦ ↦⃖₇ ∷ ◾
                    , ts₂ ++↦ (↦⃗₇ ∷ ↦⃗₅ ∷ ◾) ++↦ appendκ↦* rs refl (h ⊕☐• (f ⊕ g ⨾☐• ☐)) ++↦ ↦⃖₅ ∷ ↦⃖₇ ∷ ◾)
      Loop₃⃗ {b₁} {b₂} (ts₁ , ts₂) | inj₂ ((b₃  , rs) , eq) =
             inj₂ b₃ ⃗ , ts₁ ++↦ ↦⃗₇ ∷ appendκ↦* rs refl (g ⨾☐• (f ⨾ h ⊕☐• ☐)) ++↦ ↦⃗₁₀ ∷ ↦⃗₁₂ ∷ ◾
                       , ts₂ ++↦ (↦⃗₇ ∷ ↦⃗₅ ∷ ◾) ++↦ appendκ↦* rs refl (h ⊕☐• (f ⊕ g ⨾☐• ☐)) ++↦ ↦⃗₁₂ ∷ ↦⃗₁₀ ∷ ◾

      Loop₄⃗ : {b₁ : ⟦ B₁ ⟧} {b₂ : ⟦ B₂ ⟧}
             → ⟨ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₂ b₁ ∣ ☐ ⟩▷ ↦* ［ g ∣ b₂ ∣ ☐⨾ i • (f ⨾ h ⊕☐• ☐) ］◁
             × ⟨ f ⊕ g ⨾ h ⊕ i ∣ inj₂ b₁ ∣ ☐ ⟩▷ ↦* ［ f ⊕ g ∣ inj₂ b₂ ∣ ☐⨾ h ⊕ i • ☐ ］◁
             → Σ[ x ∈ Val (A₃ +ᵤ B₃) (A₁ +ᵤ B₁) ]
               ⟨ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₂ b₁ ∣ ☐ ⟩▷ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) x
             × ⟨ f ⊕ g ⨾ h ⊕ i ∣ inj₂ b₁ ∣ ☐ ⟩▷ ↦* toState (f ⊕ g ⨾ h ⊕ i) x
      Loop₄⃗ {b₁} {b₂} (ts₁ , ts₂) with inspect⊎ (run ［ g ∣ b₂ ∣ ☐ ］◁) (λ ())
      Loop₄⃗ {b₁} {b₂} (ts₁ , ts₂) | inj₁ ((b₁' , rs) , eq) =
             inj₂ b₁' ⃖ , ts₁ ++↦ appendκ↦* rs refl (☐⨾ i • (f ⨾ h ⊕☐• ☐)) ++↦ ↦⃖₃ ∷ ↦⃖₅ ∷ ◾
                        , ts₂ ++↦ ↦⃖₁₂ ∷ appendκ↦* rs refl (f ⊕☐• (☐⨾ h ⊕ i • ☐)) ++↦ ↦⃖₅ ∷ ↦⃖₃ ∷ ◾
      Loop₄⃗ {b₁} {b₂} (ts₁ , ts₂) | inj₂ ((b₂' , rs) , eq) = 
             Loop₃⃗ ( ts₁ ++↦ appendκ↦* rs refl (☐⨾ i • (f ⨾ h ⊕☐• ☐))
                    , ts₂ ++↦ ↦⃖₁₂ ∷ appendκ↦* rs refl (f ⊕☐• (☐⨾ h ⊕ i • ☐)) ++↦ ↦⃗₁₂ ∷ ◾)

      Loop₁⃖ : {a₃ : ⟦ A₃ ⟧} {a₂ : ⟦ A₂ ⟧}
             → ［ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₁ a₃ ∣ ☐ ］◁ ↦* ［ f ∣ a₂ ∣ ☐⨾ h • (☐⊕ g ⨾ i • ☐) ］▷
             × ［ f ⊕ g ⨾ h ⊕ i ∣ inj₁ a₃ ∣ ☐ ］◁ ↦* ［ f ⊕ g ∣ inj₁ a₂ ∣ ☐⨾ h ⊕ i • ☐ ］▷
             → Σ[ x ∈ Val (A₃ +ᵤ B₃) (A₁ +ᵤ B₁) ]
               ［ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₁ a₃ ∣ ☐ ］◁ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) x
             × ［ f ⊕ g ⨾ h ⊕ i ∣ inj₁ a₃ ∣ ☐ ］◁ ↦* toState (f ⊕ g ⨾ h ⊕ i) x
      Loop₁⃖ {a₃} {a₂} (ts₁ , ts₂) with inspect⊎ (run ⟨ h ∣ a₂ ∣ ☐ ⟩▷) (λ ())
      Loop₁⃖ {a₃} {a₂} (ts₁ , ts₂) | inj₁ ((a₂' , rs) , eq) =
             Loop₂⃖ ( ts₁ ++↦ ↦⃗₇ ∷ appendκ↦* rs refl (f ⨾☐• (☐⊕ g ⨾ i • ☐)) ++↦ ↦⃖₇ ∷ ◾
                    , ts₂ ++↦ (↦⃗₇ ∷ ↦⃗₄ ∷ ◾) ++↦ appendκ↦* rs refl (☐⊕ i • (f ⊕ g ⨾☐• ☐)) ++↦ ↦⃖₄ ∷ ↦⃖₇ ∷ ◾)
      Loop₁⃖ {a₃} {a₂} (ts₁ , ts₂) | inj₂ ((a₃' , rs) , eq) =
             inj₁ a₃' ⃗ , ts₁ ++↦ ↦⃗₇ ∷ appendκ↦* rs refl (f ⨾☐• (☐⊕ g ⨾ i • ☐)) ++↦ ↦⃗₁₀ ∷ ↦⃗₁₁ ∷ ◾
                        , ts₂ ++↦ (↦⃗₇ ∷ ↦⃗₄ ∷ ◾) ++↦ appendκ↦* rs refl (☐⊕ i • (f ⊕ g ⨾☐• ☐)) ++↦ ↦⃗₁₁ ∷ ↦⃗₁₀ ∷ ◾

      Loop₂⃖ : {a₃ : ⟦ A₃ ⟧} {a₂ : ⟦ A₂ ⟧}
             → ［ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₁ a₃ ∣ ☐ ］◁ ↦* ［ f ∣ a₂ ∣ ☐⨾ h • (☐⊕ g ⨾ i • ☐) ］◁
             × ［ f ⊕ g ⨾ h ⊕ i ∣ inj₁ a₃ ∣ ☐ ］◁ ↦* ［ f ⊕ g ∣ inj₁ a₂ ∣ ☐⨾ h ⊕ i • ☐ ］◁
             → Σ[ x ∈ Val (A₃ +ᵤ B₃) (A₁ +ᵤ B₁) ]
               ［ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₁ a₃ ∣ ☐ ］◁ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) x
             × ［ f ⊕ g ⨾ h ⊕ i ∣ inj₁ a₃ ∣ ☐ ］◁ ↦* toState (f ⊕ g ⨾ h ⊕ i) x
      Loop₂⃖ {a₃} {a₂} (ts₁ , ts₂) with inspect⊎ (run ［ f ∣ a₂ ∣ ☐ ］◁) (λ ())
      Loop₂⃖ {a₃} {a₂} (ts₁ , ts₂) | inj₁ ((a₁' , rs) , eq) =
             inj₁ a₁' ⃖ , ts₁ ++↦ appendκ↦* rs refl (☐⨾ h • (☐⊕ g ⨾ i • ☐)) ++↦ ↦⃖₃ ∷ ↦⃖₄ ∷ ◾
                        , ts₂ ++↦ ↦⃖₁₁ ∷ appendκ↦* rs refl (☐⊕ g • (☐⨾ h ⊕ i • ☐)) ++↦ ↦⃖₄ ∷ ↦⃖₃ ∷ ◾
      Loop₂⃖ {a₃} {a₂} (ts₁ , ts₂) | inj₂ ((a₂' , rs) , eq) =
             Loop₁⃖ ( ts₁ ++↦ appendκ↦* rs refl (☐⨾ h • (☐⊕ g ⨾ i • ☐))
                    , ts₂ ++↦ ↦⃖₁₁ ∷ appendκ↦* rs refl (☐⊕ g • (☐⨾ h ⊕ i • ☐)) ++↦ ↦⃗₁₁ ∷ ◾)

      Loop₃⃖ : {b₃ : ⟦ B₃ ⟧} {b₂ : ⟦ B₂ ⟧}
             → ［ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₂ b₃ ∣ ☐ ］◁ ↦* ［ g ∣ b₂ ∣ ☐⨾ i • (f ⨾ h ⊕☐• ☐) ］▷
             × ［ f ⊕ g ⨾ h ⊕ i ∣ inj₂ b₃ ∣ ☐ ］◁ ↦* ［ f ⊕ g ∣ inj₂ b₂ ∣ ☐⨾ h ⊕ i • ☐ ］▷
             → Σ[ x ∈ Val (A₃ +ᵤ B₃) (A₁ +ᵤ B₁) ]
               ［ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₂ b₃ ∣ ☐ ］◁ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) x
             × ［ f ⊕ g ⨾ h ⊕ i ∣ inj₂ b₃ ∣ ☐ ］◁ ↦* toState (f ⊕ g ⨾ h ⊕ i) x
      Loop₃⃖ {b₃} {b₂} (ts₁ , ts₂) with inspect⊎ (run ⟨ i ∣ b₂ ∣ ☐ ⟩▷) (λ ())
      Loop₃⃖ {b₃} {b₂} (ts₁ , ts₂) | inj₁ ((b₂' , rs) , eq) =
             Loop₄⃖ ( ts₁ ++↦ ↦⃗₇ ∷ appendκ↦* rs refl (g ⨾☐• (f ⨾ h ⊕☐• ☐)) ++↦ ↦⃖₇ ∷ ◾
                    , ts₂ ++↦ (↦⃗₇ ∷ ↦⃗₅ ∷ ◾) ++↦ appendκ↦* rs refl (h ⊕☐• (f ⊕ g ⨾☐• ☐)) ++↦ ↦⃖₅ ∷ ↦⃖₇ ∷ ◾)
      Loop₃⃖ {b₃} {b₂} (ts₁ , ts₂) | inj₂ ((b₃' , rs) , eq) =
             inj₂ b₃' ⃗ , ts₁ ++↦ ↦⃗₇ ∷ appendκ↦* rs refl (g ⨾☐• (f ⨾ h ⊕☐• ☐)) ++↦ ↦⃗₁₀ ∷ ↦⃗₁₂ ∷ ◾
                        , ts₂ ++↦ (↦⃗₇ ∷ ↦⃗₅ ∷ ◾) ++↦ appendκ↦* rs refl (h ⊕☐• (f ⊕ g ⨾☐• ☐)) ++↦ ↦⃗₁₂ ∷ ↦⃗₁₀ ∷ ◾

      Loop₄⃖ : {b₃ : ⟦ B₃ ⟧} {b₂ : ⟦ B₂ ⟧}
             → ［ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₂ b₃ ∣ ☐ ］◁ ↦* ［ g ∣ b₂ ∣ ☐⨾ i • (f ⨾ h ⊕☐• ☐) ］◁
             × ［ f ⊕ g ⨾ h ⊕ i ∣ inj₂ b₃ ∣ ☐ ］◁ ↦* ［ f ⊕ g ∣ inj₂ b₂ ∣ ☐⨾ h ⊕ i • ☐ ］◁
             → Σ[ x ∈ Val (A₃ +ᵤ B₃) (A₁ +ᵤ B₁) ]
               ［ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₂ b₃ ∣ ☐ ］◁ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) x
             × ［ f ⊕ g ⨾ h ⊕ i ∣ inj₂ b₃ ∣ ☐ ］◁ ↦* toState (f ⊕ g ⨾ h ⊕ i) x
      Loop₄⃖ {b₃} {b₂} (ts₁ , ts₂) with inspect⊎ (run ［ g ∣ b₂ ∣ ☐ ］◁) (λ ())
      Loop₄⃖ {b₃} {b₂} (ts₁ , ts₂) | inj₁ ((b₁' , rs) , eq) =
             inj₂ b₁' ⃖ , ts₁ ++↦ appendκ↦* rs refl (☐⨾ i • (f ⨾ h ⊕☐• ☐)) ++↦ ↦⃖₃ ∷ ↦⃖₅ ∷ ◾
                        , ts₂ ++↦ ↦⃖₁₂ ∷ appendκ↦* rs refl (f ⊕☐• (☐⨾ h ⊕ i • ☐)) ++↦ ↦⃖₅ ∷ ↦⃖₃ ∷ ◾
      Loop₄⃖ {b₃} {b₂} (ts₁ , ts₂) | inj₂ ((b₂' , rs) , eq) = 
             Loop₃⃖ ( ts₁ ++↦ appendκ↦* rs refl (☐⨾ i • (f ⨾ h ⊕☐• ☐))
                    , ts₂ ++↦ ↦⃖₁₂ ∷ appendκ↦* rs refl (f ⊕☐• (☐⨾ h ⊕ i • ☐)) ++↦ ↦⃗₁₂ ∷ ◾)

open homomorphism public

module Inverse where
  !invᵢ : ∀ {A B} → (c : A ↔ B) → interp c ∼ interp (! (! c))
  !invᵢ unite₊l x = refl
  !invᵢ uniti₊l x = refl
  !invᵢ swap₊ x = refl
  !invᵢ assocl₊ x = refl
  !invᵢ assocr₊ x = refl
  !invᵢ unite⋆l x = refl
  !invᵢ uniti⋆l x = refl
  !invᵢ swap⋆ x = refl
  !invᵢ assocl⋆ x = refl
  !invᵢ assocr⋆ x = refl
  !invᵢ absorbr x = refl
  !invᵢ factorzl x = refl
  !invᵢ dist x = refl
  !invᵢ factor x = refl
  !invᵢ id↔ x = refl
  !invᵢ (c₁ ⨾ c₂) x = ∘-resp-≈ᵢ (!invᵢ c₂) (!invᵢ c₁) x
  !invᵢ (c₁ ⊕ c₂) (inj₁ x ⃗) rewrite sym (!invᵢ c₁ (x ⃗)) with interp c₁ (x ⃗)
  ... | x' ⃗ = refl
  ... | x' ⃖ = refl
  !invᵢ (c₁ ⊕ c₂) (inj₂ y ⃗) rewrite sym (!invᵢ c₂ (y ⃗)) with interp c₂ (y ⃗)
  ... | y' ⃗ = refl
  ... | y' ⃖ = refl
  !invᵢ (c₁ ⊕ c₂) (inj₁ x ⃖) rewrite sym (!invᵢ c₁ (x ⃖)) with interp c₁ (x ⃖)
  ... | x' ⃗ = refl
  ... | x' ⃖ = refl
  !invᵢ (c₁ ⊕ c₂) (inj₂ y ⃖) rewrite sym (!invᵢ c₂ (y ⃖)) with interp c₂ (y ⃖)
  ... | y' ⃗ = refl
  ... | y' ⃖ = refl  
  !invᵢ (c₁ ⊗ c₂) ((x , y) ⃗) rewrite sym (!invᵢ c₁ (x ⃗)) with interp c₁ (x ⃗)
  !invᵢ (c₁ ⊗ c₂) ((x , y) ⃗) | x' ⃗ rewrite sym (!invᵢ c₂ (y ⃗)) with interp c₂ (y ⃗)
  !invᵢ (c₁ ⊗ c₂) ((x , y) ⃗) | x' ⃗ | y' ⃗ = refl
  !invᵢ (c₁ ⊗ c₂) ((x , y) ⃗) | x' ⃗ | y' ⃖ = refl
  !invᵢ (c₁ ⊗ c₂) ((x , y) ⃗) | x' ⃖ = refl  
  !invᵢ (c₁ ⊗ c₂) ((x , y) ⃖) rewrite sym (!invᵢ c₂ (y ⃖)) with interp c₂ (y ⃖)
  !invᵢ (c₁ ⊗ c₂) ((x , y) ⃖) | y' ⃗ = refl
  !invᵢ (c₁ ⊗ c₂) ((x , y) ⃖) | y' ⃖ rewrite sym (!invᵢ c₁ (x ⃖)) with interp c₁ (x ⃖)
  !invᵢ (c₁ ⊗ c₂) ((x , y) ⃖) | y' ⃖ | x' ⃗ = refl
  !invᵢ (c₁ ⊗ c₂) ((x , y) ⃖) | y' ⃖ | x' ⃖ = refl
  !invᵢ η₊ x = refl
  !invᵢ ε₊ x = refl

  !inv : ∀ {A B} → (c : A ↔ B) → eval c ∼ eval (! (! c))
  !inv c x = trans  (eval≡interp c x)
             (trans (!invᵢ c x)
                    (sym (eval≡interp (! (! c)) x)))

  private
    toState! : ∀ {A B} → (c : A ↔ B) → Val B A → State
    toState! c (b ⃗) = ⟨ ! c ∣ b ∣ ☐ ⟩◁
    toState! c (a ⃖) = ［ ! c ∣ a ∣ ☐ ］▷

  mutual
    !rev : ∀ {A B} → (c : A ↔ B) → ∀ x {y} → eval c x ≡ y → eval (! c) y ≡ x
    !rev unite₊l (inj₂ y ⃗) refl = refl
    !rev unite₊l (x ⃖) refl = refl
    !rev uniti₊l (x ⃗) refl = refl
    !rev uniti₊l (inj₂ y ⃖) refl = refl
    !rev swap₊ (inj₁ x ⃗) refl = refl
    !rev swap₊ (inj₂ y ⃗) refl = refl
    !rev swap₊ (inj₁ x ⃖) refl = refl
    !rev swap₊ (inj₂ y ⃖) refl = refl
    !rev assocl₊ (inj₁ x ⃗) refl = refl
    !rev assocl₊ (inj₂ (inj₁ y) ⃗) refl = refl
    !rev assocl₊ (inj₂ (inj₂ z) ⃗) refl = refl
    !rev assocl₊ (inj₁ (inj₁ x) ⃖) refl = refl
    !rev assocl₊ (inj₁ (inj₂ y) ⃖) refl = refl
    !rev assocl₊ (inj₂ z ⃖) refl = refl
    !rev assocr₊ (inj₁ (inj₁ x) ⃗) refl = refl
    !rev assocr₊ (inj₁ (inj₂ y) ⃗) refl = refl
    !rev assocr₊ (inj₂ z ⃗) refl = refl
    !rev assocr₊ (inj₁ x ⃖) refl = refl
    !rev assocr₊ (inj₂ (inj₁ y) ⃖) refl = refl
    !rev assocr₊ (inj₂ (inj₂ z) ⃖) refl = refl
    !rev unite⋆l ((tt , x) ⃗) refl = refl
    !rev unite⋆l (x ⃖) refl = refl
    !rev uniti⋆l (x ⃗) refl = refl
    !rev uniti⋆l ((tt , x) ⃖) refl = refl
    !rev swap⋆ ((x , y) ⃗) refl = refl
    !rev swap⋆ ((y , x) ⃖) refl = refl
    !rev assocl⋆ ((x , (y , z)) ⃗) refl = refl
    !rev assocl⋆ (((x , y) , z) ⃖) refl = refl
    !rev assocr⋆ (((x , y) , z) ⃗) refl = refl
    !rev assocr⋆ ((x , (y , z)) ⃖) refl = refl
    !rev absorbr (() ⃗)
    !rev absorbr (() ⃖)
    !rev factorzl (() ⃗)
    !rev factorzl (() ⃖)
    !rev dist ((inj₁ x , z) ⃗) refl = refl
    !rev dist ((inj₂ y , z) ⃗) refl = refl
    !rev dist (inj₁ (x , z) ⃖) refl = refl
    !rev dist (inj₂ (y , z) ⃖) refl = refl
    !rev factor (inj₁ (x , z) ⃗) refl = refl
    !rev factor (inj₂ (y , z) ⃗) refl = refl
    !rev factor ((inj₁ x , z) ⃖) refl = refl
    !rev factor ((inj₂ y , z) ⃖) refl = refl
    !rev id↔ (x ⃗) refl = refl
    !rev id↔ (x ⃖) refl = refl
    !rev (c₁ ⨾ c₂) (x ⃗) refl with inspect⊎ (run ⟨ c₁ ∣ x ∣ ☐ ⟩▷) (λ ())
    !rev (c₁ ⨾ c₂) (x ⃗) refl | inj₁ ((x' , rs) , eq) = lem
      where
      rs' : ⟨ c₁ ⨾ c₂ ∣ x ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⨾ c₂ ∣ x' ∣ ☐ ⟩◁
      rs' = ↦⃗₃ ∷ appendκ↦* rs refl (☐⨾ c₂ • ☐) ++↦ ↦⃖₃ ∷ ◾

      rs! : ［ ! c₂ ⨾ ! c₁ ∣ x' ∣ ☐ ］◁ ↦* ［ ! c₂ ⨾ ! c₁ ∣ x ∣ ☐ ］▷
      rs! = ↦⃖₁₀ ∷ appendκ↦* (getₜᵣ⃖ (! c₁) (!rev c₁ (x ⃗) (eval-toState₁ rs))) refl (! c₂ ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾

      lem : eval (! (c₁ ⨾ c₂)) (eval (c₁ ⨾ c₂) (x ⃗)) ≡ x ⃗
      lem rewrite eval-toState₁ rs' = eval-toState₂ rs!
    !rev (c₁ ⨾ c₂) (x ⃗) refl | inj₂ ((x' , rs) , eq) = lem
      where
      rs' : ⟨ c₁ ⨾ c₂ ∣ x ∣ ☐ ⟩▷ ↦* ［ c₁ ∣ x' ∣ ☐⨾ c₂ • ☐ ］▷
      rs' = ↦⃗₃ ∷ appendκ↦* rs refl (☐⨾ c₂ • ☐)

      rs! : ［ ! c₂ ⨾ ! c₁ ∣ x ∣ ☐ ］◁ ↦* ⟨ ! c₁ ∣ x' ∣ ! c₂ ⨾☐• ☐ ⟩◁
      rs! = ↦⃖₁₀ ∷ Rev* (appendκ↦* (getₜᵣ⃗ (! c₁) (!rev c₁ (x ⃗) (eval-toState₁ rs))) refl (! c₂ ⨾☐• ☐))

      lem : eval (! (c₁ ⨾ c₂)) (eval (c₁ ⨾ c₂) (x ⃗)) ≡ x ⃗
      lem with eval (c₁ ⨾ c₂) (x ⃗) | loop₁⃗ rs' rs!
      ... | (x'' ⃗) | rs!' = eval-toState₁ (Rev* rs!')
      ... | (x'' ⃖) | rs!' = eval-toState₂ (Rev* rs!')
    !rev (c₁ ⨾ c₂) (x ⃖) refl with inspect⊎ (run ［ c₂ ∣ x ∣ ☐ ］◁) (λ ())
    !rev (c₁ ⨾ c₂) (x ⃖) refl | inj₁ ((x' , rs) , eq) = lem
      where
      rs' : ［ c₁ ⨾ c₂ ∣ x ∣ ☐ ］◁ ↦* ［ c₁ ∣ x' ∣ ☐⨾ c₂ • ☐ ］◁
      rs' = ↦⃖₁₀ ∷ appendκ↦* rs refl (c₁ ⨾☐• ☐) ++↦ ↦⃖₇ ∷ ◾
      
      rs! :  ⟨ ! c₂ ⨾ ! c₁ ∣ x ∣ ☐ ⟩▷ ↦* ⟨ ! c₁ ∣ x' ∣ ! c₂ ⨾☐• ☐ ⟩▷
      rs! = (↦⃗₃ ∷ ◾) ++↦ Rev* (appendκ↦* (getₜᵣ⃖ (! c₂) (!rev c₂ (x ⃖) (eval-toState₂ rs))) refl (☐⨾ ! c₁ • ☐)) ++↦ ↦⃗₇ ∷ ◾

      lem : eval (! (c₁ ⨾ c₂)) (eval (c₁ ⨾ c₂) (x ⃖)) ≡ x ⃖
      lem with eval (c₁ ⨾ c₂) (x ⃖) | loop₂⃖ rs' rs!
      ... | (x'' ⃗) | rs!' = eval-toState₁ (Rev* rs!')
      ... | (x'' ⃖) | rs!' = eval-toState₂ (Rev* rs!')
    !rev (c₁ ⨾ c₂) (x ⃖) refl | inj₂ ((x' , rs) , eq) = lem
      where
      rs' : ［ c₁ ⨾ c₂ ∣ x ∣ ☐ ］◁ ↦* ［ c₁ ⨾ c₂ ∣ x' ∣ ☐ ］▷
      rs' = ↦⃖₁₀ ∷ appendκ↦* rs refl (c₁ ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾

      rs! : ⟨ ! c₂ ⨾ ! c₁ ∣ x' ∣ ☐ ⟩▷ ↦* ⟨ ! c₂ ⨾ ! c₁ ∣ x ∣ ☐ ⟩◁
      rs! = ↦⃗₃ ∷ appendκ↦* (getₜᵣ⃗ (! c₂) (!rev c₂ (x ⃖) (eval-toState₂ rs))) refl (☐⨾ ! c₁ • ☐) ++↦ ↦⃖₃ ∷ ◾
      
      lem : eval (! (c₁ ⨾ c₂)) (eval (c₁ ⨾ c₂) (x ⃖)) ≡ x ⃖
      lem rewrite eval-toState₂ rs' = eval-toState₁ rs!
    !rev (c₁ ⊕ c₂) (inj₁ x ⃗) refl with inspect⊎ (run ⟨ c₁ ∣ x ∣ ☐ ⟩▷) (λ ())
    !rev (c₁ ⊕ c₂) (inj₁ x ⃗) refl | inj₁ ((x' , rs) , eq) = lem
      where
      rs' : ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₁ x' ∣ ☐ ⟩◁
      rs' = ↦⃗₄ ∷ appendκ↦* rs refl (☐⊕ c₂ • ☐) ++↦ ↦⃖₄ ∷ ◾

      rs! : ［ ! (c₁ ⊕ c₂) ∣ inj₁ x' ∣ ☐ ］◁  ↦* ［ ! (c₁ ⊕ c₂) ∣ inj₁ x ∣ ☐ ］▷ 
      rs! = ↦⃖₁₁ ∷ appendκ↦* (getₜᵣ⃖ (! c₁) (!rev c₁ (x ⃗) (eval-toState₁ rs))) refl (☐⊕ ! c₂ • ☐) ++↦ ↦⃗₁₁ ∷ ◾
      
      lem : eval (! (c₁ ⊕ c₂)) (eval (c₁ ⊕ c₂) (inj₁ x ⃗)) ≡ inj₁ x ⃗
      lem rewrite eval-toState₁ rs' = eval-toState₂ rs!
    !rev (c₁ ⊕ c₂) (inj₁ x ⃗) refl | inj₂ ((x' , rs) , eq) = lem
      where
      rs' : ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷ ↦* ［ c₁ ⊕ c₂ ∣ inj₁ x' ∣ ☐ ］▷ 
      rs' = ↦⃗₄ ∷ appendκ↦* rs refl (☐⊕ c₂ • ☐) ++↦ ↦⃗₁₁ ∷ ◾

      rs! : ⟨ ! (c₁ ⊕ c₂) ∣ inj₁ x' ∣ ☐ ⟩▷  ↦* ［ ! (c₁ ⊕ c₂) ∣ inj₁ x ∣ ☐ ］▷ 
      rs! = ↦⃗₄ ∷ appendκ↦* (getₜᵣ⃗ (! c₁) (!rev c₁ (x ⃗) (eval-toState₁ rs))) refl (☐⊕ ! c₂ • ☐) ++↦ ↦⃗₁₁ ∷ ◾
      
      lem : eval (! (c₁ ⊕ c₂)) (eval (c₁ ⊕ c₂) (inj₁ x ⃗)) ≡ inj₁ x ⃗
      lem rewrite eval-toState₁ rs' = eval-toState₁ rs!
    !rev (c₁ ⊕ c₂) (inj₂ y ⃗) refl with inspect⊎ (run ⟨ c₂ ∣ y ∣ ☐ ⟩▷) (λ ())
    !rev (c₁ ⊕ c₂) (inj₂ y ⃗) refl | inj₁ ((y' , rs) , eq) = lem
      where
      rs' : ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₂ y' ∣ ☐ ⟩◁
      rs' = ↦⃗₅ ∷ appendκ↦* rs refl (c₁ ⊕☐• ☐) ++↦ ↦⃖₅ ∷ ◾

      rs! : ［ ! (c₁ ⊕ c₂) ∣ inj₂ y' ∣ ☐ ］◁  ↦* ［ ! (c₁ ⊕ c₂) ∣ inj₂ y ∣ ☐ ］▷ 
      rs! = ↦⃖₁₂ ∷ appendκ↦* (getₜᵣ⃖ (! c₂) (!rev c₂ (y ⃗) (eval-toState₁ rs))) refl (! c₁ ⊕☐• ☐) ++↦ ↦⃗₁₂ ∷ ◾
      
      lem : eval (! (c₁ ⊕ c₂)) (eval (c₁ ⊕ c₂) (inj₂ y ⃗)) ≡ inj₂ y ⃗
      lem rewrite eval-toState₁ rs' = eval-toState₂ rs!
    !rev (c₁ ⊕ c₂) (inj₂ y ⃗) refl | inj₂ ((y' , rs) , eq) = lem
      where
      rs' : ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷ ↦* ［ c₁ ⊕ c₂ ∣ inj₂ y' ∣ ☐ ］▷ 
      rs' = ↦⃗₅ ∷ appendκ↦* rs refl (c₁ ⊕☐• ☐) ++↦ ↦⃗₁₂ ∷ ◾

      rs! : ⟨ ! (c₁ ⊕ c₂) ∣ inj₂ y' ∣ ☐ ⟩▷  ↦* ［ ! (c₁ ⊕ c₂) ∣ inj₂ y ∣ ☐ ］▷ 
      rs! = ↦⃗₅ ∷ appendκ↦* (getₜᵣ⃗ (! c₂) (!rev c₂ (y ⃗) (eval-toState₁ rs))) refl (! c₁ ⊕☐• ☐) ++↦ ↦⃗₁₂ ∷ ◾
      
      lem : eval (! (c₁ ⊕ c₂)) (eval (c₁ ⊕ c₂) (inj₂ y ⃗)) ≡ inj₂ y ⃗
      lem rewrite eval-toState₁ rs' = eval-toState₁ rs!
    !rev (c₁ ⊕ c₂) (inj₁ x ⃖) refl with inspect⊎ (run ［ c₁ ∣ x ∣ ☐ ］◁) (λ ())
    !rev (c₁ ⊕ c₂) (inj₁ x ⃖) refl | inj₁ ((x' , rs) , eq) = lem
      where
      rs' : ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₁ x' ∣ ☐ ⟩◁
      rs' = ↦⃖₁₁ ∷ appendκ↦* rs refl (☐⊕ c₂ • ☐) ++↦ ↦⃖₄ ∷ ◾

      rs! : ［ ! (c₁ ⊕ c₂) ∣ inj₁ x' ∣ ☐ ］◁  ↦* ⟨ ! (c₁ ⊕ c₂) ∣ inj₁ x ∣ ☐ ⟩◁
      rs! = ↦⃖₁₁ ∷ appendκ↦* (getₜᵣ⃖ (! c₁) (!rev c₁ (x ⃖) (eval-toState₂ rs))) refl (☐⊕ ! c₂ • ☐) ++↦ ↦⃖₄ ∷ ◾
      
      lem : eval (! (c₁ ⊕ c₂)) (eval (c₁ ⊕ c₂) (inj₁ x ⃖)) ≡ inj₁ x ⃖
      lem rewrite eval-toState₂ rs' = eval-toState₂ rs!
    !rev (c₁ ⊕ c₂) (inj₁ x ⃖) refl | inj₂ ((x' , rs) , eq) = lem
      where
      rs' : ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁ ↦* ［ c₁ ⊕ c₂ ∣ inj₁ x' ∣ ☐ ］▷ 
      rs' = ↦⃖₁₁ ∷ appendκ↦* rs refl (☐⊕ c₂ • ☐) ++↦ ↦⃗₁₁ ∷ ◾

      rs! : ⟨ ! (c₁ ⊕ c₂) ∣ inj₁ x' ∣ ☐ ⟩▷  ↦* ⟨ ! (c₁ ⊕ c₂) ∣ inj₁ x ∣ ☐ ⟩◁
      rs! = ↦⃗₄ ∷ appendκ↦* (getₜᵣ⃗ (! c₁) (!rev c₁ (x ⃖) (eval-toState₂ rs))) refl (☐⊕ ! c₂ • ☐) ++↦ ↦⃖₄ ∷ ◾
      
      lem : eval (! (c₁ ⊕ c₂)) (eval (c₁ ⊕ c₂) (inj₁ x ⃖)) ≡ inj₁ x ⃖
      lem rewrite eval-toState₂ rs' = eval-toState₁ rs!
    !rev (c₁ ⊕ c₂) (inj₂ y ⃖) refl with inspect⊎ (run ［ c₂ ∣ y ∣ ☐ ］◁) (λ ())
    !rev (c₁ ⊕ c₂) (inj₂ y ⃖) refl | inj₁ ((y' , rs) , eq) = lem
      where
      rs' : ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₂ y' ∣ ☐ ⟩◁
      rs' = ↦⃖₁₂ ∷ appendκ↦* rs refl (c₁ ⊕☐• ☐) ++↦ ↦⃖₅ ∷ ◾

      rs! : ［ ! (c₁ ⊕ c₂) ∣ inj₂ y' ∣ ☐ ］◁  ↦* ⟨ ! (c₁ ⊕ c₂) ∣ inj₂ y ∣ ☐ ⟩◁
      rs! = ↦⃖₁₂ ∷ appendκ↦* (getₜᵣ⃖ (! c₂) (!rev c₂ (y ⃖) (eval-toState₂ rs))) refl (! c₁ ⊕☐• ☐) ++↦ ↦⃖₅ ∷ ◾
      
      lem : eval (! (c₁ ⊕ c₂)) (eval (c₁ ⊕ c₂) (inj₂ y ⃖)) ≡ inj₂ y ⃖
      lem rewrite eval-toState₂ rs' = eval-toState₂ rs!
    !rev (c₁ ⊕ c₂) (inj₂ y ⃖) refl | inj₂ ((y' , rs) , eq) = lem
      where
      rs' : ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁ ↦* ［ c₁ ⊕ c₂ ∣ inj₂ y' ∣ ☐ ］▷ 
      rs' = ↦⃖₁₂ ∷ appendκ↦* rs refl (c₁ ⊕☐• ☐) ++↦ ↦⃗₁₂ ∷ ◾

      rs! : ⟨ ! (c₁ ⊕ c₂) ∣ inj₂ y' ∣ ☐ ⟩▷  ↦* ⟨ ! (c₁ ⊕ c₂) ∣ inj₂ y ∣ ☐ ⟩◁
      rs! = ↦⃗₅ ∷ appendκ↦* (getₜᵣ⃗ (! c₂) (!rev c₂ (y ⃖) (eval-toState₂ rs))) refl (! c₁ ⊕☐• ☐) ++↦ ↦⃖₅ ∷ ◾
      
      lem : eval (! (c₁ ⊕ c₂)) (eval (c₁ ⊕ c₂) (inj₂ y ⃖)) ≡ inj₂ y ⃖
      lem rewrite eval-toState₂ rs' = eval-toState₁ rs!
    !rev (c₁ ⊗ c₂) ((x , y) ⃗) refl with inspect⊎ (run ⟨ c₁ ∣ x ∣ ☐ ⟩▷) (λ ())
    !rev (c₁ ⊗ c₂) ((x , y) ⃗) refl | inj₁ ((x' , rsx) , _) = lem
      where
      rsx' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊗ c₂ ∣ (x' , y) ∣ ☐ ⟩◁
      rsx' = ↦⃗₆ ∷ appendκ↦* rsx refl (☐⊗[ c₂ , y ]• ☐) ++↦ ↦⃖₆ ∷ ◾

      rs! : ［ ! (c₁ ⊗ c₂) ∣ (x' , y) ∣ ☐ ］◁ ↦* ［ ! (c₁ ⊗ c₂) ∣ (x , y) ∣ ☐ ］▷
      rs! = (↦⃖₁₀ ∷ ↦⃖₁₀ ∷ ↦⃖₁ ∷ ↦⃖₇ ∷ ↦⃖₉ ∷ ◾) ++↦
            appendκ↦* (getₜᵣ⃖ (! c₁) (!rev c₁ (x ⃗) (eval-toState₁ rsx))) refl ([ ! c₂ , y ]⊗☐• ☐⨾ swap⋆ • (swap⋆ ⨾☐• ☐)) ++↦
            ↦⃗₉ ∷ ↦⃗₇ ∷ ↦⃗₁ ∷ ↦⃗₁₀ ∷ ↦⃗₁₀ ∷ ◾
      
      lem : eval (! (c₁ ⊗ c₂)) (eval (c₁ ⊗ c₂) ((x , y) ⃗)) ≡ (x , y) ⃗
      lem rewrite eval-toState₁ rsx' = eval-toState₂ rs!
    !rev (c₁ ⊗ c₂) ((x , y) ⃗) refl | inj₂ ((x' , rsx) , _) with inspect⊎ (run ⟨ c₂ ∣ y ∣ ☐ ⟩▷) (λ ())
    !rev (c₁ ⊗ c₂) ((x , y) ⃗) refl | inj₂ ((x' , rsx) , _) | inj₁ ((y' , rsy) , _) = lem
      where
      rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊗ c₂ ∣ (x , y') ∣ ☐ ⟩◁
      rs' = ↦⃗₆ ∷ appendκ↦* rsx refl (☐⊗[ c₂ , y ]• ☐) ++↦
            ↦⃗₈ ∷ appendκ↦* rsy refl ([ c₁ , x' ]⊗☐• ☐) ++↦
            ↦⃖₈ ∷ Rev* (appendκ↦* rsx refl (☐⊗[ c₂ , y' ]• ☐)) ++↦
            ↦⃖₆ ∷ ◾

      rs! : ［ ! (c₁ ⊗ c₂) ∣ (x , y') ∣ ☐ ］◁ ↦* ［ ! (c₁ ⊗ c₂) ∣ (x , y) ∣ ☐ ］▷
      rs! = (↦⃖₁₀ ∷ ↦⃖₁₀ ∷ ↦⃖₁ ∷ ↦⃖₇ ∷ ↦⃖₉ ∷ ◾) ++↦
            appendκ↦* (Rev* (getₜᵣ⃗ (! c₁) (!rev c₁ (x ⃗) (eval-toState₁ rsx)))) refl ([ ! c₂ , y' ]⊗☐• (☐⨾ swap⋆ • (swap⋆ ⨾☐• ☐))) ++↦
            ↦⃖₈ ∷ appendκ↦* (getₜᵣ⃖ (! c₂) (!rev c₂ (y ⃗) (eval-toState₁ rsy))) refl (☐⊗[ ! c₁ , x' ]• (☐⨾ swap⋆ • (swap⋆ ⨾☐• ☐))) ++↦
            ↦⃗₈ ∷ appendκ↦* (getₜᵣ⃗ (! c₁) (!rev c₁ (x ⃗) (eval-toState₁ rsx))) refl ([ ! c₂ , y ]⊗☐• (☐⨾ swap⋆ • (swap⋆ ⨾☐• ☐))) ++↦
            ↦⃗₉ ∷ ↦⃗₇ ∷ ↦⃗₁ ∷ ↦⃗₁₀ ∷ ↦⃗₁₀ ∷ ◾

      lem : eval (! (c₁ ⊗ c₂)) (eval (c₁ ⊗ c₂) ((x , y) ⃗)) ≡ (x , y) ⃗
      lem rewrite eval-toState₁ rs' = eval-toState₂ rs!
    !rev (c₁ ⊗ c₂) ((x , y) ⃗) refl | inj₂ ((x' , rsx) , _) | inj₂ ((y' , rsy) , _) = lem
      where
      rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ［ c₁ ⊗ c₂ ∣ (x' , y') ∣ ☐ ］▷
      rs' = ↦⃗₆ ∷ appendκ↦* rsx refl (☐⊗[ c₂ , y ]• ☐) ++↦
            ↦⃗₈ ∷ appendκ↦* rsy refl ([ c₁ , x' ]⊗☐• ☐) ++↦
            ↦⃗₉ ∷ ◾

      rs! : ⟨ ! (c₁ ⊗ c₂) ∣ (x' , y') ∣ ☐ ⟩▷  ↦* ［ ! (c₁ ⊗ c₂) ∣ (x , y) ∣ ☐ ］▷
      rs! = (↦⃗₃ ∷ ↦⃗₁ ∷ ↦⃗₇ ∷ ↦⃗₃ ∷ ↦⃗₆ ∷ ◾) ++↦
            appendκ↦* (getₜᵣ⃗ (! c₂) (!rev c₂ (y ⃗) (eval-toState₁ rsy))) refl (☐⊗[ ! c₁ , x' ]• (☐⨾ swap⋆ • (swap⋆ ⨾☐• ☐))) ++↦
            ↦⃗₈ ∷ appendκ↦* (getₜᵣ⃗ (! c₁) (!rev c₁ (x ⃗) (eval-toState₁ rsx))) refl ([ ! c₂ , y ]⊗☐• (☐⨾ swap⋆ • (swap⋆ ⨾☐• ☐))) ++↦
            ↦⃗₉ ∷ ↦⃗₇ ∷ ↦⃗₁ ∷ ↦⃗₁₀ ∷ ↦⃗₁₀ ∷ ◾

      lem : eval (! (c₁ ⊗ c₂)) (eval (c₁ ⊗ c₂) ((x , y) ⃗)) ≡ (x , y) ⃗
      lem rewrite eval-toState₁ rs' = eval-toState₁ rs!
    !rev (c₁ ⊗ c₂) ((x , y) ⃖) refl with inspect⊎ (run ［ c₂ ∣ y ∣ ☐  ］◁) (λ ())
    !rev (c₁ ⊗ c₂) ((x , y) ⃖) refl | inj₁ ((y' , rsy) , _) with inspect⊎ (run ［ c₁ ∣ x ∣ ☐  ］◁) (λ ())
    !rev (c₁ ⊗ c₂) ((x , y) ⃖) refl | inj₁ ((y' , rsy) , _) | inj₁ ((x' , rsx) , _) = lem
      where
      rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ⟨ c₁ ⊗ c₂ ∣ (x' , y') ∣ ☐ ⟩◁
      rs' = ↦⃖₉ ∷ appendκ↦* rsy refl ([ c₁ , x ]⊗☐• ☐) ++↦
            ↦⃖₈ ∷ appendκ↦* rsx refl (☐⊗[ c₂ , y' ]• ☐) ++↦ ↦⃖₆ ∷ ◾

      rs! : ［ ! (c₁ ⊗ c₂) ∣ (x' , y') ∣ ☐ ］◁  ↦* ⟨ ! (c₁ ⊗ c₂) ∣ (x , y) ∣ ☐ ⟩◁
      rs! = ↦⃖₁₀ ∷ ↦⃖₁₀ ∷ ↦⃖₁ ∷ ↦⃖₇ ∷ ↦⃖₉ ∷ ◾ ++↦
            appendκ↦* (getₜᵣ⃖ (! c₁) (!rev c₁ (x ⃖) (eval-toState₂ rsx))) refl ([ ! c₂ , y' ]⊗☐• (☐⨾ swap⋆ • (swap⋆ ⨾☐• ☐))) ++↦
            ↦⃖₈ ∷ appendκ↦* (getₜᵣ⃖ (! c₂) (!rev c₂ (y ⃖) (eval-toState₂ rsy))) refl (☐⊗[ ! c₁ , x ]• (☐⨾ swap⋆ • (swap⋆ ⨾☐• ☐))) ++↦
            ↦⃖₆ ∷ ↦⃖₃ ∷ ↦⃖₇ ∷ ↦⃖₁ ∷ ↦⃖₃ ∷ ◾
      
      lem : eval (! (c₁ ⊗ c₂)) (eval (c₁ ⊗ c₂) ((x , y) ⃖)) ≡ (x , y) ⃖
      lem rewrite eval-toState₂ rs' = eval-toState₂ rs!
    !rev (c₁ ⊗ c₂) ((x , y) ⃖) refl | inj₁ ((y' , rsy) , _) | inj₂ ((x' , rsx) , _) = lem
      where
      rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ［ c₁ ⊗ c₂ ∣ (x' , y) ∣ ☐ ］▷
      rs' = ↦⃖₉ ∷ appendκ↦* rsy refl ([ c₁ , x ]⊗☐• ☐) ++↦
            ↦⃖₈ ∷ appendκ↦* rsx refl (☐⊗[ c₂ , y' ]• ☐) ++↦
            ↦⃗₈ ∷ Rev* (appendκ↦* rsy refl ([ c₁ , x' ]⊗☐• ☐)) ++↦ ↦⃗₉ ∷ ◾

      rs! : ⟨ ! (c₁ ⊗ c₂) ∣ (x' , y) ∣ ☐ ⟩▷  ↦* ⟨ ! (c₁ ⊗ c₂) ∣ (x , y) ∣ ☐ ⟩◁
      rs! = (↦⃗₃ ∷ ↦⃗₁ ∷ ↦⃗₇ ∷ ↦⃗₃ ∷ ↦⃗₆ ∷ ◾) ++↦
            Rev* (appendκ↦* (getₜᵣ⃖ (! c₂) (!rev c₂ (y ⃖) (eval-toState₂ rsy))) refl (☐⊗[ ! c₁ , x' ]• (☐⨾ swap⋆ • (swap⋆ ⨾☐• ☐)))) ++↦
            ↦⃗₈ ∷ appendκ↦* (getₜᵣ⃗ (! c₁) (!rev c₁ (x ⃖) (eval-toState₂ rsx))) refl ([ ! c₂ , y' ]⊗☐• (☐⨾ swap⋆ • (swap⋆ ⨾☐• ☐))) ++↦
            ↦⃖₈ ∷ appendκ↦* (getₜᵣ⃖ (! c₂) (!rev c₂ (y ⃖) (eval-toState₂ rsy))) refl (☐⊗[ ! c₁ , x ]• (☐⨾ swap⋆ • (swap⋆ ⨾☐• ☐))) ++↦
            ↦⃖₆ ∷ ↦⃖₃ ∷ ↦⃖₇ ∷ ↦⃖₁ ∷ ↦⃖₃ ∷ ◾

      lem : eval (! (c₁ ⊗ c₂)) (eval (c₁ ⊗ c₂) ((x , y) ⃖)) ≡ (x , y) ⃖
      lem rewrite eval-toState₂ rs' = eval-toState₁ rs!
    !rev (c₁ ⊗ c₂) ((x , y) ⃖) refl | inj₂ ((y' , rsy) , _) = lem
      where
      rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ［ c₁ ⊗ c₂ ∣ (x , y') ∣ ☐ ］▷
      rs' = ↦⃖₉ ∷ appendκ↦* rsy refl ([ c₁ , x ]⊗☐• ☐) ++↦ ↦⃗₉ ∷ ◾

      rs! : ⟨ ! (c₁ ⊗ c₂) ∣ (x , y') ∣ ☐ ⟩▷  ↦* ⟨ ! (c₁ ⊗ c₂) ∣ (x , y) ∣ ☐ ⟩◁
      rs! = (↦⃗₃ ∷ ↦⃗₁ ∷ ↦⃗₇ ∷ ↦⃗₃ ∷ ↦⃗₆ ∷ ◾) ++↦
            appendκ↦* (getₜᵣ⃗ (! c₂) (!rev c₂ (y ⃖) (eval-toState₂ rsy))) refl (☐⊗[ ! c₁ , x ]• (☐⨾ swap⋆ • (swap⋆ ⨾☐• ☐))) ++↦
            ↦⃖₆ ∷ ↦⃖₃ ∷ ↦⃖₇ ∷ ↦⃖₁ ∷ ↦⃖₃ ∷ ◾

      lem : eval (! (c₁ ⊗ c₂)) (eval (c₁ ⊗ c₂) ((x , y) ⃖)) ≡ (x , y) ⃖
      lem rewrite eval-toState₂ rs' = eval-toState₁ rs!
    !rev η₊ (inj₁ x ⃖) refl = refl
    !rev η₊ (inj₂ (- x) ⃖) refl = refl
    !rev ε₊ (inj₁ x ⃗) refl = refl
    !rev ε₊ (inj₂ (- x) ⃗) refl = refl

    private
      {-# TERMINATING #-}
      loop₁⃗ : ∀ {A B C a₀} {c₁ : A ↔ B} {b : ⟦ B ⟧} {c₂ : B ↔ C}
             → ⟨ c₁ ⨾ c₂ ∣ a₀ ∣ ☐ ⟩▷ ↦* ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷
             → ［ ! c₂ ⨾ ! c₁ ∣ a₀ ∣ ☐ ］◁ ↦* ⟨ ! c₁ ∣ b ∣ ! c₂ ⨾☐• ☐ ⟩◁
             → ［ ! c₂ ⨾ ! c₁ ∣ a₀ ∣ ☐ ］◁ ↦* (toState! (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (a₀ ⃗)))
      loop₁⃗ {a₀ = a₀} {c₁} {b} {c₂} rs rs! with inspect⊎ (run ⟨ c₂ ∣ b ∣ ☐ ⟩▷) (λ ())
      loop₁⃗ {a₀ = a₀} {c₁} {b} {c₂} rs rs! | inj₁ ((b' , rsb) , eq) = loop₁⃖ rs' rs!'
        where
        rs' : ⟨ c₁ ⨾ c₂ ∣ a₀ ∣ ☐ ⟩▷ ↦* ［ c₁ ∣ b' ∣ ☐⨾ c₂ • ☐ ］◁
        rs' = rs ++↦ ↦⃗₇ ∷ appendκ↦* rsb refl (c₁ ⨾☐• ☐) ++↦ ↦⃖₇ ∷ ◾

        rs!' : ［ ! c₂ ⨾ ! c₁ ∣ a₀ ∣ ☐ ］◁ ↦* ⟨ ! c₁ ∣ b' ∣ ! c₂ ⨾☐• ☐ ⟩▷
        rs!' = rs! ++↦ ↦⃖₇ ∷ Rev* (appendκ↦* (getₜᵣ⃖ (! c₂) (!rev c₂ (b ⃗) (eval-toState₁ rsb))) refl (☐⨾ ! c₁ • ☐)) ++↦ ↦⃗₇ ∷ ◾
      loop₁⃗ {a₀ = a₀} {c₁} {b} {c₂} rs rs! | inj₂ ((c  , rsb) , eq) = lem
        where
        rs' : ⟨ c₁ ⨾ c₂ ∣ a₀ ∣ ☐ ⟩▷ ↦* ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］▷
        rs' = rs ++↦ ↦⃗₇ ∷ appendκ↦* rsb refl (c₁ ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾

        rs!' : ［ ! c₂ ⨾ ! c₁ ∣ a₀ ∣ ☐ ］◁ ↦* ⟨ ! c₂ ⨾ ! c₁ ∣ c ∣ ☐ ⟩◁
        rs!' = rs! ++↦ ↦⃖₇ ∷ Rev* (appendκ↦* (getₜᵣ⃗ (! c₂) (!rev c₂ (b ⃗) (eval-toState₁ rsb))) refl (☐⨾ ! c₁ • ☐)) ++↦ ↦⃖₃ ∷ ◾

        lem : ［ ! c₂ ⨾ ! c₁ ∣ a₀ ∣ ☐ ］◁ ↦* (toState! (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (a₀ ⃗)))
        lem rewrite eval-toState₁ rs' = rs!'
        
      loop₁⃖ : ∀ {A B C a₀} {c₁ : A ↔ B} {b : ⟦ B ⟧} {c₂ : B ↔ C}
             → ⟨ c₁ ⨾ c₂ ∣ a₀ ∣ ☐ ⟩▷ ↦* ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］◁
             → ［ ! c₂ ⨾ ! c₁ ∣ a₀ ∣ ☐ ］◁ ↦* ⟨ ! c₁ ∣ b ∣ ! c₂ ⨾☐• ☐ ⟩▷
             → ［ ! c₂ ⨾ ! c₁ ∣ a₀ ∣ ☐ ］◁ ↦* (toState! (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (a₀ ⃗)))
      loop₁⃖ {a₀ = a₀} {c₁} {b} {c₂} rs rs! with inspect⊎ (run ［ c₁ ∣ b ∣ ☐  ］◁) (λ ())
      loop₁⃖ {a₀ = a₀} {c₁} {b} {c₂} rs rs! | inj₁ ((a  , rsb) , eq) = lem
        where
        rs' : ⟨ c₁ ⨾ c₂ ∣ a₀ ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩◁
        rs' = rs ++↦ appendκ↦* rsb refl (☐⨾ c₂ • ☐) ++↦ ↦⃖₃ ∷ ◾

        rs!' : ［ ! c₂ ⨾ ! c₁ ∣ a₀ ∣ ☐ ］◁ ↦* ［ ! c₂ ⨾ ! c₁ ∣ a ∣ ☐ ］▷
        rs!' = rs! ++↦ Rev* (appendκ↦* (getₜᵣ⃖ (! c₁) (!rev c₁ (b ⃖) (eval-toState₂ rsb))) refl (! c₂ ⨾☐• ☐)) ++↦ ↦⃗₁₀ ∷ ◾

        lem : ［ ! c₂ ⨾ ! c₁ ∣ a₀ ∣ ☐ ］◁ ↦* (toState! (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (a₀ ⃗)))
        lem rewrite eval-toState₁ rs' = rs!'
      loop₁⃖ {a₀ = a₀} {c₁} {b} {c₂} rs rs! | inj₂ ((b' , rsb) , eq) = loop₁⃗ rs' rs!'
        where
        rs' : ⟨ c₁ ⨾ c₂ ∣ a₀ ∣ ☐ ⟩▷ ↦* ［ c₁ ∣ b' ∣ ☐⨾ c₂ • ☐ ］▷
        rs' = rs ++↦ appendκ↦* rsb refl (☐⨾ c₂ • ☐)

        rs!' : ［ ! c₂ ⨾ ! c₁ ∣ a₀ ∣ ☐ ］◁ ↦* ⟨ ! c₁ ∣ b' ∣ ! c₂ ⨾☐• ☐ ⟩◁
        rs!' = rs! ++↦ Rev* (appendκ↦* (getₜᵣ⃗ (! c₁) (!rev c₁ (b ⃖) (eval-toState₂ rsb))) refl (! c₂ ⨾☐• ☐))

      loop₂⃗ : ∀ {A B C c₀} {c₁ : A ↔ B} {b : ⟦ B ⟧} {c₂ : B ↔ C}
             → ［ c₁ ⨾ c₂ ∣ c₀ ∣ ☐ ］◁ ↦* ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷
             →  ⟨ ! c₂ ⨾ ! c₁ ∣ c₀ ∣ ☐ ⟩▷ ↦* ⟨ ! c₁ ∣ b ∣ ! c₂ ⨾☐• ☐ ⟩◁
             →  ⟨ ! c₂ ⨾ ! c₁ ∣ c₀ ∣ ☐ ⟩▷ ↦* (toState! (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (c₀ ⃖)))
      loop₂⃗ {c₀ = c₀} {c₁} {b} {c₂} rs rs! with inspect⊎ (run ⟨ c₂ ∣ b ∣ ☐ ⟩▷) (λ ())
      loop₂⃗ {c₀ = c₀} {c₁} {b} {c₂} rs rs! | inj₁ ((b' , rsb) , eq) = loop₂⃖ rs' rs!'
        where
        rs' : ［ c₁ ⨾ c₂ ∣ c₀ ∣ ☐ ］◁ ↦* ［ c₁ ∣ b' ∣ ☐⨾ c₂ • ☐ ］◁
        rs' = rs ++↦ ↦⃗₇ ∷ appendκ↦* rsb refl (c₁ ⨾☐• ☐) ++↦ ↦⃖₇ ∷ ◾

        rs!' : ⟨ ! c₂ ⨾ ! c₁ ∣ c₀ ∣ ☐ ⟩▷ ↦* ⟨ ! c₁ ∣ b' ∣ ! c₂ ⨾☐• ☐ ⟩▷
        rs!' = rs! ++↦ ↦⃖₇ ∷ Rev* (appendκ↦* (getₜᵣ⃖ (! c₂) (!rev c₂ (b ⃗) (eval-toState₁ rsb))) refl (☐⨾ ! c₁ • ☐)) ++↦ ↦⃗₇ ∷ ◾
      loop₂⃗ {c₀ = c₀} {c₁} {b} {c₂} rs rs! | inj₂ ((c  , rsb) , eq) = lem
        where
        rs' : ［ c₁ ⨾ c₂ ∣ c₀ ∣ ☐ ］◁ ↦* ［ c₁ ⨾ c₂  ∣ c ∣ ☐ ］▷
        rs' = rs ++↦ ↦⃗₇ ∷ appendκ↦* rsb refl (c₁ ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾

        rs!' : ⟨ ! c₂ ⨾ ! c₁ ∣ c₀ ∣ ☐ ⟩▷ ↦* ⟨ ! c₂ ⨾ ! c₁ ∣ c ∣ ☐ ⟩◁
        rs!' = rs! ++↦ ↦⃖₇ ∷ Rev* (appendκ↦* (getₜᵣ⃗ (! c₂) (!rev c₂ (b ⃗) (eval-toState₁ rsb))) refl (☐⨾ ! c₁ • ☐)) ++↦ ↦⃖₃ ∷ ◾

        lem : ⟨ ! c₂ ⨾ ! c₁ ∣ c₀ ∣ ☐ ⟩▷ ↦* (toState! (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (c₀ ⃖)))
        lem rewrite eval-toState₂ rs' = rs!'

      loop₂⃖ : ∀ {A B C c₀} {c₁ : A ↔ B} {b : ⟦ B ⟧} {c₂ : B ↔ C}
             → ［ c₁ ⨾ c₂ ∣ c₀ ∣ ☐ ］◁ ↦* ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］◁
             →  ⟨ ! c₂ ⨾ ! c₁ ∣ c₀ ∣ ☐ ⟩▷ ↦* ⟨ ! c₁ ∣ b ∣ ! c₂ ⨾☐• ☐ ⟩▷
             →  ⟨ ! c₂ ⨾ ! c₁ ∣ c₀ ∣ ☐ ⟩▷ ↦* (toState! (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (c₀ ⃖)))
      loop₂⃖ {c₀ = c₀} {c₁} {b} {c₂} rs rs! with inspect⊎ (run ［ c₁ ∣ b ∣ ☐  ］◁) (λ ())
      loop₂⃖ {c₀ = c₀} {c₁} {b} {c₂} rs rs! | inj₁ ((a  , rsb) , eq) = lem
        where
        rs' : ［ c₁ ⨾ c₂ ∣ c₀ ∣ ☐ ］◁ ↦* ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩◁
        rs' = rs ++↦ appendκ↦* rsb refl (☐⨾ c₂ • ☐) ++↦ ↦⃖₃ ∷ ◾

        rs!' : ⟨ ! c₂ ⨾ ! c₁ ∣ c₀ ∣ ☐ ⟩▷ ↦* ［ ! c₂ ⨾ ! c₁ ∣ a ∣ ☐ ］▷
        rs!' = rs! ++↦ Rev* (appendκ↦* (getₜᵣ⃖ (! c₁) (!rev c₁ (b ⃖) (eval-toState₂ rsb))) refl (! c₂ ⨾☐• ☐)) ++↦ ↦⃗₁₀ ∷ ◾

        lem : ⟨ ! c₂ ⨾ ! c₁ ∣ c₀ ∣ ☐ ⟩▷ ↦* (toState! (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (c₀ ⃖)))
        lem rewrite eval-toState₂ rs' = rs!'
      loop₂⃖ {c₀ = c₀} {c₁} {b} {c₂} rs rs! | inj₂ ((b' , rsb) , eq) = loop₂⃗ rs' rs!'
        where
        rs' : ［ c₁ ⨾ c₂ ∣ c₀ ∣ ☐ ］◁ ↦* ［ c₁ ∣ b' ∣ ☐⨾ c₂ • ☐ ］▷
        rs' = rs ++↦ appendκ↦* rsb refl (☐⨾ c₂ • ☐)

        rs!' : ⟨ ! c₂ ⨾ ! c₁ ∣ c₀ ∣ ☐ ⟩▷ ↦* ⟨ ! c₁ ∣ b' ∣ ! c₂ ⨾☐• ☐ ⟩◁
        rs!' = rs! ++↦ Rev* (appendκ↦* (getₜᵣ⃗ (! c₁) (!rev c₁ (b ⃖) (eval-toState₂ rsb))) refl (! c₂ ⨾☐• ☐))

  pinv₁ : ∀ {A B} → (c : A ↔ B) → eval ((c ⨾ ! c) ⨾ c) ∼ eval c
  pinv₁ c (x ⃗) with inspect⊎ (run ⟨ c ∣ x ∣ ☐ ⟩▷) (λ ())
  pinv₁ c (x ⃗) | inj₁ ((x' , rs) , eq) = trans (eval-toState₁ rs') (sym (eval-toState₁ rs))
    where
    rs' : ⟨ (c ⨾ ! c) ⨾ c ∣ x ∣ ☐ ⟩▷ ↦* ⟨ (c ⨾ ! c) ⨾ c ∣ x' ∣ ☐ ⟩◁
    rs' = (↦⃗₃ ∷ ↦⃗₃ ∷ ◾) ++↦ appendκ↦* rs refl (☐⨾(! c) • ☐⨾ c • ☐) ++↦ ↦⃖₃ ∷ ↦⃖₃ ∷ ◾
  pinv₁ c (x ⃗) | inj₂ ((x' , rs) , eq) = trans (eval-toState₁ rs') (sym (eval-toState₁ rs))
    where
    rs! : ⟨ ! c ∣ x' ∣ ☐ ⟩▷ ↦* ［ ! c ∣ x ∣ ☐ ］▷
    rs! = getₜᵣ⃗ _ (!rev c (x ⃗) (eval-toState₁ rs))
    
    rs' : ⟨ (c ⨾ ! c) ⨾ c ∣ x ∣ ☐ ⟩▷ ↦* ［ (c ⨾ ! c) ⨾ c ∣ x' ∣ ☐ ］▷
    rs' = (↦⃗₃ ∷ ↦⃗₃ ∷ ◾) ++↦ appendκ↦* rs refl (☐⨾(! c) • ☐⨾ c • ☐) ++↦
          (↦⃗₇ ∷ ◾) ++↦ appendκ↦* rs! refl (c ⨾☐• (☐⨾ c • ☐)) ++↦
          (↦⃗₁₀ ∷ ↦⃗₇ ∷ ◾) ++↦ appendκ↦* rs refl ((c ⨾ ! c) ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾
  pinv₁ c (x ⃖) with inspect⊎ (run ［ c ∣ x ∣ ☐ ］◁) (λ ())
  pinv₁ c (x ⃖) | inj₁ ((x' , rs) , eq) = trans (eval-toState₂ rs') (sym (eval-toState₂ rs))
    where
    rs! : ［ ! c ∣ x' ∣ ☐ ］◁ ↦* ⟨ ! c ∣ x ∣ ☐ ⟩◁
    rs! = getₜᵣ⃖ _ (!rev c (x ⃖) (eval-toState₂ rs))

    rs' : ［ (c ⨾ ! c) ⨾ c ∣ x ∣ ☐ ］◁ ↦* ⟨ (c ⨾ ! c) ⨾ c ∣ x' ∣ ☐ ⟩◁
    rs' = ↦⃖₁₀ ∷ appendκ↦* rs refl ((c ⨾ ! c) ⨾☐• ☐) ++↦
          (↦⃖₇ ∷ ↦⃖₁₀ ∷ ◾) ++↦ appendκ↦* rs! refl (c ⨾☐• (☐⨾ c • ☐)) ++↦
          (↦⃖₇ ∷ ◾) ++↦ appendκ↦* rs refl (☐⨾(! c) • ☐⨾ c • ☐) ++↦ ↦⃖₃ ∷ ↦⃖₃ ∷ ◾
  pinv₁ c (x ⃖) | inj₂ ((x' , rs) , eq) = trans (eval-toState₂ rs') (sym (eval-toState₂ rs))
    where
    rs' : ［ (c ⨾ ! c) ⨾ c ∣ x ∣ ☐ ］◁ ↦* ［ (c ⨾ ! c) ⨾ c ∣ x' ∣ ☐ ］▷
    rs' = ↦⃖₁₀ ∷ appendκ↦* rs refl ((c ⨾ ! c) ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾

  pinv₂ : ∀ {A B} → (c : A ↔ B) → eval ((! c ⨾ c) ⨾ ! c) ∼ eval (! c)
  pinv₂ c x = trans (∘-resp-≈ (λ z → refl)
                              (∘-resp-≈ (!inv c) (λ z → refl)) x)
                    (pinv₁ (! c) x)
open Inverse public
