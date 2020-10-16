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
open import Data.Nat.Induction
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

-- Helper functions
inspect⊎ : ∀ {ℓ ℓ' ℓ''} {P : Set ℓ} {Q : Set ℓ'} {R : Set ℓ''}
         → (f : P → Q ⊎ R) → (p : P) → (∃[ q ] (inj₁ q ≡ f p)) ⊎ (∃[ r ] (inj₂ r ≡ f p))
inspect⊎ f p with f p
... | inj₁ q = inj₁ (q , refl)
... | inj₂ r = inj₂ (r , refl)

toState : ∀ {A B} → (c : A ↔ B) → Val B A → State
toState c (b ⃗) = ［ c ∣ b ∣ ☐ ］▷
toState c (a ⃖) = ⟨ c ∣ a ∣ ☐ ⟩◁

is-stuck-toState : ∀ {A B} → (c : A ↔ B) → (v : Val B A) → is-stuck (toState c v)
is-stuck-toState c (b ⃗) = λ ()
is-stuck-toState c (a ⃖) = λ ()

toState≡₁ : ∀ {A B b} {c : A ↔ B} {x : Val B A} → toState c x ≡ ［ c ∣ b ∣ ☐ ］▷ → x ≡ b ⃗
toState≡₁ {x = x ⃗} refl = refl

toState≡₂ : ∀ {A B a} {c : A ↔ B} {x : Val B A} → toState c x ≡ ⟨ c ∣ a ∣ ☐ ⟩◁ → x ≡ a ⃖
toState≡₂ {x = x ⃖} refl = refl

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

getₜᵣ⃗ : ∀ {A B} → (c : A ↔ B) → {v : ⟦ A ⟧} {v' : Val B A} → eval c (v ⃗) ≡ v'
       → ⟨ c ∣ v ∣ ☐ ⟩▷ ↦* toState c v'
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
       → ［ c ∣ v ∣ ☐ ］◁ ↦* toState c v'
getₜᵣ⃖ c {v} {v'} eq with inspect⊎ (run ［ c ∣ v ∣ ☐ ］◁) (λ ())
getₜᵣ⃖ c {v} {v' ⃗} eq | inj₁ ((v'' , rs) , eq') with trans (subst (λ x → (v'' ⃖) ≡ [ _⃖ ∘ proj₁ ,  _⃗ ∘ proj₁ ]′ x) eq' refl) eq
... | ()
getₜᵣ⃖ c {v} {v' ⃖} eq | inj₁ ((v'' , rs) , eq') with trans (subst (λ x → (v'' ⃖) ≡ [ _⃖ ∘ proj₁ ,  _⃗ ∘ proj₁ ]′ x) eq' refl) eq
... | refl = rs
getₜᵣ⃖ c {v} {v' ⃗} eq | inj₂ ((v'' , rs) , eq') with trans (subst (λ x → (v'' ⃗) ≡ [ _⃖ ∘ proj₁ ,  _⃗ ∘ proj₁ ]′ x) eq' refl) eq
... | refl = rs
getₜᵣ⃖ c {v} {v' ⃖} eq | inj₂ ((v'' , rs) , eq') with trans (subst (λ x → (v'' ⃗) ≡ [ _⃖ ∘ proj₁ ,  _⃗ ∘ proj₁ ]′ x) eq' refl) eq
... | ()

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
    eval≡interp (c₁ ⨾ c₂) (a ⃗) with interp c₁ (a ⃗) | inspect (interp c₁) (a ⃗)
    eval≡interp (c₁ ⨾ c₂) (a ⃗) | b ⃗  | [ eq ] = (proj₁ (loop (len↦ rs') b) rs' refl)
      where
      rs : ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩▷ ↦* toState (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (a ⃗))
      rs = getₜᵣ⃗ (c₁ ⨾ c₂) refl
      
      rs' : ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷ ↦* toState (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (a ⃗))
      rs' = proj₁ (deterministic*' (↦⃗₃ ∷ appendκ↦* ((getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (a ⃗)) eq))) refl (☐⨾ c₂ • ☐)) rs (is-stuck-toState _ _))
    eval≡interp (c₁ ⨾ c₂) (a ⃗) | a' ⃖ | [ eq ] = eval-toState₁ rs
      where
      rs : ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⨾ c₂ ∣ a' ∣ ☐ ⟩◁
      rs = ↦⃗₃ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (a ⃗)) eq)) refl (☐⨾ c₂ • ☐) ++↦ ↦⃖₃ ∷ ◾
    eval≡interp (c₁ ⨾ c₂) (c ⃖) with interp c₂ (c ⃖) | inspect (interp c₂) (c ⃖)
    eval≡interp (c₁ ⨾ c₂) (c ⃖) | b ⃖ | [ eq' ] = proj₂ (loop (len↦ rs') b) rs' refl
      where
      rs : ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］◁ ↦* toState (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (c ⃖))
      rs = getₜᵣ⃖ (c₁ ⨾ c₂) refl
      
      rs' : ⟨ c₂ ∣ b ∣ c₁ ⨾☐• ☐ ⟩◁ ↦* toState (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (c ⃖))
      rs' = proj₁ (deterministic*' (↦⃖₁₀ ∷ appendκ↦* ((getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (c ⃖)) eq'))) refl (c₁ ⨾☐• ☐)) rs (is-stuck-toState _ _))
    eval≡interp (c₁ ⨾ c₂) (c ⃖) | (c' ⃗) | [ eq ] = eval-toState₂ rs
      where
      rs : ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］◁ ↦* ［ c₁ ⨾ c₂ ∣ c' ∣ ☐ ］▷
      rs = ↦⃖₁₀ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (c ⃖)) eq)) refl (c₁ ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾
    eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) with interp c₁ (x ⃗) | inspect (interp c₁) (x ⃗)
    eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) | x' ⃗ | [ eq ] = eval-toState₁ rs
      where
      rs : ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷ ↦* ［ c₁ ⊕ c₂ ∣ inj₁ x' ∣ ☐ ］▷
      rs = ↦⃗₄ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq)) refl (☐⊕ c₂ • ☐) ++↦ ↦⃗₁₁ ∷ ◾
    eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) | x' ⃖ | [ eq ] = eval-toState₁ rs
      where
      rs : ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₁ x' ∣ ☐ ⟩◁
      rs = ↦⃗₄ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq)) refl (☐⊕ c₂ • ☐) ++↦ ↦⃖₄ ∷ ◾
    eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) with interp c₂ (y ⃗) | inspect (interp c₂) (y ⃗)
    eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) | y' ⃗ | [ eq ] = eval-toState₁ rs
      where
      rs : ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷ ↦* ［ c₁ ⊕ c₂ ∣ inj₂ y' ∣ ☐ ］▷
      rs = ↦⃗₅ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq)) refl (c₁ ⊕☐• ☐) ++↦ ↦⃗₁₂ ∷ ◾
    eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) | y' ⃖ | [ eq ] = eval-toState₁ rs
      where
      rs : ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₂ y' ∣ ☐ ⟩◁
      rs = ↦⃗₅ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq)) refl (c₁ ⊕☐• ☐) ++↦ ↦⃖₅ ∷ ◾
    eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) with interp c₁ (x ⃖) | inspect (interp c₁) (x ⃖)
    eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) | x' ⃗ | [ eq ] = eval-toState₂ rs
      where
      rs : ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁ ↦* ［ c₁ ⊕ c₂ ∣ inj₁ x' ∣ ☐ ］▷
      rs = ↦⃖₁₁ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq)) refl (☐⊕ c₂ • ☐) ++↦ ↦⃗₁₁ ∷ ◾
    eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) | x' ⃖ | [ eq ] = eval-toState₂ rs
      where
      rs : ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₁ x' ∣ ☐ ⟩◁
      rs = ↦⃖₁₁ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq)) refl (☐⊕ c₂ • ☐) ++↦ ↦⃖₄ ∷ ◾
    eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) with interp c₂ (y ⃖) | inspect (interp c₂) (y ⃖)
    eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) | y' ⃖ | [ eq ] = eval-toState₂ rs
      where
      rs : ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₂ y' ∣ ☐ ⟩◁
      rs = ↦⃖₁₂ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq)) refl (c₁ ⊕☐• ☐) ++↦ ↦⃖₅ ∷ ◾
    eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) | y' ⃗ | [ eq ] = eval-toState₂ rs
      where
      rs : ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁ ↦* ［ c₁ ⊕ c₂ ∣ inj₂ y' ∣ ☐ ］▷
      rs = ↦⃖₁₂ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq)) refl (c₁ ⊕☐• ☐) ++↦ ↦⃗₁₂ ∷ ◾
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) with interp c₁ (x ⃗) | inspect (interp c₁) (x ⃗)
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | x₁ ⃗ | [ eq₁ ] with interp c₂ (y ⃗) | inspect (interp c₂) (y ⃗)
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | x₁ ⃗ | [ eq₁ ] | y₁ ⃗ | [ eq₂ ] = eval-toState₁ rs'
      where
      rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ［ c₁ ⊗ c₂ ∣ (x₁ , y₁) ∣ ☐ ］▷
      rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) refl (☐⊗[ c₂ , y ]• ☐) ++↦
            ↦⃗₈ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₂)) refl ([ c₁ , x₁ ]⊗☐• ☐) ++↦ ↦⃗₉ ∷ ◾
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | x₁ ⃗ | [ eq₁ ] | y₁ ⃖ | [ eq₂ ] = eval-toState₁ rs'
      where
      rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊗ c₂ ∣ (x , y₁) ∣ ☐ ⟩◁
      rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) refl (☐⊗[ c₂ , y ]• ☐) ++↦
            ↦⃗₈ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₂)) refl ([ c₁ , x₁ ]⊗☐• ☐) ++↦
            ↦⃖₈ ∷ Rev* (appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) refl (☐⊗[ c₂ , y₁ ]• ☐)) ++↦ ↦⃖₆ ∷ ◾
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | x₁ ⃖ | [ eq₁ ] = eval-toState₁ rs'
      where
      rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊗ c₂ ∣ (x₁ , y) ∣ ☐ ⟩◁
      rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) refl (☐⊗[ c₂ , y ]• ☐) ++↦ ↦⃖₆ ∷ ◾
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) with interp c₂ (y ⃖) | inspect (interp c₂) (y ⃖)
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | y₁ ⃗ | [ eq₂ ] = eval-toState₂ rs'
      where
      rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ［ c₁ ⊗ c₂ ∣ (x , y₁) ∣ ☐ ］▷
      rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) refl ([ c₁ , x ]⊗☐• ☐) ++↦ ↦⃗₉ ∷ ◾
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | y₁ ⃖ | [ eq₂ ] with interp c₁ (x ⃖) | inspect (interp c₁) (x ⃖)
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | y₁ ⃖ | [ eq₂ ] | x₁ ⃗ | [ eq₁ ] = eval-toState₂ rs'
      where
      rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ［ c₁ ⊗ c₂ ∣ (x₁ , y) ∣ ☐ ］▷
      rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) refl ([ c₁ , x ]⊗☐• ☐) ++↦
            ↦⃖₈ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) refl (☐⊗[ c₂ , y₁ ]• ☐) ++↦
            ↦⃗₈ ∷ Rev* (appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) refl ([ c₁ , x₁ ]⊗☐• ☐)) ++↦ ↦⃗₉ ∷ ◾
    eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | y₁ ⃖ | [ eq₂ ] | x₁ ⃖ | [ eq₁ ] = eval-toState₂ rs'
      where
      rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ⟨ c₁ ⊗ c₂ ∣ (x₁ , y₁) ∣ ☐ ⟩◁
      rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) refl ([ c₁ , x ]⊗☐• ☐) ++↦
            ↦⃖₈ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) refl (☐⊗[ c₂ , y₁ ]• ☐) ++↦ ↦⃖₆ ∷ ◾
    eval≡interp η₊ (inj₁ x ⃖) = refl
    eval≡interp η₊ (inj₂ (- x) ⃖) = refl
    eval≡interp ε₊ (inj₁ x ⃗) = refl
    eval≡interp ε₊ (inj₂ (- x) ⃗) = refl

    private
      loop : ∀ {A B C x} {c₁ : A ↔ B} {c₂ : B ↔ C} (n : ℕ)
           → ∀ b → ((rs : ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷ ↦* toState (c₁ ⨾ c₂) x) → len↦ rs ≡ n → x ≡ c₁ ⨾[ b ⃗]⨾ c₂)
                 × ((rs : ⟨ c₂ ∣ b ∣ c₁ ⨾☐• ☐ ⟩◁ ↦* toState (c₁ ⨾ c₂) x) → len↦ rs ≡ n → x ≡ c₁ ⨾[ b ⃖]⨾ c₂)
      loop {A} {B} {C} {x} {c₁} {c₂} = <′-rec (λ n → _) loop-rec
        where
        loop-rec : (n : ℕ) → (∀ m → m <′ n → _) → _
        loop-rec n R b = loop₁ , loop₂
          where
          loop₁ : (rs  : ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷ ↦* toState (c₁ ⨾ c₂) x) → len↦ rs ≡ n → x ≡ c₁ ⨾[ b ⃗]⨾ c₂
          loop₁ rs refl with interp c₂ (b ⃗) | inspect (interp c₂) (b ⃗)
          loop₁ rs refl | c ⃗   | [ eq ] = toState≡₁ (deterministic* rs rsb→c (is-stuck-toState _ _) (λ ()))
            where
            rsb→c : ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷ ↦* ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］▷
            rsb→c = ↦⃗₇ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (b ⃗)) eq)) refl (c₁ ⨾☐• ☐) ++↦ (↦⃗₁₀ ∷ ◾)
          loop₁ rs refl | b' ⃖  | [ eq ] = proj₂ (R (len↦ rsb') le b') rsb' refl
            where
            rsb→b' : ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷ ↦* ⟨ c₂ ∣ b' ∣ c₁ ⨾☐• ☐ ⟩◁
            rsb→b' = ↦⃗₇ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (b ⃗)) eq)) refl (c₁ ⨾☐• ☐)

            rsb' : ⟨ c₂ ∣ b' ∣ c₁ ⨾☐• ☐ ⟩◁ ↦* toState (c₁ ⨾ c₂) x
            rsb' = proj₁ (deterministic*' rsb→b' rs (is-stuck-toState _ _))

            req : len↦ rs ≡ len↦ rsb→b' + len↦ rsb'
            req = proj₂ (deterministic*' rsb→b' rs (is-stuck-toState _ _))

            le : len↦ rsb' <′ len↦ rs
            le rewrite req = s≤′s (n≤′m+n _ _)

          loop₂ : (rs : ⟨ c₂ ∣ b ∣ c₁ ⨾☐• ☐ ⟩◁ ↦* toState (c₁ ⨾ c₂) x) → len↦ rs ≡ n → x ≡ c₁ ⨾[ b ⃖]⨾ c₂
          loop₂ rs refl with interp c₁ (b ⃖) | inspect (interp c₁) (b ⃖)
          loop₂ rs refl | a' ⃖ | [ eq ] = toState≡₂ (deterministic* rs rsb→a (is-stuck-toState _ _) (λ ()))
            where
            rsb→a : ⟨ c₂ ∣ b ∣ c₁ ⨾☐• ☐ ⟩◁ ↦* ⟨ c₁ ⨾ c₂ ∣ a' ∣ ☐ ⟩◁
            rsb→a = ↦⃖₇ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (b ⃖)) eq)) refl (☐⨾ c₂ • ☐) ++↦ (↦⃖₃ ∷ ◾)
          loop₂ rs refl | b' ⃗ | [ eq ] = proj₁ (R (len↦ rsb') le b') rsb' refl
            where
            rsb→b' : ⟨ c₂ ∣ b ∣ c₁ ⨾☐• ☐ ⟩◁ ↦* ［ c₁ ∣ b' ∣ ☐⨾ c₂ • ☐ ］▷
            rsb→b' = ↦⃖₇ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (b ⃖)) eq)) refl (☐⨾ c₂ • ☐)

            rsb' : ［ c₁ ∣ b' ∣ ☐⨾ c₂ • ☐ ］▷ ↦* toState (c₁ ⨾ c₂) x
            rsb' = proj₁ (deterministic*' rsb→b' rs (is-stuck-toState _ _))

            req : len↦ rs ≡ len↦ rsb→b' + len↦ rsb'
            req = proj₂ (deterministic*' rsb→b' rs (is-stuck-toState _ _))

            le : len↦ rsb' <′ len↦ rs
            le rewrite req = s≤′s (n≤′m+n _ _)

open eval≡interp public

module ∘-resp-≈ {A B C : 𝕌} {g i : B ↔ C} {f h : A ↔ B} (g~i : eval g ∼ eval i) (f~h : eval f ∼ eval h) where
  private
    loop : ∀ {x} (n : ℕ) → ∀ b
         → ((rs : ［ f ∣ b ∣ ☐⨾ g • ☐ ］▷ ↦* toState (f ⨾ g) x) → len↦ rs ≡ n → ［ h ∣ b ∣ ☐⨾ i • ☐ ］▷ ↦* toState (h ⨾ i) x)
         × ((rs : ⟨ g ∣ b ∣ f ⨾☐• ☐ ⟩◁ ↦* toState (f ⨾ g) x) → len↦ rs ≡ n → ⟨ i ∣ b ∣ h ⨾☐• ☐ ⟩◁ ↦* toState (h ⨾ i) x)
    loop {x} = <′-rec (λ n → _) loop-rec
      where
      loop-rec : (n : ℕ) → (∀ m → m <′ n → _) → _
      loop-rec n R b = loop₁ , loop₂
        where
        loop₁ : (rs : ［ f ∣ b ∣ ☐⨾ g • ☐ ］▷ ↦* toState (f ⨾ g) x) → len↦ rs ≡ n → ［ h ∣ b ∣ ☐⨾ i • ☐ ］▷ ↦* toState (h ⨾ i) x
        loop₁ rs refl with inspect⊎ (run ⟨ g ∣ b ∣ ☐ ⟩▷) (λ ())
        loop₁ rs refl | inj₁ ((b₁ , rs₁) , eq₁) = ↦⃗₇ ∷ appendκ↦* rs₂ refl (h ⨾☐• ☐) ++↦ proj₂ (R (len↦ rs₁'') le b₁) rs₁'' refl
          where
          rs₁' : ［ f ∣ b ∣ ☐⨾ g • ☐ ］▷ ↦* ⟨ g ∣ b₁ ∣ f ⨾☐• ☐ ⟩◁
          rs₁' = ↦⃗₇ ∷ appendκ↦* rs₁ refl (f ⨾☐• ☐)

          rs₂ : ⟨ i ∣ b ∣ ☐ ⟩▷ ↦* ⟨ i ∣ b₁ ∣ ☐ ⟩◁
          rs₂ = getₜᵣ⃗ i (trans (sym (g~i (b ⃗))) (eval-toState₁ rs₁))

          rs₁'' : ⟨ g ∣ b₁ ∣ f ⨾☐• ☐ ⟩◁ ↦* toState (f ⨾ g) x
          rs₁'' = proj₁ (deterministic*' rs₁' rs (is-stuck-toState _ _))

          req : len↦ rs ≡ len↦ rs₁' + len↦ rs₁''
          req = proj₂ (deterministic*' rs₁' rs (is-stuck-toState _ _))

          le : len↦ rs₁'' <′ len↦ rs
          le = subst (λ x → len↦ rs₁'' <′ x) (sym req) (s≤′s (n≤′m+n _ _))
        loop₁ rs refl | inj₂ ((c₁ , rs₁) , eq₁) = rs₂'
          where
          rs₁' : ［ f ∣ b ∣ ☐⨾ g • ☐ ］▷ ↦* ［ f ⨾ g ∣ c₁ ∣ ☐ ］▷
          rs₁' = ↦⃗₇ ∷ appendκ↦* rs₁ refl (f ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾

          rs₂ : ⟨ i ∣ b ∣ ☐ ⟩▷ ↦* ［ i ∣ c₁ ∣ ☐ ］▷
          rs₂ = getₜᵣ⃗ i (trans (sym (g~i (b ⃗))) (eval-toState₁ rs₁))

          xeq : x ≡ c₁ ⃗
          xeq = toState≡₁ (sym (deterministic* rs₁' rs (λ ()) (is-stuck-toState _ _)))

          rs₂' : ［ h ∣ b ∣ ☐⨾ i • ☐ ］▷ ↦* toState (h ⨾ i) x
          rs₂' rewrite xeq = ↦⃗₇ ∷ appendκ↦* rs₂ refl (h ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾
        loop₂ : (rs : ⟨ g ∣ b ∣ f ⨾☐• ☐ ⟩◁ ↦* toState (f ⨾ g) x) → len↦ rs ≡ n → ⟨ i ∣ b ∣ h ⨾☐• ☐ ⟩◁ ↦* toState (h ⨾ i) x
        loop₂ rs refl with inspect⊎ (run ［ f ∣ b ∣ ☐ ］◁) (λ ())
        loop₂ rs refl | inj₁ ((a₁ , rs₁) , eq₁) = rs₂'
          where
          rs₁' : ⟨ g ∣ b ∣ f ⨾☐• ☐ ⟩◁ ↦* ⟨ f ⨾ g ∣ a₁ ∣ ☐ ⟩◁
          rs₁' = ↦⃖₇ ∷ appendκ↦* rs₁ refl (☐⨾ g • ☐) ++↦ ↦⃖₃ ∷ ◾

          rs₂ : ［ h ∣ b ∣ ☐ ］◁ ↦* ⟨ h ∣ a₁ ∣ ☐ ⟩◁
          rs₂ = getₜᵣ⃖ h (trans (sym (f~h (b ⃖))) (eval-toState₂ rs₁))

          xeq : x ≡ a₁ ⃖
          xeq = toState≡₂ (sym (deterministic* rs₁' rs (λ ()) (is-stuck-toState _ _)))

          rs₂' : ⟨ i ∣ b ∣ h ⨾☐• ☐ ⟩◁ ↦* toState (h ⨾ i) x
          rs₂' rewrite xeq = ↦⃖₇ ∷ appendκ↦* rs₂ refl (☐⨾ i • ☐) ++↦ ↦⃖₃ ∷ ◾
        loop₂ rs refl | inj₂ ((b₁ , rs₁) , eq₁) = (↦⃖₇ ∷ appendκ↦* rs₂ refl (☐⨾ i • ☐)) ++↦ proj₁ (R (len↦ rs₁'') le b₁) rs₁'' refl
          where
          rs₁' : ⟨ g ∣ b ∣ f ⨾☐• ☐ ⟩◁ ↦* ［ f ∣ b₁ ∣ ☐⨾ g • ☐ ］▷
          rs₁' = ↦⃖₇ ∷ appendκ↦* rs₁ refl (☐⨾ g • ☐)

          rs₂ : ［ h ∣ b ∣ ☐ ］◁ ↦* ［ h ∣ b₁ ∣ ☐ ］▷
          rs₂ = getₜᵣ⃖ h (trans (sym (f~h (b ⃖))) (eval-toState₂ rs₁))

          rs₁'' : ［ f ∣ b₁ ∣ ☐⨾ g • ☐ ］▷ ↦* toState (f ⨾ g) x
          rs₁'' = proj₁ (deterministic*' rs₁' rs (is-stuck-toState _ _))

          req : len↦ rs ≡ len↦ rs₁' + len↦ rs₁''
          req = proj₂ (deterministic*' rs₁' rs (is-stuck-toState _ _))

          le : len↦ rs₁'' <′ len↦ rs
          le = subst (λ x → len↦ rs₁'' <′ x) (sym req) (s≤′s (n≤′m+n _ _))

  ∘-resp-≈ : eval (f ⨾ g) ∼ eval (h ⨾ i)
  ∘-resp-≈ (a ⃗) with inspect⊎ (run ⟨ f ∣ a ∣ ☐ ⟩▷) (λ ())
  ∘-resp-≈ (a ⃗) | inj₁ ((a₁ , rs₁) , eq₁) = lem
    where
    rs₁' : ⟨ f ⨾ g ∣ a ∣ ☐ ⟩▷ ↦* ⟨ f ⨾ g ∣ a₁ ∣ ☐ ⟩◁
    rs₁' = ↦⃗₃ ∷ appendκ↦* rs₁ refl (☐⨾ g • ☐) ++↦ ↦⃖₃ ∷ ◾

    eq~ : eval h (a ⃗) ≡ (a₁ ⃖)
    eq~ = trans (sym (f~h (a ⃗))) (eval-toState₁ rs₁)

    rs₂' : ⟨ h ⨾ i ∣ a ∣ ☐ ⟩▷ ↦* ⟨ h ⨾ i ∣ a₁ ∣ ☐ ⟩◁
    rs₂' = ↦⃗₃ ∷ appendκ↦* (getₜᵣ⃗ h eq~) refl (☐⨾ i • ☐) ++↦ ↦⃖₃ ∷ ◾

    lem : eval (f ⨾ g) (a ⃗) ≡ eval (h ⨾ i) (a ⃗)
    lem rewrite eval-toState₁ rs₁' | eval-toState₁ rs₂' = refl
  ∘-resp-≈ (a ⃗) | inj₂ ((b₁ , rs₁) , eq₁) = sym (eval-toState₁ rs₂'')
    where
    rs : ⟨ f ⨾ g ∣ a ∣ ☐ ⟩▷ ↦* toState (f ⨾ g) (eval (f ⨾ g) (a ⃗))
    rs = getₜᵣ⃗ (f ⨾ g) refl
    
    rs₁' : ⟨ f ⨾ g ∣ a ∣ ☐ ⟩▷ ↦* ［ f ∣ b₁ ∣ ☐⨾ g • ☐ ］▷
    rs₁' = ↦⃗₃ ∷ appendκ↦* rs₁ refl (☐⨾ g • ☐)

    rs₁'' : ［ f ∣ b₁ ∣ ☐⨾ g • ☐ ］▷ ↦* toState (f ⨾ g) (eval (f ⨾ g) (a ⃗))
    rs₁'' = proj₁ (deterministic*' rs₁' rs (is-stuck-toState _ _))

    eq~ : eval h (a ⃗) ≡ (b₁ ⃗)
    eq~ = trans (sym (f~h (a ⃗))) (eval-toState₁ rs₁)

    rs₂' : ⟨ h ⨾ i ∣ a ∣ ☐ ⟩▷ ↦* ［ h ∣ b₁ ∣ ☐⨾ i • ☐ ］▷
    rs₂' = ↦⃗₃ ∷ appendκ↦* (getₜᵣ⃗ h eq~) refl (☐⨾ i • ☐)

    rs₂'' : ⟨ h ⨾ i ∣ a ∣ ☐ ⟩▷ ↦* toState (h ⨾ i) (eval (f ⨾ g) (a ⃗))
    rs₂'' = rs₂' ++↦ proj₁ (loop (len↦ rs₁'') b₁) rs₁'' refl
  ∘-resp-≈ (c ⃖) with inspect⊎ (run ［ g ∣ c ∣ ☐ ］◁) (λ ())
  ∘-resp-≈ (c ⃖) | inj₁ ((b₁ , rs₁) , eq₁) = sym (eval-toState₂ rs₂'')
    where
    rs : ［ f ⨾ g ∣ c ∣ ☐ ］◁ ↦* toState (f ⨾ g) (eval (f ⨾ g) (c ⃖))
    rs = getₜᵣ⃖ (f ⨾ g) refl

    rs₁' : ［ f ⨾ g ∣ c ∣ ☐ ］◁ ↦* ⟨ g ∣ b₁ ∣ f ⨾☐• ☐ ⟩◁
    rs₁' = ↦⃖₁₀ ∷ appendκ↦* rs₁ refl (f ⨾☐• ☐)

    rs₁'' : ⟨ g ∣ b₁ ∣ f ⨾☐• ☐ ⟩◁ ↦* toState (f ⨾ g) (eval (f ⨾ g) (c ⃖))
    rs₁'' = proj₁ (deterministic*' rs₁' rs (is-stuck-toState _ _))

    eq~ : eval i (c ⃖) ≡ (b₁ ⃖)
    eq~ = trans (sym (g~i (c ⃖))) (eval-toState₂ rs₁)

    rs₂' : ［ h ⨾ i ∣ c ∣ ☐ ］◁ ↦* ⟨ i ∣ b₁ ∣ h ⨾☐• ☐ ⟩◁
    rs₂' = ↦⃖₁₀ ∷ appendκ↦* (getₜᵣ⃖ i eq~) refl (h ⨾☐• ☐)

    rs₂'' : ［ h ⨾ i ∣ c ∣ ☐ ］◁ ↦* toState (h ⨾ i) (eval (f ⨾ g) (c ⃖))
    rs₂'' = rs₂' ++↦ proj₂ (loop (len↦ rs₁'') b₁) rs₁'' refl
  ∘-resp-≈ (c ⃖) | inj₂ ((c₁ , rs₁) , eq₁) = lem
    where
    rs₁' : ［ f ⨾ g ∣ c ∣ ☐ ］◁ ↦* ［ f ⨾ g ∣ c₁ ∣ ☐ ］▷
    rs₁' = ↦⃖₁₀ ∷ appendκ↦* rs₁ refl (f ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾

    eq~ : eval i (c ⃖) ≡ (c₁ ⃗)
    eq~ = trans (sym (g~i (c ⃖))) (eval-toState₂ rs₁)

    rs₂' : ［ h ⨾ i ∣ c ∣ ☐ ］◁ ↦* ［ h ⨾ i ∣ c₁ ∣ ☐ ］▷
    rs₂' = ↦⃖₁₀ ∷ appendκ↦* (getₜᵣ⃖ i eq~) refl (h ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾

    lem : eval (f ⨾ g) (c ⃖) ≡ eval (h ⨾ i) (c ⃖)
    lem rewrite eval-toState₂ rs₁' | eval-toState₂ rs₂' = refl

open ∘-resp-≈ public

module ∘-resp-≈ᵢ {A B C : 𝕌} {g i : B ↔ C} {f h : A ↔ B} (g~i : interp g ∼ interp i) (f~h : interp f ∼ interp h) where
  ∘-resp-≈ᵢ : interp (f ⨾ g) ∼ interp (h ⨾ i)
  ∘-resp-≈ᵢ x = trans  (sym (eval≡interp (f ⨾ g) x))
                (trans (∘-resp-≈ (λ z → trans (eval≡interp g z) (trans (g~i z) (sym (eval≡interp i z))))
                                 (λ z → trans (eval≡interp f z) (trans (f~h z) (sym (eval≡interp h z)))) x)
                       (eval≡interp (h ⨾ i) x))
open ∘-resp-≈ᵢ public

module assoc {A B C D : 𝕌} {f : A ↔ B} {g : B ↔ C} {h : C ↔ D} where
  private
    loop : ∀ {x} (n : ℕ)
         → (∀ b → ((rs : ［ f ∣ b ∣ ☐⨾ g ⨾ h • ☐ ］▷ ↦* toState (f ⨾ (g ⨾ h)) x) → len↦ rs ≡ n → ［ f ∣ b ∣ ☐⨾ g • ☐⨾ h • ☐ ］▷ ↦* toState ((f ⨾ g) ⨾ h) x)
                × ((rs : ⟨ g ∣ b ∣ ☐⨾ h • (f ⨾☐• ☐) ⟩◁ ↦* toState (f ⨾ (g ⨾ h)) x) → len↦ rs ≡ n → ⟨ g ∣ b ∣ f ⨾☐• (☐⨾ h • ☐) ⟩◁ ↦* toState ((f ⨾ g) ⨾ h) x))
         × (∀ c → ((rs : ［ g ∣ c ∣ ☐⨾ h • (f ⨾☐• ☐) ］▷ ↦* toState (f ⨾ (g ⨾ h)) x) → len↦ rs ≡ n → ［ g ∣ c ∣ f ⨾☐• (☐⨾ h • ☐) ］▷ ↦* toState ((f ⨾ g) ⨾ h) x)
                × ((rs : ⟨ h ∣ c ∣ g ⨾☐• (f ⨾☐• ☐) ⟩◁ ↦* toState (f ⨾ (g ⨾ h)) x) → len↦ rs ≡ n → ⟨ h ∣ c ∣ f ⨾ g ⨾☐• ☐ ⟩◁ ↦* toState ((f ⨾ g) ⨾ h) x))
    loop {x} = <′-rec (λ n → _) loop-rec
      where
      loop-rec : (n : ℕ) → (∀ m → m <′ n → _) → _
      loop-rec n R = loop₁ , loop₂
        where
        loop₁ : ∀ b → ((rs : ［ f ∣ b ∣ ☐⨾ g ⨾ h • ☐ ］▷ ↦* toState (f ⨾ (g ⨾ h)) x) → len↦ rs ≡ n → ［ f ∣ b ∣ ☐⨾ g • ☐⨾ h • ☐ ］▷ ↦* toState ((f ⨾ g) ⨾ h) x)
                    × ((rs : ⟨ g ∣ b ∣ ☐⨾ h • (f ⨾☐• ☐) ⟩◁ ↦* toState (f ⨾ (g ⨾ h)) x) → len↦ rs ≡ n → ⟨ g ∣ b ∣ f ⨾☐• (☐⨾ h • ☐) ⟩◁ ↦* toState ((f ⨾ g) ⨾ h) x)
        loop₁ b = loop⃗ , loop⃖
          where
          loop⃗ : (rs : ［ f ∣ b ∣ ☐⨾ g ⨾ h • ☐ ］▷ ↦* toState (f ⨾ (g ⨾ h)) x) → len↦ rs ≡ n → ［ f ∣ b ∣ ☐⨾ g • ☐⨾ h • ☐ ］▷ ↦* toState ((f ⨾ g) ⨾ h) x
          loop⃗ rs refl with inspect⊎ (run ⟨ g ∣ b ∣ ☐ ⟩▷) (λ ())
          loop⃗ rs refl | inj₁ ((b' , rsb) , _) = rs₂' ++↦ proj₂ (proj₁ (R (len↦ rs₁'') le) b') rs₁'' refl
            where
            rs₁' : ［ f ∣ b ∣ ☐⨾ g ⨾ h • ☐ ］▷ ↦* ⟨ g ∣ b' ∣ ☐⨾ h • (f ⨾☐• ☐) ⟩◁
            rs₁' = (↦⃗₇ ∷ ↦⃗₃ ∷ ◾) ++↦ appendκ↦* rsb refl (☐⨾ h • (f ⨾☐• ☐))

            rs₁'' : ⟨ g ∣ b' ∣ ☐⨾ h • (f ⨾☐• ☐) ⟩◁ ↦* toState (f ⨾ (g ⨾ h)) x
            rs₁'' = proj₁ (deterministic*' rs₁' rs (is-stuck-toState _ _))

            rs₂' : ［ f ∣ b ∣ ☐⨾ g • ☐⨾ h • ☐ ］▷ ↦* ⟨ g ∣ b' ∣ f ⨾☐• (☐⨾ h • ☐) ⟩◁
            rs₂' = ↦⃗₇ ∷ appendκ↦* rsb refl (f ⨾☐• (☐⨾ h • ☐))
            
            req : len↦ rs ≡ len↦ rs₁' + len↦ rs₁''
            req = proj₂ (deterministic*' rs₁' rs (is-stuck-toState _ _))

            le : len↦ rs₁'' <′ len↦ rs
            le = subst (λ x → len↦ rs₁'' <′ x) (sym req) (s≤′s (n≤′m+n _ _))            
          loop⃗ rs refl | inj₂ ((c  , rsb) , _) = rs₂' ++↦ proj₁ (proj₂ (R (len↦ rs₁'') le) c) rs₁'' refl
            where
            rs₁' : ［ f ∣ b ∣ ☐⨾ g ⨾ h • ☐ ］▷ ↦* ［ g ∣ c ∣ ☐⨾ h • (f ⨾☐• ☐) ］▷
            rs₁' = (↦⃗₇ ∷ ↦⃗₃ ∷ ◾) ++↦ appendκ↦* rsb refl (☐⨾ h • (f ⨾☐• ☐))

            rs₁'' : ［ g ∣ c ∣ ☐⨾ h • (f ⨾☐• ☐) ］▷ ↦* toState (f ⨾ (g ⨾ h)) x
            rs₁'' = proj₁ (deterministic*' rs₁' rs (is-stuck-toState _ _))

            rs₂' : ［ f ∣ b ∣ ☐⨾ g • ☐⨾ h • ☐ ］▷ ↦* ［ g ∣ c ∣ f ⨾☐• (☐⨾ h • ☐) ］▷
            rs₂' = ↦⃗₇ ∷ appendκ↦* rsb refl (f ⨾☐• (☐⨾ h • ☐))
            
            req : len↦ rs ≡ len↦ rs₁' + len↦ rs₁''
            req = proj₂ (deterministic*' rs₁' rs (is-stuck-toState _ _))

            le : len↦ rs₁'' <′ len↦ rs
            le = subst (λ x → len↦ rs₁'' <′ x) (sym req) (s≤′s (n≤′m+n _ _))            
          loop⃖ : (rs : ⟨ g ∣ b ∣ ☐⨾ h • (f ⨾☐• ☐) ⟩◁ ↦* toState (f ⨾ (g ⨾ h)) x) → len↦ rs ≡ n → ⟨ g ∣ b ∣ f ⨾☐• (☐⨾ h • ☐) ⟩◁ ↦* toState ((f ⨾ g) ⨾ h) x
          loop⃖ rs refl with inspect⊎ (run ［ f ∣ b ∣ ☐ ］◁) (λ ())
          loop⃖ rs refl | inj₁ ((a  , rsb) , eq) = lem
            where
            rs₁' : ⟨ g ∣ b ∣ ☐⨾ h • (f ⨾☐• ☐) ⟩◁ ↦* ⟨ f ⨾ (g ⨾ h) ∣ a ∣ ☐ ⟩◁
            rs₁' = (↦⃖₃ ∷ ↦⃖₇ ∷ ◾) ++↦ appendκ↦* rsb refl (☐⨾ g ⨾ h • ☐) ++↦ ↦⃖₃ ∷ ◾

            xeq : x ≡ a ⃖
            xeq = toState≡₂ (sym (deterministic* rs₁' rs (λ ()) (is-stuck-toState _ _)))           

            lem : ⟨ g ∣ b ∣ f ⨾☐• (☐⨾ h • ☐) ⟩◁ ↦* toState ((f ⨾ g) ⨾ h) x
            lem rewrite xeq = (↦⃖₇ ∷ ◾) ++↦ appendκ↦* rsb refl (☐⨾ g • ☐⨾ h • ☐) ++↦ ↦⃖₃ ∷ ↦⃖₃ ∷ ◾
          loop⃖ rs refl | inj₂ ((b' , rsb) , eq) = ↦⃖₇ ∷ rs₂' ++↦ proj₁ (proj₁ (R (len↦ rs₁'') le) b') rs₁'' refl
            where
            rs₁' : ⟨ g ∣ b ∣ ☐⨾ h • (f ⨾☐• ☐) ⟩◁ ↦* ［ f ∣ b' ∣ ☐⨾ g ⨾ h • ☐ ］▷
            rs₁' = (↦⃖₃ ∷ ↦⃖₇ ∷ ◾) ++↦ appendκ↦* rsb refl (☐⨾ g ⨾ h • ☐)

            rs₁'' : ［ f ∣ b' ∣ ☐⨾ g ⨾ h • ☐ ］▷ ↦* (toState (f ⨾ g ⨾ h) x)
            rs₁'' = proj₁ (deterministic*' rs₁' rs (is-stuck-toState _ _))

            rs₂' : ［ f ∣ b ∣ ☐⨾ g • ☐⨾ h • ☐ ］◁ ↦* ［ f ∣ b' ∣ ☐⨾ g • (☐⨾ h • ☐) ］▷
            rs₂' = appendκ↦* rsb refl (☐⨾ g • ☐⨾ h • ☐)

            req : len↦ rs ≡ len↦ rs₁' + len↦ rs₁''
            req = proj₂ (deterministic*' rs₁' rs (is-stuck-toState _ _))

            le : len↦ rs₁'' <′ len↦ rs
            le = subst (λ x → len↦ rs₁'' <′ x) (sym req) (s≤′s (n≤′m+n _ _))
        loop₂ : ∀ c → ((rs : ［ g ∣ c ∣ ☐⨾ h • (f ⨾☐• ☐) ］▷ ↦* toState (f ⨾ (g ⨾ h)) x) → len↦ rs ≡ n → ［ g ∣ c ∣ f ⨾☐• (☐⨾ h • ☐) ］▷ ↦* toState ((f ⨾ g) ⨾ h) x)
                    × ((rs : ⟨ h ∣ c ∣ g ⨾☐• (f ⨾☐• ☐) ⟩◁ ↦* toState (f ⨾ (g ⨾ h)) x) → len↦ rs ≡ n → ⟨ h ∣ c ∣ f ⨾ g ⨾☐• ☐ ⟩◁ ↦* toState ((f ⨾ g) ⨾ h) x)
        loop₂ c = loop⃗ , loop⃖
          where
          loop⃗ : (rs : ［ g ∣ c ∣ ☐⨾ h • (f ⨾☐• ☐) ］▷ ↦* toState (f ⨾ (g ⨾ h)) x) → len↦ rs ≡ n → ［ g ∣ c ∣ f ⨾☐• (☐⨾ h • ☐) ］▷ ↦* toState ((f ⨾ g) ⨾ h) x
          loop⃗ rs refl with inspect⊎ (run ⟨ h ∣ c ∣ ☐ ⟩▷) (λ ())
          loop⃗ rs refl | inj₁ ((c' , rsc) , eq) = rs₂' ++↦ proj₂ (proj₂ (R (len↦ rs₁'') le) c') rs₁'' refl
            where
            rs₁' : ［ g ∣ c ∣ ☐⨾ h • (f ⨾☐• ☐) ］▷ ↦* ⟨ h ∣ c' ∣ g ⨾☐• (f ⨾☐• ☐) ⟩◁
            rs₁' = ↦⃗₇ ∷ appendκ↦* rsc refl (g ⨾☐• (f ⨾☐• ☐))

            rs₁'' : ⟨ h ∣ c' ∣ g ⨾☐• (f ⨾☐• ☐) ⟩◁ ↦* (toState (f ⨾ g ⨾ h) x)
            rs₁'' = proj₁ (deterministic*' rs₁' rs (is-stuck-toState _ _))

            rs₂' : ［ g ∣ c ∣ f ⨾☐• (☐⨾ h • ☐) ］▷ ↦* ⟨ h ∣ c' ∣ f ⨾ g ⨾☐• ☐ ⟩◁
            rs₂' = (↦⃗₁₀ ∷ ↦⃗₇ ∷ ◾) ++↦ appendκ↦* rsc refl (f ⨾ g ⨾☐• ☐)

            req : len↦ rs ≡ len↦ rs₁' + len↦ rs₁''
            req = proj₂ (deterministic*' rs₁' rs (is-stuck-toState _ _))

            le : len↦ rs₁'' <′ len↦ rs
            le = subst (λ x → len↦ rs₁'' <′ x) (sym req) (s≤′s (n≤′m+n _ _))
          loop⃗ rs refl | inj₂ ((d  , rsc) , eq) = lem
            where
            rs₁' : ［ g ∣ c ∣ ☐⨾ h • (f ⨾☐• ☐) ］▷ ↦* ［ f ⨾ g ⨾ h ∣ d ∣ ☐ ］▷
            rs₁' = ↦⃗₇ ∷ appendκ↦* rsc refl (g ⨾☐• (f ⨾☐• ☐)) ++↦ ↦⃗₁₀ ∷ ↦⃗₁₀ ∷ ◾

            xeq : x ≡ d ⃗
            xeq = toState≡₁ (sym (deterministic* rs₁' rs (λ ()) (is-stuck-toState _ _)))

            lem : ［ g ∣ c ∣ f ⨾☐• (☐⨾ h • ☐) ］▷ ↦* toState ((f ⨾ g) ⨾ h) x
            lem rewrite xeq = (↦⃗₁₀ ∷ ↦⃗₇ ∷ ◾) ++↦ appendκ↦* rsc refl (f ⨾ g ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾
          loop⃖ : (rs : ⟨ h ∣ c ∣ g ⨾☐• (f ⨾☐• ☐) ⟩◁ ↦* toState (f ⨾ (g ⨾ h)) x) → len↦ rs ≡ n → ⟨ h ∣ c ∣ f ⨾ g ⨾☐• ☐ ⟩◁ ↦* toState ((f ⨾ g) ⨾ h) x
          loop⃖ rs refl with inspect⊎ (run ［ g ∣ c ∣ ☐ ］◁) (λ ())
          loop⃖ rs refl | inj₁ ((b  , rsc) , eq) = rs₂' ++↦ proj₂ (proj₁ (R (len↦ rs₁'') le) b) rs₁'' refl
            where
            rs₁' : ⟨ h ∣ c ∣ g ⨾☐• (f ⨾☐• ☐) ⟩◁ ↦* ⟨ g ∣ b ∣ ☐⨾ h • (f ⨾☐• ☐) ⟩◁
            rs₁' = ↦⃖₇ ∷ appendκ↦* rsc refl (☐⨾ h • (f ⨾☐• ☐))

            rs₁'' : ⟨ g ∣ b ∣ ☐⨾ h • (f ⨾☐• ☐) ⟩◁ ↦* (toState (f ⨾ g ⨾ h) x)
            rs₁'' = proj₁ (deterministic*' rs₁' rs (is-stuck-toState _ _))

            rs₂' : ⟨ h ∣ c ∣ f ⨾ g ⨾☐• ☐ ⟩◁ ↦* ⟨ g ∣ b ∣ f ⨾☐• (☐⨾ h • ☐) ⟩◁
            rs₂' = (↦⃖₇ ∷ ↦⃖₁₀ ∷ ◾) ++↦ appendκ↦* rsc refl (f ⨾☐• (☐⨾ h • ☐))

            req : len↦ rs ≡ len↦ rs₁' + len↦ rs₁''
            req = proj₂ (deterministic*' rs₁' rs (is-stuck-toState _ _))

            le : len↦ rs₁'' <′ len↦ rs
            le = subst (λ x → len↦ rs₁'' <′ x) (sym req) (s≤′s (n≤′m+n _ _))
          loop⃖ rs refl | inj₂ ((c' , rsc) , eq) = rs₂' ++↦ proj₁ (proj₂ (R (len↦ rs₁'') le) c') rs₁'' refl
            where
            rs₁' : ⟨ h ∣ c ∣ g ⨾☐• (f ⨾☐• ☐) ⟩◁ ↦* ［ g ∣ c' ∣ ☐⨾ h • (f ⨾☐• ☐) ］▷
            rs₁' = ↦⃖₇ ∷ appendκ↦* rsc refl (☐⨾ h • (f ⨾☐• ☐))

            rs₁'' : ［ g ∣ c' ∣ ☐⨾ h • (f ⨾☐• ☐) ］▷ ↦* (toState (f ⨾ g ⨾ h) x)
            rs₁'' = proj₁ (deterministic*' rs₁' rs (is-stuck-toState _ _))

            rs₂' : ⟨ h ∣ c ∣ f ⨾ g ⨾☐• ☐ ⟩◁ ↦* ［ g ∣ c' ∣ f ⨾☐• (☐⨾ h • ☐) ］▷
            rs₂' = (↦⃖₇ ∷ ↦⃖₁₀ ∷ ◾) ++↦ appendκ↦* rsc refl (f ⨾☐• (☐⨾ h • ☐))

            req : len↦ rs ≡ len↦ rs₁' + len↦ rs₁''
            req = proj₂ (deterministic*' rs₁' rs (is-stuck-toState _ _))

            le : len↦ rs₁'' <′ len↦ rs
            le = subst (λ x → len↦ rs₁'' <′ x) (sym req) (s≤′s (n≤′m+n _ _))

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
  assoc (a ⃗) | inj₂ ((b₁ , rs₁) , eq₁) = sym (eval-toState₁ rs₂'')
    where
    rs : ⟨ f ⨾ (g ⨾ h) ∣ a ∣ ☐ ⟩▷ ↦* toState (f ⨾ g ⨾ h) (eval (f ⨾ g ⨾ h) (a ⃗))
    rs = getₜᵣ⃗ (f ⨾ g ⨾ h) refl
    
    rs₁' : ⟨ f ⨾ (g ⨾ h) ∣ a ∣ ☐ ⟩▷ ↦* ［ f ∣ b₁ ∣ ☐⨾ g ⨾ h • ☐ ］▷
    rs₁' = ↦⃗₃ ∷ appendκ↦* rs₁ refl (☐⨾ g ⨾ h • ☐)

    rs₁'' : ［ f ∣ b₁ ∣ ☐⨾ g ⨾ h • ☐ ］▷ ↦* toState (f ⨾ g ⨾ h) (eval (f ⨾ g ⨾ h) (a ⃗))
    rs₁'' = proj₁ (deterministic*' rs₁' rs (is-stuck-toState _ _))

    rs₂' : ⟨ (f ⨾ g) ⨾ h ∣ a ∣ ☐ ⟩▷ ↦* ［ f ∣ b₁ ∣ ☐⨾ g • ☐⨾ h • ☐ ］▷
    rs₂' = (↦⃗₃ ∷ ↦⃗₃ ∷ ◾) ++↦ appendκ↦* rs₁ refl (☐⨾ g • ☐⨾ h • ☐)

    rs₂'' : ⟨ (f ⨾ g) ⨾ h ∣ a ∣ ☐ ⟩▷ ↦* toState ((f ⨾ g) ⨾ h) (eval (f ⨾ g ⨾ h) (a ⃗))
    rs₂'' = rs₂' ++↦ proj₁ ((proj₁ (loop (len↦ rs₁''))) b₁) rs₁'' refl
  assoc (d ⃖) with inspect⊎ (run ［ h ∣ d ∣ ☐ ］◁) (λ ())
  assoc (d ⃖) | inj₁ ((c₁ , rs₁) , eq₁) = sym (eval-toState₂ rs₂'')
    where
    rs : ［ f ⨾ (g ⨾ h) ∣ d ∣ ☐ ］◁ ↦* toState (f ⨾ g ⨾ h) (eval (f ⨾ g ⨾ h) (d ⃖))
    rs = getₜᵣ⃖ (f ⨾ g ⨾ h) refl
    
    rs₁' : ［ f ⨾ (g ⨾ h) ∣ d ∣ ☐ ］◁ ↦* ⟨ h ∣ c₁ ∣ g ⨾☐• (f ⨾☐• ☐) ⟩◁
    rs₁' = (↦⃖₁₀ ∷ ↦⃖₁₀ ∷ ◾) ++↦ appendκ↦* rs₁ refl (g ⨾☐• (f ⨾☐• ☐))

    rs₁'' : ⟨ h ∣ c₁ ∣ g ⨾☐• (f ⨾☐• ☐) ⟩◁ ↦* toState (f ⨾ g ⨾ h) (eval (f ⨾ g ⨾ h) (d ⃖))
    rs₁'' = proj₁ (deterministic*' rs₁' rs (is-stuck-toState _ _))

    rs₂' : ［ (f ⨾ g) ⨾ h ∣ d ∣ ☐ ］◁ ↦* ⟨ h ∣ c₁ ∣ f ⨾ g ⨾☐• ☐ ⟩◁
    rs₂' = (↦⃖₁₀ ∷ ◾) ++↦ appendκ↦* rs₁ refl ((f ⨾ g) ⨾☐• ☐)

    rs₂'' : ［ (f ⨾ g) ⨾ h ∣ d ∣ ☐ ］◁ ↦* toState ((f ⨾ g) ⨾ h) (eval (f ⨾ g ⨾ h) (d ⃖))
    rs₂'' = rs₂' ++↦ proj₂ ((proj₂ (loop (len↦ rs₁''))) c₁) rs₁'' refl
  assoc (d ⃖) | inj₂ ((d₁ , rs₁) , eq₁) = lem
    where
    rs₁' : ［ f ⨾ (g ⨾ h) ∣ d ∣ ☐ ］◁ ↦* ［ f ⨾ (g ⨾ h) ∣ d₁ ∣ ☐ ］▷
    rs₁' = (↦⃖₁₀ ∷ ↦⃖₁₀ ∷ ◾) ++↦ appendκ↦* rs₁ refl (g ⨾☐• (f ⨾☐• ☐)) ++↦ ↦⃗₁₀ ∷ ↦⃗₁₀ ∷ ◾

    rs₂' : ［ (f ⨾ g) ⨾ h ∣ d ∣ ☐ ］◁ ↦* ［ (f ⨾ g) ⨾ h ∣ d₁ ∣ ☐ ］▷
    rs₂' = (↦⃖₁₀ ∷ ◾) ++↦ appendκ↦* rs₁ refl ((f ⨾ g) ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾

    lem : eval (f ⨾ g ⨾ h) (d ⃖) ≡ eval ((f ⨾ g) ⨾ h) (d ⃖)
    lem rewrite eval-toState₂ rs₁' | eval-toState₂ rs₂' = refl

open assoc public

module homomorphism {A₁ B₁ A₂ B₂ A₃ B₃} {f : A₁ ↔ A₂}  {g : B₁ ↔ B₂} {h : A₂ ↔ A₃} {i : B₂ ↔ B₃} where
  private
    P₁ : ∀ {x} ℕ → Set _
    P₁ {x} n = ∀ a₂ → ((rs : ［ f ∣ a₂ ∣ ☐⨾ h • (☐⊕ g ⨾ i • ☐) ］▷ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) x) → len↦ rs ≡ n → ［ f  ∣ a₂ ∣ ☐⊕ g • ☐⨾ h ⊕ i • ☐ ］▷ ↦* toState (f ⊕ g ⨾ h ⊕ i) x)
                    × ((rs : ⟨ h ∣ a₂ ∣ f ⨾☐• (☐⊕ (g ⨾ i) • ☐) ⟩◁ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) x) → len↦ rs ≡ n → ⟨ h ∣ a₂ ∣ ☐⊕ i • (f ⊕ g ⨾☐• ☐) ⟩◁ ↦* toState (f ⊕ g ⨾ h ⊕ i) x)
    P₂ : ∀ {x} ℕ → Set _
    P₂ {x} n = ∀ b₂ → ((rs : ［ g ∣ b₂ ∣ ☐⨾ i • (f ⨾ h ⊕☐• ☐) ］▷ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) x) → len↦ rs ≡ n → ［ g ∣ b₂ ∣ f ⊕☐• (☐⨾ h ⊕ i • ☐) ］▷ ↦* toState (f ⊕ g ⨾ h ⊕ i) x)
                    × ((rs : ⟨ i ∣ b₂ ∣ g ⨾☐• (f ⨾ h ⊕☐• ☐) ⟩◁ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) x) → len↦ rs ≡ n → ⟨ i ∣ b₂ ∣ h ⊕☐• (f ⊕ g ⨾☐• ☐) ⟩◁ ↦* toState (f ⊕ g ⨾ h ⊕ i) x)
    
    P : ∀ {x} ℕ → Set _
    P {x} n = P₁ {x} n × P₂ {x} n
                     
    loop : ∀ {x} (n : ℕ) → P {x} n
    loop {x} = <′-rec (λ n → P n) loop-rec
      where
      loop-rec : (n : ℕ) → (∀ m → m <′ n → P m) → P n
      loop-rec n R = loop₁ , loop₂
        where
        loop₁ : P₁ n
        loop₁ a₂ = loop⃗ , loop⃖
          where
          loop⃗ : (rs : ［ f ∣ a₂ ∣ ☐⨾ h • (☐⊕ g ⨾ i • ☐) ］▷ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) x) → len↦ rs ≡ n → ［ f  ∣ a₂ ∣ ☐⊕ g • ☐⨾ h ⊕ i • ☐ ］▷ ↦* toState (f ⊕ g ⨾ h ⊕ i) x
          loop⃗ rs refl with inspect⊎ (run ⟨ h ∣ a₂ ∣ ☐ ⟩▷) (λ ())
          loop⃗ rs refl | inj₁ ((a₂' , rsa) , _) = rs₂' ++↦ proj₂ (proj₁ (R (len↦ rs₁'') le) a₂') rs₁'' refl
            where
            rs₁' : ［ f ∣ a₂ ∣ ☐⨾ h • (☐⊕ g ⨾ i • ☐) ］▷ ↦* ⟨ h ∣ a₂' ∣ f ⨾☐• (☐⊕ (g ⨾ i) • ☐) ⟩◁
            rs₁' = ↦⃗₇ ∷ appendκ↦* rsa refl (f ⨾☐• (☐⊕ g ⨾ i • ☐))

            rs₁'' : ⟨ h ∣ a₂' ∣ f ⨾☐• (☐⊕ (g ⨾ i) • ☐) ⟩◁ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) x
            rs₁'' = proj₁ (deterministic*' rs₁' rs (is-stuck-toState _ _))

            rs₂' : ［ f  ∣ a₂ ∣ ☐⊕ g • ☐⨾ h ⊕ i • ☐ ］▷ ↦* ⟨ h ∣ a₂' ∣ ☐⊕ i • (f ⊕ g ⨾☐• ☐) ⟩◁
            rs₂' = (↦⃗₁₁ ∷ ↦⃗₇ ∷ ↦⃗₄ ∷ ◾) ++↦ appendκ↦* rsa refl (☐⊕ i • (f ⊕ g ⨾☐• ☐))

            req : len↦ rs ≡ len↦ rs₁' + len↦ rs₁''
            req = proj₂ (deterministic*' rs₁' rs (is-stuck-toState _ _))

            le : len↦ rs₁'' <′ len↦ rs
            le = subst (λ x → len↦ rs₁'' <′ x) (sym req) (s≤′s (n≤′m+n _ _))
          loop⃗ rs refl | inj₂ ((a₃  , rsa) , _) = lem
            where
            rs₁' : ［ f ∣ a₂ ∣ ☐⨾ h • (☐⊕ g ⨾ i • ☐) ］▷ ↦* ［ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₁ a₃ ∣ ☐ ］▷
            rs₁' = ↦⃗₇ ∷ appendκ↦* rsa refl (f ⨾☐• (☐⊕ g ⨾ i • ☐)) ++↦ ↦⃗₁₀ ∷ ↦⃗₁₁ ∷ ◾

            xeq : x ≡ inj₁ a₃ ⃗
            xeq = toState≡₁ (deterministic* rs rs₁' (is-stuck-toState _ _) (λ ()))

            lem : ［ f ∣ a₂ ∣ ☐⊕ g • (☐⨾ h ⊕ i • ☐) ］▷ ↦* toState (f ⊕ g ⨾ h ⊕ i) x
            lem rewrite xeq = (↦⃗₁₁ ∷ ↦⃗₇ ∷ ↦⃗₄ ∷ ◾) ++↦ appendκ↦* rsa refl (☐⊕ i • (f ⊕ g ⨾☐• ☐)) ++↦ ↦⃗₁₁ ∷ ↦⃗₁₀ ∷ ◾
          loop⃖ : (rs : ⟨ h ∣ a₂ ∣ f ⨾☐• (☐⊕ (g ⨾ i) • ☐) ⟩◁ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) x) → len↦ rs ≡ n → ⟨ h ∣ a₂ ∣ ☐⊕ i • (f ⊕ g ⨾☐• ☐) ⟩◁ ↦* toState (f ⊕ g ⨾ h ⊕ i) x
          loop⃖ rs refl with inspect⊎ (run ［ f ∣ a₂ ∣ ☐ ］◁) (λ ())
          loop⃖ rs refl | inj₁ ((a₁   , rsa) , _) = lem
            where
            rs₁' : ⟨ h ∣ a₂ ∣ f ⨾☐• (☐⊕ (g ⨾ i) • ☐) ⟩◁ ↦* ⟨ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₁ a₁ ∣ ☐ ⟩◁
            rs₁' = ↦⃖₇ ∷ appendκ↦* rsa refl (☐⨾ h • (☐⊕ g ⨾ i • ☐)) ++↦ ↦⃖₃ ∷ ↦⃖₄ ∷ ◾

            xeq : x ≡ inj₁ a₁ ⃖
            xeq = toState≡₂ (deterministic* rs rs₁' (is-stuck-toState _ _) (λ ()))

            lem : ⟨ h ∣ a₂ ∣ ☐⊕ i • ((f ⊕ g) ⨾☐• ☐) ⟩◁ ↦* toState (f ⊕ g ⨾ h ⊕ i) x
            lem rewrite xeq = (↦⃖₄ ∷ ↦⃖₇ ∷ ↦⃖₁₁ ∷ ◾) ++↦ appendκ↦* rsa refl (☐⊕ g • (☐⨾ h ⊕ i • ☐)) ++↦ ↦⃖₄ ∷ ↦⃖₃ ∷ ◾
          loop⃖ rs refl | inj₂ ((a₂'  , rsa) , _) = rs₂' ++↦ proj₁ (proj₁ (R (len↦ rs₁'') le) a₂') rs₁'' refl
            where
            rs₁' : ⟨ h ∣ a₂ ∣ f ⨾☐• (☐⊕ (g ⨾ i) • ☐) ⟩◁ ↦* ［ f ∣ a₂' ∣ ☐⨾ h • (☐⊕ g ⨾ i • ☐) ］▷
            rs₁' = ↦⃖₇ ∷ appendκ↦* rsa refl (☐⨾ h • (☐⊕ g ⨾ i • ☐))

            rs₁'' : ［ f ∣ a₂' ∣ ☐⨾ h • (☐⊕ g ⨾ i • ☐) ］▷ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) x
            rs₁'' = proj₁ (deterministic*' rs₁' rs (is-stuck-toState _ _))

            rs₂' : ⟨ h ∣ a₂ ∣ ☐⊕ i • ((f ⊕ g) ⨾☐• ☐) ⟩◁ ↦* ［ f  ∣ a₂' ∣ ☐⊕ g • ☐⨾ h ⊕ i • ☐ ］▷
            rs₂' = (↦⃖₄ ∷ ↦⃖₇ ∷ ↦⃖₁₁ ∷ ◾) ++↦ appendκ↦* rsa refl (☐⊕ g • (☐⨾ h ⊕ i • ☐))

            req : len↦ rs ≡ len↦ rs₁' + len↦ rs₁''
            req = proj₂ (deterministic*' rs₁' rs (is-stuck-toState _ _))

            le : len↦ rs₁'' <′ len↦ rs
            le = subst (λ x → len↦ rs₁'' <′ x) (sym req) (s≤′s (n≤′m+n _ _))
        loop₂ : P₂ n
        loop₂ b₂ = loop⃗ , loop⃖
          where
          loop⃗ : (rs : ［ g ∣ b₂ ∣ ☐⨾ i • (f ⨾ h ⊕☐• ☐) ］▷ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) x) → len↦ rs ≡ n → ［ g ∣ b₂ ∣ f ⊕☐• (☐⨾ h ⊕ i • ☐) ］▷ ↦* toState (f ⊕ g ⨾ h ⊕ i) x
          loop⃗ rs refl with inspect⊎ (run ⟨ i ∣ b₂ ∣ ☐ ⟩▷) (λ ())
          loop⃗ rs refl | inj₁ ((b₂' , rsb) , _) = rs₂' ++↦ proj₂ (proj₂ (R (len↦ rs₁'') le) b₂') rs₁'' refl
            where
            rs₁' : ［ g ∣ b₂ ∣ ☐⨾ i • (f ⨾ h ⊕☐• ☐) ］▷ ↦* ⟨ i ∣ b₂' ∣ g ⨾☐• (f ⨾ h ⊕☐• ☐) ⟩◁
            rs₁' = ↦⃗₇ ∷ appendκ↦* rsb refl (g ⨾☐• (f ⨾ h ⊕☐• ☐))

            rs₁'' : ⟨ i ∣ b₂' ∣ g ⨾☐• (f ⨾ h ⊕☐• ☐) ⟩◁ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) x
            rs₁'' = proj₁ (deterministic*' rs₁' rs (is-stuck-toState _ _))

            rs₂' : ［ g ∣ b₂ ∣ f ⊕☐• (☐⨾ h ⊕ i • ☐) ］▷ ↦* ⟨ i ∣ b₂' ∣ h ⊕☐• (f ⊕ g ⨾☐• ☐) ⟩◁
            rs₂' = (↦⃗₁₂ ∷ ↦⃗₇ ∷ ↦⃗₅ ∷ ◾) ++↦ appendκ↦* rsb refl (h ⊕☐• (f ⊕ g ⨾☐• ☐))

            req : len↦ rs ≡ len↦ rs₁' + len↦ rs₁''
            req = proj₂ (deterministic*' rs₁' rs (is-stuck-toState _ _))

            le : len↦ rs₁'' <′ len↦ rs
            le = subst (λ x → len↦ rs₁'' <′ x) (sym req) (s≤′s (n≤′m+n _ _))
          loop⃗ rs refl | inj₂ ((b₃  , rsb) , _) = lem
            where
            rs₁' : ［ g ∣ b₂ ∣ ☐⨾ i • (f ⨾ h ⊕☐• ☐) ］▷ ↦* ［ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₂ b₃ ∣ ☐ ］▷
            rs₁' = ↦⃗₇ ∷ appendκ↦* rsb refl (g ⨾☐• (f ⨾ h ⊕☐• ☐)) ++↦ ↦⃗₁₀ ∷ ↦⃗₁₂ ∷ ◾

            xeq : x ≡ inj₂ b₃ ⃗
            xeq = toState≡₁ (deterministic* rs rs₁' (is-stuck-toState _ _) (λ ()))

            lem : ［ g ∣ b₂ ∣ f ⊕☐• (☐⨾ h ⊕ i • ☐) ］▷ ↦* toState (f ⊕ g ⨾ h ⊕ i) x
            lem rewrite xeq = (↦⃗₁₂ ∷ ↦⃗₇ ∷ ↦⃗₅ ∷ ◾) ++↦ appendκ↦* rsb refl (h ⊕☐• (f ⊕ g ⨾☐• ☐)) ++↦ ↦⃗₁₂ ∷ ↦⃗₁₀ ∷ ◾
          loop⃖ : (rs : ⟨ i ∣ b₂ ∣ g ⨾☐• (f ⨾ h ⊕☐• ☐) ⟩◁ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) x) → len↦ rs ≡ n → ⟨ i ∣ b₂ ∣ h ⊕☐• (f ⊕ g ⨾☐• ☐) ⟩◁ ↦* toState (f ⊕ g ⨾ h ⊕ i) x
          loop⃖ rs refl with inspect⊎ (run ［ g ∣ b₂ ∣ ☐ ］◁) (λ ())
          loop⃖ rs refl | inj₁ ((b₁  , rsb) , _) = lem
            where
            rs₁' : ⟨ i ∣ b₂ ∣ g ⨾☐• (f ⨾ h ⊕☐• ☐) ⟩◁ ↦* ⟨ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₂ b₁ ∣ ☐ ⟩◁
            rs₁' = ↦⃖₇ ∷ appendκ↦* rsb refl (☐⨾ i • (f ⨾ h ⊕☐• ☐)) ++↦ ↦⃖₃ ∷ ↦⃖₅ ∷ ◾

            xeq : x ≡ inj₂ b₁ ⃖
            xeq = toState≡₂ (deterministic* rs rs₁' (is-stuck-toState _ _) (λ ()))

            lem : ⟨ i ∣ b₂ ∣ h ⊕☐• ((f ⊕ g) ⨾☐• ☐) ⟩◁ ↦* toState (f ⊕ g ⨾ h ⊕ i) x
            lem rewrite xeq = (↦⃖₅ ∷ ↦⃖₇ ∷ ↦⃖₁₂ ∷ ◾) ++↦ appendκ↦* rsb refl (f ⊕☐• (☐⨾ h ⊕ i • ☐)) ++↦ ↦⃖₅ ∷ ↦⃖₃ ∷ ◾
          loop⃖ rs refl | inj₂ ((b₂' , rsb) , _) = rs₂' ++↦ proj₁ (proj₂ (R (len↦ rs₁'') le) b₂') rs₁'' refl
            where
            rs₁' : ⟨ i ∣ b₂ ∣ g ⨾☐• (f ⨾ h ⊕☐• ☐) ⟩◁ ↦* ［ g ∣ b₂' ∣ ☐⨾ i • ((f ⨾ h) ⊕☐• ☐) ］▷
            rs₁' = ↦⃖₇ ∷ appendκ↦* rsb refl (☐⨾ i • (f ⨾ h ⊕☐• ☐))

            rs₁'' : ［ g ∣ b₂' ∣ ☐⨾ i • ((f ⨾ h) ⊕☐• ☐) ］▷ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) x
            rs₁'' = proj₁ (deterministic*' rs₁' rs (is-stuck-toState _ _))

            rs₂' : ⟨ i ∣ b₂ ∣ h ⊕☐• ((f ⊕ g) ⨾☐• ☐) ⟩◁ ↦* ［ g ∣ b₂' ∣ f ⊕☐• (☐⨾ h ⊕ i • ☐) ］▷
            rs₂' = (↦⃖₅ ∷ ↦⃖₇ ∷ ↦⃖₁₂ ∷ ◾) ++↦ appendκ↦* rsb refl (f ⊕☐• (☐⨾ h ⊕ i • ☐))

            req : len↦ rs ≡ len↦ rs₁' + len↦ rs₁''
            req = proj₂ (deterministic*' rs₁' rs (is-stuck-toState _ _))

            le : len↦ rs₁'' <′ len↦ rs
            le = subst (λ x → len↦ rs₁'' <′ x) (sym req) (s≤′s (n≤′m+n _ _))

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

    rs₁'' : ［ f ∣ a₂ ∣ ☐⨾ h • (☐⊕ g ⨾ i • ☐) ］▷ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) (eval ((f ⨾ h) ⊕ (g ⨾ i)) (inj₁ a ⃗))
    rs₁'' = proj₁ (deterministic*' rs₁' (getₜᵣ⃗ ((f ⨾ h) ⊕ (g ⨾ i)) refl) (is-stuck-toState _ _))

    rs₂' : ⟨ f ⊕ g ⨾ h ⊕ i ∣ inj₁ a ∣ ☐ ⟩▷ ↦* ［ f ∣ a₂ ∣ ☐⊕ g • (☐⨾ h ⊕ i • ☐) ］▷
    rs₂' = (↦⃗₃ ∷ ↦⃗₄ ∷ ◾) ++↦ appendκ↦* rs refl (☐⊕ g • (☐⨾ h ⊕ i • ☐))

    rs₂'' : ［ f ∣ a₂ ∣ ☐⊕ g • (☐⨾ h ⊕ i • ☐) ］▷ ↦* toState (f ⊕ g ⨾ h ⊕ i) (eval ((f ⨾ h) ⊕ (g ⨾ i)) (inj₁ a ⃗))
    rs₂'' = proj₁ (proj₁ (loop (len↦ rs₁'')) a₂) rs₁'' refl

    lem : eval ((f ⨾ h) ⊕ (g ⨾ i)) (inj₁ a ⃗) ≡ eval (f ⊕ g ⨾ h ⊕ i) (inj₁ a ⃗)
    lem rewrite eval-toState₁ (rs₂' ++↦ rs₂'') = refl
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

    rs₁'' : ［ g ∣ b₂ ∣ ☐⨾ i • (f ⨾ h ⊕☐• ☐) ］▷ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) (eval ((f ⨾ h) ⊕ (g ⨾ i)) (inj₂ b ⃗))
    rs₁'' = proj₁ (deterministic*' rs₁' (getₜᵣ⃗ ((f ⨾ h) ⊕ (g ⨾ i)) refl) (is-stuck-toState _ _))

    rs₂' : ⟨ f ⊕ g ⨾ h ⊕ i ∣ inj₂ b ∣ ☐ ⟩▷ ↦* ［ g ∣ b₂ ∣ f ⊕☐• (☐⨾ h ⊕ i • ☐) ］▷
    rs₂' = (↦⃗₃ ∷ ↦⃗₅ ∷ ◾) ++↦ appendκ↦* rs refl (f ⊕☐• (☐⨾ h ⊕ i • ☐))

    rs₂'' : ［ g ∣ b₂ ∣ f ⊕☐• (☐⨾ h ⊕ i • ☐) ］▷ ↦* toState (f ⊕ g ⨾ h ⊕ i) (eval ((f ⨾ h) ⊕ (g ⨾ i)) (inj₂ b ⃗))
    rs₂'' = proj₁ (proj₂ (loop (len↦ rs₁'')) b₂) rs₁'' refl

    lem : eval ((f ⨾ h) ⊕ (g ⨾ i)) (inj₂ b ⃗) ≡ eval (f ⊕ g ⨾ h ⊕ i) (inj₂ b ⃗)
    lem rewrite eval-toState₁ (rs₂' ++↦ rs₂'') = refl
  homomorphism (inj₁ a ⃖) with inspect⊎ (run ［ h ∣ a ∣ ☐ ］◁) (λ ())
  homomorphism (inj₁ a ⃖) | inj₁ ((a₂ , rs) , eq) = lem
    where
    rs₁' : ［ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₁ a ∣ ☐ ］◁ ↦* ⟨ h ∣ a₂ ∣ f ⨾☐• (☐⊕ (g ⨾ i) • ☐) ⟩◁
    rs₁' = (↦⃖₁₁ ∷ ↦⃖₁₀ ∷ ◾) ++↦ appendκ↦* rs refl (f ⨾☐• (☐⊕ g ⨾ i • ☐))

    rs₁'' : ⟨ h ∣ a₂ ∣ f ⨾☐• (☐⊕ (g ⨾ i) • ☐) ⟩◁ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) (eval ((f ⨾ h) ⊕ (g ⨾ i)) (inj₁ a ⃖))
    rs₁'' = proj₁ (deterministic*' rs₁' (getₜᵣ⃖ ((f ⨾ h) ⊕ (g ⨾ i)) refl) (is-stuck-toState _ _))

    rs₂' : ［ f ⊕ g ⨾ h ⊕ i ∣ inj₁ a ∣ ☐ ］◁ ↦* ⟨ h ∣ a₂ ∣ ☐⊕ i • (f ⊕ g ⨾☐• ☐) ⟩◁
    rs₂' = (↦⃖₁₀ ∷ ↦⃖₁₁ ∷ ◾) ++↦ appendκ↦* rs refl (☐⊕ i • (f ⊕ g ⨾☐• ☐))

    rs₂'' : ⟨ h ∣ a₂ ∣ ☐⊕ i • (f ⊕ g ⨾☐• ☐) ⟩◁ ↦* toState (f ⊕ g ⨾ h ⊕ i) (eval ((f ⨾ h) ⊕ (g ⨾ i)) (inj₁ a ⃖))
    rs₂'' = proj₂ (proj₁ (loop (len↦ rs₁'')) a₂) rs₁'' refl
    
    lem : eval ((f ⨾ h) ⊕ (g ⨾ i)) (inj₁ a ⃖) ≡ eval (f ⊕ g ⨾ h ⊕ i) (inj₁ a ⃖)
    lem rewrite eval-toState₂ (rs₂' ++↦ rs₂'') = refl
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
    rs₁' : ［ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₂ b ∣ ☐ ］◁ ↦* ⟨ i ∣ b₂ ∣ g ⨾☐• (f ⨾ h ⊕☐• ☐) ⟩◁
    rs₁' = (↦⃖₁₂ ∷ ↦⃖₁₀ ∷ ◾) ++↦ appendκ↦* rs refl (g ⨾☐• (f ⨾ h ⊕☐• ☐))

    rs₁'' : ⟨ i ∣ b₂ ∣ g ⨾☐• (f ⨾ h ⊕☐• ☐) ⟩◁ ↦* toState ((f ⨾ h) ⊕ (g ⨾ i)) (eval ((f ⨾ h) ⊕ (g ⨾ i)) (inj₂ b ⃖))
    rs₁'' = proj₁ (deterministic*' rs₁' (getₜᵣ⃖ ((f ⨾ h) ⊕ (g ⨾ i)) refl) (is-stuck-toState _ _))

    rs₂' : ［ f ⊕ g ⨾ h ⊕ i ∣ inj₂ b ∣ ☐ ］◁ ↦* ⟨ i ∣ b₂ ∣ h ⊕☐• (f ⊕ g ⨾☐• ☐) ⟩◁
    rs₂' = (↦⃖₁₀ ∷ ↦⃖₁₂ ∷ ◾) ++↦ appendκ↦* rs refl (h ⊕☐• (f ⊕ g ⨾☐• ☐))

    rs₂'' : ⟨ i ∣ b₂ ∣ h ⊕☐• (f ⊕ g ⨾☐• ☐) ⟩◁ ↦* toState (f ⊕ g ⨾ h ⊕ i) (eval ((f ⨾ h) ⊕ (g ⨾ i)) (inj₂ b ⃖))
    rs₂'' = proj₂ (proj₂ (loop (len↦ rs₁'')) b₂) rs₁'' refl

    lem : eval ((f ⨾ h) ⊕ (g ⨾ i)) (inj₂ b ⃖) ≡ eval (f ⊕ g ⨾ h ⊕ i) (inj₂ b ⃖)
    lem rewrite eval-toState₂ (rs₂' ++↦ rs₂'') = refl
  homomorphism (inj₂ b ⃖) | inj₂ ((b₃ , rs) , eq) = lem
    where
    rs₁' : ［ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₂ b ∣ ☐ ］◁ ↦* ［ (f ⨾ h) ⊕ (g ⨾ i) ∣ inj₂ b₃ ∣ ☐ ］▷
    rs₁' = (↦⃖₁₂ ∷ ↦⃖₁₀ ∷ ◾) ++↦ appendκ↦* rs refl (g ⨾☐• (f ⨾ h ⊕☐• ☐)) ++↦ ↦⃗₁₀ ∷ ↦⃗₁₂ ∷ ◾

    rs₂' : ［ f ⊕ g ⨾ h ⊕ i ∣ inj₂ b ∣ ☐ ］◁ ↦* ［ f ⊕ g ⨾ h ⊕ i ∣ inj₂ b₃ ∣ ☐ ］▷
    rs₂' = (↦⃖₁₀ ∷ ↦⃖₁₂ ∷ ◾) ++↦ appendκ↦* rs refl (h ⊕☐• (f ⊕ g ⨾☐• ☐)) ++↦ ↦⃗₁₂ ∷ ↦⃗₁₀ ∷ ◾

    lem : eval ((f ⨾ h) ⊕ (g ⨾ i)) (inj₂ b ⃖) ≡ eval (f ⊕ g ⨾ h ⊕ i) (inj₂ b ⃖)
    lem rewrite eval-toState₂ rs₁' | eval-toState₂ rs₂' = refl

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
      rs' : ［ c₁ ∣ x' ∣ ☐⨾ c₂ • ☐ ］▷ ↦* toState (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (x ⃗))
      rs' = proj₁ (deterministic*' (↦⃗₃ ∷ appendκ↦* rs refl (☐⨾ c₂ • ☐)) (getₜᵣ⃗ (c₁ ⨾ c₂) refl) (is-stuck-toState _ _))

      rs! : ［ ! c₂ ⨾ ! c₁ ∣ x ∣ ☐ ］◁ ↦* ⟨ ! c₁ ∣ x' ∣ ! c₂ ⨾☐• ☐ ⟩◁
      rs! = ↦⃖₁₀ ∷ Rev* (appendκ↦* (getₜᵣ⃗ (! c₁) (!rev c₁ (x ⃗) (eval-toState₁ rs))) refl (! c₂ ⨾☐• ☐))

      rs!' : ⟨ ! c₁ ∣ x' ∣ ! c₂ ⨾☐• ☐ ⟩◁ ↦* toState! (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (x ⃗))
      rs!' = proj₁ (loop (len↦ rs') x') rs' refl

      lem : eval (! (c₁ ⨾ c₂)) (eval (c₁ ⨾ c₂) (x ⃗)) ≡ x ⃗
      lem with eval (c₁ ⨾ c₂) (x ⃗) | inspect (eval (c₁ ⨾ c₂)) (x ⃗)
      ... | (x'' ⃗) | [ eq ] = eval-toState₁ (Rev* rs!'')
        where
        seq : toState! (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (x ⃗)) ≡ ⟨ ! c₂ ⨾ ! c₁ ∣ x'' ∣ ☐ ⟩◁
        seq rewrite eq = refl
        
        rs!'' : ［ ! c₂ ⨾ ! c₁ ∣ x ∣ ☐ ］◁ ↦* ⟨ ! c₂ ⨾ ! c₁ ∣ x'' ∣ ☐ ⟩◁
        rs!'' = subst (λ st → ［ ! c₂ ⨾ ! c₁ ∣ x ∣ ☐ ］◁ ↦* st) seq (rs! ++↦ rs!')
      ... | (x'' ⃖) | [ eq ] = eval-toState₂ (Rev* rs!'')
        where
        seq : toState! (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (x ⃗)) ≡ ［ ! c₂ ⨾ ! c₁ ∣ x'' ∣ ☐ ］▷
        seq rewrite eq = refl
        
        rs!'' : ［ ! c₂ ⨾ ! c₁ ∣ x ∣ ☐ ］◁ ↦* ［ ! c₂ ⨾ ! c₁ ∣ x'' ∣ ☐ ］▷
        rs!'' = subst (λ st → ［ ! c₂ ⨾ ! c₁ ∣ x ∣ ☐ ］◁ ↦* st) seq (rs! ++↦ rs!')
    !rev (c₁ ⨾ c₂) (x ⃖) refl with inspect⊎ (run ［ c₂ ∣ x ∣ ☐ ］◁) (λ ())
    !rev (c₁ ⨾ c₂) (x ⃖) refl | inj₁ ((x' , rs) , eq) = lem
      where
      rs' : ⟨ c₂ ∣ x' ∣ c₁ ⨾☐• ☐ ⟩◁ ↦* toState (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (x ⃖))
      rs' = proj₁ (deterministic*' (↦⃖₁₀ ∷ appendκ↦* rs refl (c₁ ⨾☐• ☐)) (getₜᵣ⃖ (c₁ ⨾ c₂) refl) (is-stuck-toState _ _))

      rs! :  ⟨ ! c₂ ⨾ ! c₁ ∣ x ∣ ☐ ⟩▷ ↦* ⟨ ! c₁ ∣ x' ∣ ! c₂ ⨾☐• ☐ ⟩▷
      rs! = (↦⃗₃ ∷ ◾) ++↦ Rev* (appendκ↦* (getₜᵣ⃖ (! c₂) (!rev c₂ (x ⃖) (eval-toState₂ rs))) refl (☐⨾ ! c₁ • ☐)) ++↦ ↦⃗₇ ∷ ◾

      rs!' : ⟨ ! c₁ ∣ x' ∣ ! c₂ ⨾☐• ☐ ⟩▷ ↦* toState! (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (x ⃖))
      rs!' = proj₂ (loop (len↦ rs') x') rs' refl

      lem : eval (! (c₁ ⨾ c₂)) (eval (c₁ ⨾ c₂) (x ⃖)) ≡ x ⃖
      lem with eval (c₁ ⨾ c₂) (x ⃖) | inspect (eval (c₁ ⨾ c₂)) (x ⃖)
      ... | (x'' ⃗) | [ eq ] = eval-toState₁ (Rev* rs!'')
        where
        seq : toState! (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (x ⃖)) ≡ ⟨ ! c₂ ⨾ ! c₁ ∣ x'' ∣ ☐ ⟩◁
        seq rewrite eq = refl
        
        rs!'' : ⟨ ! c₂ ⨾ ! c₁ ∣ x ∣ ☐ ⟩▷ ↦* ⟨ ! c₂ ⨾ ! c₁ ∣ x'' ∣ ☐ ⟩◁
        rs!'' = subst (λ st → ⟨ ! c₂ ⨾ ! c₁ ∣ x ∣ ☐ ⟩▷ ↦* st) seq (rs! ++↦ rs!')
      ... | (x'' ⃖) | [ eq ] = eval-toState₂ (Rev* rs!'')
        where
        seq : toState! (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (x ⃖)) ≡ ［ ! c₂ ⨾ ! c₁ ∣ x'' ∣ ☐ ］▷
        seq rewrite eq = refl
        
        rs!'' : ⟨ ! c₂ ⨾ ! c₁ ∣ x ∣ ☐ ⟩▷ ↦* ［ ! c₂ ⨾ ! c₁ ∣ x'' ∣ ☐ ］▷
        rs!'' = subst (λ st → ⟨ ! c₂ ⨾ ! c₁ ∣ x ∣ ☐ ⟩▷ ↦* st) seq (rs! ++↦ rs!')
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
      loop : ∀ {A B C x} {c₁ : A ↔ B}  {c₂ : B ↔ C} (n : ℕ) →
             ∀ b → ((rs : ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷ ↦* toState (c₁ ⨾ c₂) x) →
                    len↦ rs ≡ n →
                    ⟨ ! c₁ ∣ b ∣ ! c₂ ⨾☐• ☐ ⟩◁ ↦* (toState! (c₁ ⨾ c₂) x))
                 × ((rs : ⟨ c₂ ∣ b ∣ c₁ ⨾☐• ☐ ⟩◁ ↦* toState (c₁ ⨾ c₂) x) →
                    len↦ rs ≡ n →
                    ⟨ ! c₁ ∣ b ∣ ! c₂ ⨾☐• ☐ ⟩▷ ↦* (toState! (c₁ ⨾ c₂) x))
      loop {x = x} {c₁} {c₂} = <′-rec (λ n → _) loop-rec
        where
        loop-rec : (n : ℕ) → (∀ m → m <′ n → _) → _
        loop-rec n R b = loop₁ , loop₂
          where
          loop₁ : (rs : ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷ ↦* toState (c₁ ⨾ c₂) x)
                → len↦ rs ≡ n
                → ⟨ ! c₁ ∣ b ∣ ! c₂ ⨾☐• ☐ ⟩◁ ↦* (toState! (c₁ ⨾ c₂) x)
          loop₁ rs refl with inspect⊎ (run ⟨ c₂ ∣ b ∣ ☐ ⟩▷) (λ ())
          loop₁ rs refl | inj₁ ((b' , rsb) , eq) = rs!' ++↦ proj₂ (R (len↦ rs'') le b') rs'' refl
            where
            rs' : ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷ ↦* ⟨ c₂ ∣ b' ∣ c₁ ⨾☐• ☐ ⟩◁
            rs' = ↦⃗₇ ∷ appendκ↦* rsb refl (c₁ ⨾☐• ☐)

            rs'' : ⟨ c₂ ∣ b' ∣ c₁ ⨾☐• ☐ ⟩◁ ↦* toState (c₁ ⨾ c₂) x
            rs'' = proj₁ (deterministic*' rs' rs (is-stuck-toState _ _))

            req : len↦ rs ≡ len↦ rs' + len↦ rs''
            req = proj₂ (deterministic*' rs' rs (is-stuck-toState _ _))

            le : len↦ rs'' <′ len↦ rs
            le = subst (λ x → len↦ rs'' <′ x) (sym req) (s≤′s (n≤′m+n _ _))

            rs!' : ⟨ ! c₁ ∣ b ∣ ! c₂ ⨾☐• ☐ ⟩◁ ↦* ⟨ ! c₁ ∣ b' ∣ ! c₂ ⨾☐• ☐ ⟩▷
            rs!' = ↦⃖₇ ∷ Rev* (appendκ↦* (getₜᵣ⃖ (! c₂) (!rev c₂ (b ⃗) (eval-toState₁ rsb))) refl (☐⨾ ! c₁ • ☐)) ++↦ ↦⃗₇ ∷ ◾
          loop₁ rs refl | inj₂ ((c  , rsb) , eq) = lem
            where
            rs' : ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷ ↦* ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］▷
            rs' = ↦⃗₇ ∷ appendκ↦* rsb refl (c₁ ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾

            rs!' : ⟨ ! c₁ ∣ b ∣ (! c₂) ⨾☐• ☐ ⟩◁ ↦* ⟨ ! c₂ ⨾ ! c₁ ∣ c ∣ ☐ ⟩◁
            rs!' = ↦⃖₇ ∷ Rev* (appendκ↦* (getₜᵣ⃗ (! c₂) (!rev c₂ (b ⃗) (eval-toState₁ rsb))) refl (☐⨾ ! c₁ • ☐)) ++↦ ↦⃖₃ ∷ ◾

            xeq : x ≡ c ⃗
            xeq = toState≡₁ (deterministic* rs rs' (is-stuck-toState _ _) (λ ()))
            
            lem : ⟨ ! c₁ ∣ b ∣ (! c₂) ⨾☐• ☐ ⟩◁ ↦* (toState! (c₁ ⨾ c₂) x)
            lem rewrite xeq = rs!'
          loop₂ : (rs : ⟨ c₂ ∣ b ∣ c₁ ⨾☐• ☐ ⟩◁ ↦* toState (c₁ ⨾ c₂) x)
                → len↦ rs ≡ n
                → ⟨ ! c₁ ∣ b ∣ (! c₂) ⨾☐• ☐ ⟩▷ ↦* toState! (c₁ ⨾ c₂) x
          loop₂ rs refl with inspect⊎ (run ［ c₁ ∣ b ∣ ☐  ］◁) (λ ())
          loop₂ rs refl | inj₁ ((a  , rsb) , eq) = lem
            where
            rs' : ⟨ c₂ ∣ b ∣ c₁ ⨾☐• ☐ ⟩◁ ↦* ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩◁
            rs' = ↦⃖₇ ∷ appendκ↦* rsb refl (☐⨾ c₂ • ☐) ++↦ ↦⃖₃ ∷ ◾

            rs!' : ⟨ ! c₁ ∣ b ∣ (! c₂) ⨾☐• ☐ ⟩▷ ↦* ［ ! c₂ ⨾ ! c₁ ∣ a ∣ ☐ ］▷
            rs!' = Rev* (appendκ↦* (getₜᵣ⃖ (! c₁) (!rev c₁ (b ⃖) (eval-toState₂ rsb))) refl (! c₂ ⨾☐• ☐)) ++↦ ↦⃗₁₀ ∷ ◾
            
            xeq : x ≡ a ⃖
            xeq = toState≡₂ (deterministic* rs rs' (is-stuck-toState _ _) (λ ()))
            
            lem : ⟨ ! c₁ ∣ b ∣ (! c₂) ⨾☐• ☐ ⟩▷ ↦* (toState! (c₁ ⨾ c₂) x)
            lem rewrite xeq = rs!'
          loop₂ rs refl | inj₂ ((b' , rsb) , eq) = rs!' ++↦ proj₁ (R (len↦ rs'') le b') rs'' refl
            where
            rs' : ⟨ c₂ ∣ b ∣ c₁ ⨾☐• ☐ ⟩◁ ↦* ［ c₁ ∣ b' ∣ ☐⨾ c₂ • ☐ ］▷
            rs' = ↦⃖₇ ∷ appendκ↦* rsb refl (☐⨾ c₂ • ☐)
            
            rs'' : ［ c₁ ∣ b' ∣ ☐⨾ c₂ • ☐ ］▷ ↦* toState (c₁ ⨾ c₂) x
            rs'' = proj₁ (deterministic*' rs' rs (is-stuck-toState _ _))

            req : len↦ rs ≡ len↦ rs' + len↦ rs''
            req = proj₂ (deterministic*' rs' rs (is-stuck-toState _ _))

            le : len↦ rs'' <′ len↦ rs
            le = subst (λ x → len↦ rs'' <′ x) (sym req) (s≤′s (n≤′m+n _ _))

            rs!' : ⟨ ! c₁ ∣ b ∣ (! c₂) ⨾☐• ☐ ⟩▷ ↦* ⟨ ! c₁ ∣ b' ∣ ! c₂ ⨾☐• ☐ ⟩◁
            rs!' = Rev* (appendκ↦* (getₜᵣ⃗ (! c₁) (!rev c₁ (b ⃖) (eval-toState₂ rsb))) refl (! c₂ ⨾☐• ☐))

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
