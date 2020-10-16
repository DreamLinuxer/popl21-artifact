module PiQ.Properties where
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Sum
open import Data.Product
open import Data.Maybe
open import Data.Maybe.Properties
open import Data.Nat hiding (_≟_)
open import Data.Nat.Induction
open import Data.Nat.Properties hiding (_≟_)
open import Function using (_∘_)
open import Relation.Binary.Core
open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import PiQ.Syntax
open import PiQ.Opsem
open import PiQ.AuxLemmas
open import PiQ.NoRepeat
open import PiQ.Invariants
open import PiQ.Eval
open import PiQ.Interp

-- Change the direction of the given state
flip : (st : State) → st ≢ ⊠ → State
flip ⟨ c ∣ v ∣ κ ⟩▷ _ = ⟨ c ∣ v ∣ κ ⟩◁
flip ［ c ∣ v ∣ κ ］▷ _ = ［ c ∣ v ∣ κ ］◁
flip ⟨ c ∣ v ∣ κ ⟩◁ _ = ⟨ c ∣ v ∣ κ ⟩▷
flip ［ c ∣ v ∣ κ ］◁ _ = ［ c ∣ v ∣ κ ］▷
flip ⊠ st≢⊠ = ⊥-elim (st≢⊠ refl)

Rev : ∀ {st st'} → st ↦ st' → (nf : st ≢ ⊠) (nf' : st' ≢ ⊠)
    → flip st' nf' ↦ flip st nf
Rev ↦⃗₁ _ _ = ↦⃖₁
Rev ↦⃗₂ _ _ = ↦⃖₂
Rev ↦⃗₃ _ _ = ↦⃖₃
Rev ↦⃗₄ _ _ = ↦⃖₄
Rev ↦⃗₅ _ _ = ↦⃖₅
Rev ↦⃗₆ _ _ = ↦⃖₆
Rev ↦⃗₇ _ _ = ↦⃖₇
Rev ↦⃗₈ _ _ = ↦⃖₈
Rev ↦⃗₉ _ _ = ↦⃖₉
Rev ↦⃗₁₀ _ _ = ↦⃖₁₀
Rev ↦⃗₁₁ _ _ = ↦⃖₁₁
Rev ↦⃗₁₂ _ _ = ↦⃖₁₂
Rev ↦⃖₁ _ _ = ↦⃗₁
Rev ↦⃖₂ _ _ = ↦⃗₂
Rev ↦⃖₃ _ _ = ↦⃗₃
Rev ↦⃖₄ _ _ = ↦⃗₄
Rev ↦⃖₅ _ _ = ↦⃗₅
Rev ↦⃖₆ _ _ = ↦⃗₆
Rev ↦⃖₇ _ _ = ↦⃗₇
Rev ↦⃖₈ _ _ = ↦⃗₈
Rev ↦⃖₉ _ _ = ↦⃗₉
Rev ↦⃖₁₀ _ _ = ↦⃗₁₀
Rev ↦⃖₁₁ _ _ = ↦⃗₁₁
Rev ↦⃖₁₂ _ _ = ↦⃗₁₂
Rev ↦η₊₁ _ _ = ↦η₊₂
Rev ↦η₊₂ _ _ = ↦η₊₁
Rev ↦ε₊₁ _ _ = ↦ε₊₂
Rev ↦ε₊₂ _ _ = ↦ε₊₁
Rev ↦⃗ηₓ _ _ = ↦⃖ηₓ₁ {eq = refl}
Rev (↦⃖ηₓ₁ {eq = refl}) _ _ = ↦⃗ηₓ
Rev ↦⃖ηₓ₂ _ nf' = ⊥-elim (nf' refl)
Rev (↦⃗εₓ₁ {eq = refl}) _ _ = ↦⃖εₓ
Rev ↦⃗εₓ₂ _ nf' = ⊥-elim (nf' refl)
Rev ↦⃖εₓ _ _ = ↦⃗εₓ₁ {eq = refl}

Rev* : ∀ {st st'} → st ↦* st' → (nf : st ≢ ⊠) → (nf' : st' ≢ ⊠) → flip st' nf' ↦* flip st nf
Rev* {⟨ _ ∣ _ ∣ _ ⟩▷} ◾ _ _ = ◾
Rev* {［ _ ∣ _ ∣ _ ］▷} ◾ _ _ = ◾
Rev* {⟨ _ ∣ _ ∣ _ ⟩◁} ◾ _ _ = ◾
Rev* {［ _ ∣ _ ∣ _ ］◁} ◾ _ _ = ◾
Rev* {⊠} ◾ nf _ = ⊥-elim (nf refl)
Rev* (r ∷ ◾) nf nf' = Rev r nf nf' ∷ ◾
Rev* (r ∷ (r' ∷ rs)) nf nf' = Rev* (r' ∷ rs) nf'' nf' ++↦ (Rev r nf nf'' ∷ ◾)
  where
  nf'' = λ eq → ⊠-is-stuck eq (_ , r')

-- Helper functions
inspect⊎ : ∀ {ℓ ℓ₁ ℓ₂ ℓ₃} {P : Set ℓ} {Q : Set ℓ₁} {R : Set ℓ₂} {S : Set ℓ₃}
         → (f : P → Q ⊎ R ⊎ S) → (p : P) → (∃[ q ] (inj₁ q ≡ f p)) ⊎ (∃[ r ] (inj₂ (inj₁ r) ≡ f p)) ⊎ (∃[ s ] (inj₂ (inj₂ s) ≡ f p))
inspect⊎ f p with f p
... | inj₁ q = inj₁ (q , refl)
... | inj₂ (inj₁ r) = inj₂ (inj₁ (r , refl))
... | inj₂ (inj₂ r) = inj₂ (inj₂ (r , refl))

Val≢ : ∀ {A B v₁ v₂} → _⃗ {A} {B} v₁ ≢ v₂ ⃖
Val≢ ()

Maybe≢ : ∀ {ℓ} {A : Set ℓ} {a : A} → just a ≢ nothing
Maybe≢ ()

toState : ∀ {A B} → (A ↔ B) → Maybe (Val B A) → State
toState c (just (b ⃗)) = ［ c ∣ b ∣ ☐ ］▷
toState c (just (a ⃖)) = ⟨ c ∣ a ∣ ☐ ⟩◁
toState c nothing = ⊠

is-stuck-toState : ∀ {A B} → (c : A ↔ B) → (v : Maybe (Val B A)) → is-stuck (toState c v)
is-stuck-toState c (just (b ⃗)) = λ ()
is-stuck-toState c (just (a ⃖)) = λ ()
is-stuck-toState c nothing = λ ()

toStateEq₁ : ∀ {A B b} → (c : A ↔ B) → (x : Maybe (Val B A)) → ［ c ∣ b ∣ ☐ ］▷ ≡ toState c x → just (b ⃗) ≡ x
toStateEq₁ c (just (x ⃗)) refl = refl

toStateEq₂ : ∀ {A B a} → (c : A ↔ B) → (x : Maybe (Val B A)) → ⟨ c ∣ a ∣ ☐ ⟩◁ ≡ toState c x → just (a ⃖) ≡ x
toStateEq₂ c (just (x ⃖)) refl = refl

toStateEq₃ : ∀ {A B} → (c : A ↔ B) → (x : Maybe (Val B A)) → ⊠ ≡ toState c x → nothing ≡ x
toStateEq₃ c nothing refl = refl
toStateEq₃ c (just (x ⃗)) ()
toStateEq₃ c (just (x ⃖)) ()

toState≡₁ : ∀ {A B b x} {c : A ↔ B} → toState c x ≡ ［ c ∣ b ∣ ☐ ］▷ → x ≡ just (b ⃗)
toState≡₁ {x = just (x ⃗)} refl = refl

toState≡₂ : ∀ {A B a x} {c : A ↔ B} → toState c x ≡ ⟨ c ∣ a ∣ ☐ ⟩◁ → x ≡ just (a ⃖)
toState≡₂ {x = just (x ⃖)} refl = refl

toState≡₃ : ∀ {A B x} {c : A ↔ B} → toState c x ≡ ⊠ → x ≡ nothing
toState≡₃ {x = nothing} refl = refl
toState≡₃ {x = just (x ⃗)} ()
toState≡₃ {x = just (x ⃖)} ()

eval-toState₁ : ∀ {A B a x} {c : A ↔ B} → ⟨ c ∣ a ∣ ☐ ⟩▷ ↦* (toState c x) → eval c (a ⃗) ≡ x
eval-toState₁ {a = a} {just (b ⃗)} {c} rs with inspect⊎ (run ⟨ c ∣ a ∣ ☐ ⟩▷) (λ ())
eval-toState₁ {a = a} {just (b ⃗)} {c} rs | inj₁ ((a' , rs') , eq) with deterministic* rs rs' (λ ()) (λ ())
... | ()
eval-toState₁ {a = a} {just (b ⃗)} {c} rs | inj₂ (inj₁ ((b' , rs') , eq)) with deterministic* rs rs' (λ ()) (λ ())
... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (b ⃗)) eq refl
eval-toState₁ {a = a} {just (b ⃗)} {c} rs | inj₂ (inj₂ (rs' , eq)) with deterministic* rs rs' (λ ()) (λ ())
... | ()
eval-toState₁ {a = a} {just (a' ⃖)} {c} rs with inspect⊎ (run ⟨ c ∣ a ∣ ☐ ⟩▷) (λ ())
eval-toState₁ {a = a} {just (a' ⃖)} {c} rs | inj₁ ((a'' , rs') , eq) with deterministic* rs rs' (λ ()) (λ ())
... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (a' ⃖)) eq refl
eval-toState₁ {a = a} {just (a' ⃖)} {c} rs | inj₂ (inj₁ ((b' , rs') , eq)) with deterministic* rs rs' (λ ()) (λ ())
... | ()
eval-toState₁ {a = a} {just (a' ⃖)} {c} rs | inj₂ (inj₂ (rs' , eq)) with deterministic* rs rs' (λ ()) (λ ())
... | ()
eval-toState₁ {a = a} {nothing} {c} rs with inspect⊎ (run ⟨ c ∣ a ∣ ☐ ⟩▷) (λ ())
eval-toState₁ {a = a} {nothing} {c} rs | inj₁ ((a' , rs') , eq) with deterministic* rs rs' (λ ()) (λ ())
... | ()
eval-toState₁ {a = a} {nothing} {c} rs | inj₂ (inj₁ ((b' , rs') , eq)) with deterministic* rs rs' (λ ()) (λ ())
... | ()
eval-toState₁ {a = a} {nothing} {c} rs | inj₂ (inj₂ (rs' , eq)) with deterministic* rs rs' (λ ()) (λ ())
... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ nothing) eq refl

eval-toState₂ : ∀ {A B b x} {c : A ↔ B} → ［ c ∣ b ∣ ☐ ］◁ ↦* (toState c x) → eval c (b ⃖) ≡ x
eval-toState₂ {b = b} {just (b' ⃗)} {c} rs with inspect⊎ (run ［ c ∣ b ∣ ☐ ］◁) (λ ())
eval-toState₂ {b = b} {just (b' ⃗)} {c} rs | inj₁ ((a' , rs') , eq) with deterministic* rs rs' (λ ()) (λ ())
... | ()
eval-toState₂ {b = b} {just (b' ⃗)} {c} rs | inj₂ (inj₁ ((b'' , rs') , eq)) with deterministic* rs rs' (λ ()) (λ ())
... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (b' ⃗)) eq refl
eval-toState₂ {b = b} {just (b' ⃗)} {c} rs | inj₂ (inj₂ (rs' , eq)) with deterministic* rs rs' (λ ()) (λ ())
... | ()
eval-toState₂ {b = b} {just (a ⃖)} {c} rs with inspect⊎ (run ［ c ∣ b ∣ ☐ ］◁) (λ ())
eval-toState₂ {b = b} {just (a ⃖)} {c} rs | inj₁ ((a'' , rs') , eq) with deterministic* rs rs' (λ ()) (λ ())
... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (a ⃖)) eq refl
eval-toState₂ {b = b} {just (a ⃖)} {c} rs | inj₂ (inj₁ ((b' , rs') , eq)) with deterministic* rs rs' (λ ()) (λ ())
... | ()
eval-toState₂ {b = b} {just (a ⃖)} {c} rs | inj₂ (inj₂ (rs' , eq)) with deterministic* rs rs' (λ ()) (λ ())
... | ()
eval-toState₂ {b = b} {nothing} {c} rs with inspect⊎ (run ［ c ∣ b ∣ ☐ ］◁) (λ ())
eval-toState₂ {b = b} {nothing} {c} rs | inj₁ ((a' , rs') , eq) with deterministic* rs rs' (λ ()) (λ ())
... | ()
eval-toState₂ {b = b} {nothing} {c} rs | inj₂ (inj₁ ((b' , rs') , eq)) with deterministic* rs rs' (λ ()) (λ ())
... | ()
eval-toState₂ {b = b} {nothing} {c} rs | inj₂ (inj₂ (rs' , eq)) with deterministic* rs rs' (λ ()) (λ ())
... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ nothing) eq refl

getₜᵣ⃗ : ∀ {A B} → (c : A ↔ B) → {v : ⟦ A ⟧} {v' : Maybe (Val B A)} → eval c (v ⃗) ≡ v'
       → ⟨ c ∣ v ∣ ☐ ⟩▷ ↦* toState c v'
getₜᵣ⃗ c {v} {v'} eq with inspect⊎ (run ⟨ c ∣ v ∣ ☐ ⟩▷) (λ ())
getₜᵣ⃗ c {v} {nothing} eq | inj₁ ((x₁ , rs₁) , eq₁) with trans (subst (λ x → just (x₁ ⃖) ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq₁ refl) eq
... | ()
getₜᵣ⃗ c {v} {just (x ⃗)} eq | inj₁ ((x₁ , rs₁) , eq₁) with trans (subst (λ x → just (x₁ ⃖) ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq₁ refl) eq
... | ()
getₜᵣ⃗ c {v} {just (x ⃖)} eq | inj₁ ((x₁ , rs₁) , eq₁) with trans (subst (λ x → just (x₁ ⃖) ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq₁ refl) eq
... | refl = rs₁
getₜᵣ⃗ c {v} {nothing} eq | inj₂ (inj₁ ((x₁ , rs₁) , eq₁)) with trans (subst (λ x → just (x₁ ⃗) ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq₁ refl) eq
... | ()
getₜᵣ⃗ c {v} {just (x ⃗)} eq | inj₂ (inj₁ ((x₁ , rs₁) , eq₁)) with trans (subst (λ x → just (x₁ ⃗) ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq₁ refl) eq
... | refl = rs₁
getₜᵣ⃗ c {v} {just (x ⃖)} eq | inj₂ (inj₁ ((x₁ , rs₁) , eq₁)) with trans (subst (λ x → just (x₁ ⃗) ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq₁ refl) eq
... | ()
getₜᵣ⃗ c {v} {nothing} eq | inj₂ (inj₂ (rs₁ , eq₁)) with trans (subst (λ x → nothing ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq₁ refl) eq
... | refl = rs₁
getₜᵣ⃗ c {v} {just (x ⃗)} eq | inj₂ (inj₂ (rs₁ , eq₁)) with trans (subst (λ x → nothing ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq₁ refl) eq
... | ()
getₜᵣ⃗ c {v} {just (x ⃖)} eq | inj₂ (inj₂ (rs₁ , eq₁)) with trans (subst (λ x → nothing ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq₁ refl) eq
... | ()

getₜᵣ⃖ : ∀ {A B} → (c : A ↔ B) → {v : ⟦ B ⟧} {v' : Maybe (Val B A)} → eval c (v ⃖) ≡ v'
       → ［ c ∣ v ∣ ☐ ］◁ ↦* toState c v'
getₜᵣ⃖ c {v} {v'} eq with inspect⊎ (run ［ c ∣ v ∣ ☐ ］◁) (λ ())
getₜᵣ⃖ c {v} {nothing} eq | inj₁ ((x₁ , rs₁) , eq₁) with trans (subst (λ x → just (x₁ ⃖) ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq₁ refl) eq
... | ()
getₜᵣ⃖ c {v} {just (x ⃗)} eq | inj₁ ((x₁ , rs₁) , eq₁) with trans (subst (λ x → just (x₁ ⃖) ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq₁ refl) eq
... | ()
getₜᵣ⃖ c {v} {just (x ⃖)} eq | inj₁ ((x₁ , rs₁) , eq₁) with trans (subst (λ x → just (x₁ ⃖) ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq₁ refl) eq
... | refl = rs₁
getₜᵣ⃖ c {v} {nothing} eq | inj₂ (inj₁ ((x₁ , rs₁) , eq₁)) with trans (subst (λ x → just (x₁ ⃗) ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq₁ refl) eq
... | ()
getₜᵣ⃖ c {v} {just (x ⃗)} eq | inj₂ (inj₁ ((x₁ , rs₁) , eq₁)) with trans (subst (λ x → just (x₁ ⃗) ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq₁ refl) eq
... | refl = rs₁
getₜᵣ⃖ c {v} {just (x ⃖)} eq | inj₂ (inj₁ ((x₁ , rs₁) , eq₁)) with trans (subst (λ x → just (x₁ ⃗) ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq₁ refl) eq
... | ()
getₜᵣ⃖ c {v} {nothing} eq | inj₂ (inj₂ (rs₁ , eq₁)) with trans (subst (λ x → nothing ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq₁ refl) eq
... | refl = rs₁
getₜᵣ⃖ c {v} {just (x ⃗)} eq | inj₂ (inj₂ (rs₁ , eq₁)) with trans (subst (λ x → nothing ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq₁ refl) eq
... | ()
getₜᵣ⃖ c {v} {just (x ⃖)} eq | inj₂ (inj₂ (rs₁ , eq₁)) with trans (subst (λ x → nothing ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq₁ refl) eq
... | ()

-- Forward evaluator is reversible
evalIsRev : ∀ {A B} → (c : A ↔ B) (v₁ : Val A B) (v₂ : Val B A)
          → eval c v₁ ≡ (just v₂) → evalᵣₑᵥ c v₂ ≡ (just v₁)
evalIsRev c (v₁ ⃗) (v₂ ⃗) eq with inspect⊎ (run ⟨ c ∣ v₁ ∣ ☐ ⟩▷) (λ ())
evalIsRev c (v₁ ⃗) (v₂ ⃗) eq | inj₁ ((u , rs) , eq') = ⊥-elim (Val≢ (sym (just-injective contr)))
  where
  contr : just (u ⃖) ≡ just (v₂ ⃗)
  contr = trans (subst (λ x → just (u ⃖) ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq
evalIsRev c (v₁ ⃗) (v₂ ⃗) eq | inj₂ (inj₁ ((u , rs) , eq')) = subst (λ x → evalᵣₑᵥ c x ≡ just (v₁ ⃗)) u≡v₂ rsinv
  where
  u≡v₂ : (u ⃗) ≡ (v₂ ⃗)
  u≡v₂ = just-injective (trans (subst (λ x → just (u ⃗) ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq)

  rsinv : evalᵣₑᵥ c (u ⃗) ≡ just (v₁ ⃗)
  rsinv with u≡v₂ | inspect⊎ (run ［ c ∣ v₂ ∣ ☐ ］◁) (λ ())
  rsinv | refl | inj₁ ((w , rs') , eq'') with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | refl = subst (λ x → [ just ∘ _⃗ ∘ proj₁ , [ just ∘ _⃖ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (v₁ ⃗)) eq'' refl
  rsinv | refl | inj₂ (inj₁ ((w , rs') , eq'')) with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | ()
  rsinv | refl | inj₂ (inj₂ (rs' , eq'')) with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | ()
evalIsRev c (v₁ ⃗) (v₂ ⃗) eq | inj₂ (inj₂ (rs , eq')) = ⊥-elim (Maybe≢ (sym contr))
  where
  contr : nothing ≡ just (v₂ ⃗)
  contr = trans (subst (λ x → nothing ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq
evalIsRev c (v₁ ⃗) (v₂ ⃖) eq with inspect⊎ (run ⟨ c ∣ v₁ ∣ ☐ ⟩▷) (λ ())
evalIsRev c (v₁ ⃗) (v₂ ⃖) eq | inj₁ ((u , rs) , eq') = subst (λ x → evalᵣₑᵥ c x ≡ just (v₁ ⃗)) u≡v₂ rsinv
  where
  u≡v₂ : (u ⃖) ≡ (v₂ ⃖)
  u≡v₂ = just-injective (trans (subst (λ x → just (u ⃖) ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq)

  rsinv : evalᵣₑᵥ c (u ⃖) ≡ just (v₁ ⃗)
  rsinv with u≡v₂ | inspect⊎ (run ⟨ c ∣ u ∣ ☐ ⟩▷) (λ ())
  rsinv | refl | inj₁ ((w , rs') , eq'') with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | refl = subst (λ x → [ just ∘ _⃗ ∘ proj₁ , [ just ∘ _⃖ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (v₁ ⃗)) eq'' refl
  rsinv | refl | inj₂ (inj₁ ((w , rs') , eq'')) with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | ()
  rsinv | refl | inj₂ (inj₂ (rs' , eq'')) with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | ()
evalIsRev c (v₁ ⃗) (v₂ ⃖) eq | inj₂ (inj₁ ((u , rs) , eq')) = ⊥-elim (Val≢ (just-injective contr))
  where
  contr : just (u ⃗) ≡ just (v₂ ⃖)
  contr = trans (subst (λ x → just (u ⃗) ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq
evalIsRev c (v₁ ⃗) (v₂ ⃖) eq | inj₂ (inj₂ (rs , eq')) = ⊥-elim (Maybe≢ (sym contr))
  where
  contr : nothing ≡ just (v₂ ⃖)
  contr = trans (subst (λ x → nothing ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq
evalIsRev c (v₁ ⃖) (v₂ ⃗) eq with inspect⊎ (run ［ c ∣ v₁ ∣ ☐ ］◁) (λ ())
evalIsRev c (v₁ ⃖) (v₂ ⃗) eq | inj₁ ((u , rs) , eq') = ⊥-elim (Val≢ (just-injective (sym contr)))
  where
  contr : just (u ⃖) ≡ just (v₂ ⃗)
  contr = trans (subst (λ x → just (u ⃖) ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq
evalIsRev c (v₁ ⃖) (v₂ ⃗) eq | inj₂ (inj₁ ((u , rs) , eq')) = subst (λ x → evalᵣₑᵥ c x ≡ just (v₁ ⃖)) u≡v₂ rsinv
  where
  u≡v₂ : (u ⃗) ≡ (v₂ ⃗)
  u≡v₂ = just-injective (trans (subst (λ x → just (u ⃗) ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq)

  rsinv : evalᵣₑᵥ c (u ⃗) ≡ just (v₁ ⃖)
  rsinv with u≡v₂ | inspect⊎ (run ［ c ∣ u ∣ ☐ ］◁) (λ ())
  rsinv | refl | inj₁ ((w , rs') , eq'') with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | ()
  rsinv | refl | inj₂ (inj₁ ((w , rs') , eq'')) with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | refl = subst (λ x → [ just ∘ _⃗ ∘ proj₁ , [ just ∘ _⃖ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (v₁ ⃖)) eq'' refl
  rsinv | refl | inj₂ (inj₂ (rs' , eq'')) with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | ()
evalIsRev c (v₁ ⃖) (v₂ ⃗) eq | inj₂ (inj₂ (rs , eq')) = ⊥-elim (Maybe≢ (sym contr))
  where
  contr : nothing ≡ just (v₂ ⃗)
  contr = trans (subst (λ x → nothing ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq
evalIsRev c (v₁ ⃖) (v₂ ⃖) eq with inspect⊎ (run ［ c ∣ v₁ ∣ ☐ ］◁) (λ ())
evalIsRev c (v₁ ⃖) (v₂ ⃖) eq | inj₁ ((u , rs) , eq') = subst (λ x → evalᵣₑᵥ c x ≡ just (v₁ ⃖)) u≡v₂ rsinv
  where
  u≡v₂ : (u ⃖) ≡ (v₂ ⃖)
  u≡v₂ = just-injective (trans (subst (λ x → just (u ⃖) ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq)

  rsinv : evalᵣₑᵥ c (u ⃖) ≡ just (v₁ ⃖)
  rsinv with u≡v₂ | inspect⊎ (run ⟨ c ∣ u ∣ ☐ ⟩▷) (λ ())
  rsinv | refl | inj₁ ((w , rs') , eq'') with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | ()
  rsinv | refl | inj₂ (inj₁ ((w , rs') , eq'')) with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | refl = subst (λ x → [ just ∘ _⃗ ∘ proj₁ , [ just ∘ _⃖ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (v₁ ⃖)) eq'' refl
  rsinv | refl | inj₂ (inj₂ (rs' , eq'')) with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | ()
evalIsRev c (v₁ ⃖) (v₂ ⃖) eq | inj₂ (inj₁ ((u , rs) , eq')) = ⊥-elim (Val≢ (just-injective contr))
  where
  contr : just (u ⃗) ≡ just (v₂ ⃖)
  contr = trans (subst (λ x → just (u ⃗) ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq
evalIsRev c (v₁ ⃖) (v₂ ⃖) eq | inj₂ (inj₂ (rs , eq')) = ⊥-elim (Maybe≢ (sym contr))
  where
  contr : nothing ≡ just (v₂ ⃖)
  contr = trans (subst (λ x → nothing ≡ [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq

-- Backward evaluator is reversible
evalᵣₑᵥIsRev : ∀ {A B} → (c : A ↔ B) (v₁ : Val B A) (v₂ : Val A B)
             → evalᵣₑᵥ c v₁ ≡ (just v₂) → eval c v₂ ≡ (just v₁)
evalᵣₑᵥIsRev c (v₁ ⃗) (v₂ ⃗) eq with inspect⊎ (run ［ c ∣ v₁ ∣ ☐ ］◁) (λ ())
evalᵣₑᵥIsRev c (v₁ ⃗) (v₂ ⃗) eq | inj₁ ((u , rs) , eq') = subst (λ x → eval c x ≡ just (v₁ ⃗)) u≡v₂ rsinv
  where
  u≡v₂ : (u ⃗) ≡ (v₂ ⃗)
  u≡v₂ = just-injective (trans (subst (λ x → just (u ⃗) ≡ [ just ∘ _⃗ ∘ proj₁ , [ just ∘ _⃖ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq)

  rsinv : eval c (u ⃗) ≡ just (v₁ ⃗)
  rsinv with inspect⊎ (run ⟨ c ∣ u ∣ ☐ ⟩▷) (λ ())
  rsinv | inj₁ ((w , rs') , eq'') with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | ()
  rsinv | inj₂ (inj₁ ((w , rs') , eq'')) with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (v₁ ⃗)) eq'' refl
  rsinv | inj₂ (inj₂ (rs' , eq'')) with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | ()
evalᵣₑᵥIsRev c (v₁ ⃗) (v₂ ⃗) eq | inj₂ (inj₁ ((u , rs) , eq')) = ⊥-elim (Val≢ (sym (just-injective contr)))
  where
  contr : just (u ⃖) ≡ just (v₂ ⃗)
  contr = trans (subst (λ x → just (u ⃖) ≡ [ just ∘ _⃗ ∘ proj₁ , [ just ∘ _⃖ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq
evalᵣₑᵥIsRev c (v₁ ⃗) (v₂ ⃗) eq | inj₂ (inj₂ (rs' , eq')) = ⊥-elim (Maybe≢ (sym contr))
  where
  contr : nothing ≡ just (v₂ ⃗)
  contr = trans (subst (λ x → nothing ≡ [ just ∘ _⃗ ∘ proj₁ , [ just ∘ _⃖ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq
evalᵣₑᵥIsRev c (v₁ ⃗) (v₂ ⃖) eq with inspect⊎ (run ［ c ∣ v₁ ∣ ☐ ］◁) (λ ())
evalᵣₑᵥIsRev c (v₁ ⃗) (v₂ ⃖) eq | inj₁ ((u , rs) , eq') = ⊥-elim (Val≢ (just-injective contr))
  where
  contr : just (u ⃗) ≡ just (v₂ ⃖)
  contr = trans (subst (λ x → just (u ⃗) ≡ [ just ∘ _⃗ ∘ proj₁ , [ just ∘ _⃖ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq
evalᵣₑᵥIsRev c (v₁ ⃗) (v₂ ⃖) eq | inj₂ (inj₁ ((u , rs) , eq')) = subst (λ x → eval c x ≡ just (v₁ ⃗)) u≡v₂ rsinv
  where
  u≡v₂ : (u ⃖) ≡ (v₂ ⃖)
  u≡v₂ = just-injective (trans (subst (λ x → just (u ⃖) ≡ [ just ∘ _⃗ ∘ proj₁ , [ just ∘ _⃖ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq)

  rsinv : eval c (u ⃖) ≡ just (v₁ ⃗)
  rsinv with inspect⊎ (run ［ c ∣ u ∣ ☐ ］◁) (λ ())
  rsinv | inj₁ ((w , rs') , eq'') with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | ()
  rsinv | inj₂ (inj₁ ((w , rs') , eq'')) with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (v₁ ⃗)) eq'' refl
  rsinv | inj₂ (inj₂ (rs' , eq'')) with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | ()
evalᵣₑᵥIsRev c (v₁ ⃗) (v₂ ⃖) eq | inj₂ (inj₂ (rs' , eq')) = ⊥-elim (Maybe≢ (sym contr))
  where
  contr : nothing ≡ just (v₂ ⃖)
  contr = trans (subst (λ x → nothing ≡ [ just ∘ _⃗ ∘ proj₁ , [ just ∘ _⃖ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq
evalᵣₑᵥIsRev c (v₁ ⃖) (v₂ ⃗) eq with inspect⊎ (run ⟨ c ∣ v₁ ∣ ☐ ⟩▷) (λ ())
evalᵣₑᵥIsRev c (v₁ ⃖) (v₂ ⃗) eq | inj₁ ((u , rs) , eq') = subst (λ x → eval c x ≡ just (v₁ ⃖)) u≡v₂ rsinv
  where
  u≡v₂ : (u ⃗) ≡ (v₂ ⃗)
  u≡v₂ = just-injective (trans (subst (λ x → just (u ⃗) ≡ [ just ∘ _⃗ ∘ proj₁ , [ just ∘ _⃖ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq)

  rsinv : eval c (u ⃗) ≡ just (v₁ ⃖)
  rsinv with inspect⊎ (run ⟨ c ∣ u ∣ ☐ ⟩▷) (λ ())
  rsinv | inj₁ ((w , rs') , eq'') with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (v₁ ⃖)) eq'' refl
  rsinv | inj₂ (inj₁ ((w , rs') , eq'')) with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | ()
  rsinv | inj₂ (inj₂ (rs' , eq'')) with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | ()
evalᵣₑᵥIsRev c (v₁ ⃖) (v₂ ⃗) eq | inj₂ (inj₁ ((u , rs) , eq')) = ⊥-elim (Val≢ (sym (just-injective contr)))
  where
  contr : just (u ⃖) ≡ just (v₂ ⃗)
  contr = trans (subst (λ x → just (u ⃖) ≡ [ just ∘ _⃗ ∘ proj₁ , [ just ∘ _⃖ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq
evalᵣₑᵥIsRev c (v₁ ⃖) (v₂ ⃗) eq | inj₂ (inj₂ (rs' , eq')) = ⊥-elim (Maybe≢ (sym contr))
  where
  contr : nothing ≡ just (v₂ ⃗)
  contr = trans (subst (λ x → nothing ≡ [ just ∘ _⃗ ∘ proj₁ , [ just ∘ _⃖ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq
evalᵣₑᵥIsRev c (v₁ ⃖) (v₂ ⃖) eq with inspect⊎ (run ⟨ c ∣ v₁ ∣ ☐ ⟩▷) (λ ())
evalᵣₑᵥIsRev c (v₁ ⃖) (v₂ ⃖) eq | inj₁ ((u , rs) , eq') = ⊥-elim (Val≢ (just-injective contr))
  where
  contr : just (u ⃗) ≡ just (v₂ ⃖)
  contr = trans (subst (λ x → just (u ⃗) ≡ [ just ∘ _⃗ ∘ proj₁ , [ just ∘ _⃖ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq
evalᵣₑᵥIsRev c (v₁ ⃖) (v₂ ⃖) eq | inj₂ (inj₁ ((u , rs) , eq')) = subst (λ x → eval c x ≡ just (v₁ ⃖)) u≡v₂ rsinv
  where
  u≡v₂ : (u ⃖) ≡ (v₂ ⃖)
  u≡v₂ = just-injective (trans (subst (λ x → just (u ⃖) ≡ [ just ∘ _⃗ ∘ proj₁ , [ just ∘ _⃖ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq)

  rsinv : eval c (u ⃖) ≡ just (v₁ ⃖)
  rsinv with inspect⊎ (run ［ c ∣ u ∣ ☐ ］◁) (λ ())
  rsinv | inj₁ ((w , rs') , eq'') with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (v₁ ⃖)) eq'' refl
  rsinv | inj₂ (inj₁ ((w , rs') , eq'')) with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | ()
  rsinv | inj₂ (inj₂ (rs' , eq'')) with deterministic* rs' (Rev* rs (λ ()) (λ ())) (λ ()) (λ ())
  ... | ()
evalᵣₑᵥIsRev c (v₁ ⃖) (v₂ ⃖) eq | inj₂ (inj₂ (rs' , eq')) = ⊥-elim (Maybe≢ (sym contr))
  where
  contr : nothing ≡ just (v₂ ⃖)
  contr = trans (subst (λ x → nothing ≡ [ just ∘ _⃗ ∘ proj₁ , [ just ∘ _⃖ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x) eq' refl) eq

-- The abstract machine semantics is equivalent to the big-step semantics
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
  eval≡interp η₊ (inj₁ x ⃖) = refl
  eval≡interp η₊ (inj₂ (- x) ⃖) = refl
  eval≡interp ε₊ (inj₁ x ⃗) = refl
  eval≡interp ε₊ (inj₂ (- x) ⃗) = refl
  eval≡interp (ηₓ v) (tt ⃗) = refl
  eval≡interp (ηₓ v) ((v' , ↻) ⃖) with v ≟ v'
  ... | yes refl = refl
  ... | no  neq  = refl
  eval≡interp (εₓ v) ((v' , ↻) ⃗) with v ≟ v'
  ... | yes refl = refl
  ... | no  neq  = refl
  eval≡interp (εₓ v) (tt ⃖) = refl
  eval≡interp (c₁ ⨾ c₂) (a ⃗) with interp c₁ (a ⃗) | inspect (interp c₁) (a ⃗)
  eval≡interp (c₁ ⨾ c₂) (a ⃗) | just (b ⃗)  | [ eq₁ ] = lem
    where
    rs : ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩▷ ↦* ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷
    rs = ↦⃗₃ ∷ appendκ↦* ((getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (a ⃗)) eq₁))) (λ ()) (λ ()) refl (☐⨾ c₂ • ☐)
    
    rs' : ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷ ↦* (toState (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (a ⃗)))
    rs' = proj₁ (deterministic*' rs (getₜᵣ⃗ (c₁ ⨾ c₂) refl) (is-stuck-toState _ _))

    lem : eval (c₁ ⨾ c₂) (a ⃗) ≡ (c₁ ⨾[ b ⃗]⨾ c₂)
    lem = proj₁ (loop (len↦ rs') b) rs' refl
  eval≡interp (c₁ ⨾ c₂) (a ⃗) | just (a₁ ⃖) | [ eq₁ ] = lem
    where
    rs : ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⨾ c₂ ∣ a₁ ∣ ☐ ⟩◁
    rs = ↦⃗₃ ∷ appendκ↦* ((getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (a ⃗)) eq₁))) (λ ()) (λ ()) refl (☐⨾ c₂ • ☐) ++↦ ↦⃖₃ ∷ ◾

    lem : eval (c₁ ⨾ c₂) (a ⃗) ≡ just (a₁ ⃖)
    lem = eval-toState₁ rs
  eval≡interp (c₁ ⨾ c₂) (a ⃗) | nothing     | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩▷ ↦* ⊠
    rs' = ↦⃗₃ ∷ appendκ↦*⊠ ((getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (a ⃗)) eq₁))) (λ ()) (☐⨾ c₂ • ☐)

    lem : eval (c₁ ⨾ c₂) (a ⃗) ≡ nothing
    lem = eval-toState₁ rs'
  eval≡interp (c₁ ⨾ c₂) (c ⃖) with interp c₂ (c ⃖) | inspect (interp c₂) (c ⃖)
  eval≡interp (c₁ ⨾ c₂) (c ⃖) | just (c' ⃗) | [ eq' ] = lem
    where
    rs' : ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］◁ ↦* ［ c₁ ⨾ c₂ ∣ c' ∣ ☐ ］▷
    rs' = ↦⃖₁₀ ∷ appendκ↦* ((getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (c ⃖)) eq'))) (λ ()) (λ ()) refl (c₁ ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾

    lem : eval (c₁ ⨾ c₂) (c ⃖) ≡ just (c' ⃗)
    lem = eval-toState₂ rs'
  eval≡interp (c₁ ⨾ c₂) (c ⃖) | just (b ⃖)  | [ eq' ] = lem
    where
    rs : ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］◁ ↦* ⟨ c₂ ∣ b ∣ c₁ ⨾☐• ☐ ⟩◁
    rs = ↦⃖₁₀ ∷ appendκ↦* ((getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (c ⃖)) eq'))) (λ ()) (λ ()) refl (c₁ ⨾☐• ☐)
    
    rs' : ⟨ c₂ ∣ b ∣ c₁ ⨾☐• ☐ ⟩◁ ↦* (toState (c₁ ⨾ c₂) (eval (c₁ ⨾ c₂) (c ⃖)))
    rs' = proj₁ (deterministic*' rs (getₜᵣ⃖ (c₁ ⨾ c₂) refl) (is-stuck-toState _ _))

    lem : eval (c₁ ⨾ c₂) (c ⃖) ≡ (c₁ ⨾[ b ⃖]⨾ c₂)
    lem = proj₂ (loop (len↦ rs') b) rs' refl
  eval≡interp (c₁ ⨾ c₂) (c ⃖) | nothing     | [ eq' ] = lem
    where
    rs' : ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］◁ ↦* ⊠
    rs' = ↦⃖₁₀ ∷ appendκ↦*⊠ ((getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (c ⃖)) eq'))) (λ ()) (c₁ ⨾☐• ☐)

    lem : eval (c₁ ⨾ c₂) (c ⃖) ≡ nothing
    lem = eval-toState₂ rs'
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) with interp c₁ (x ⃗) | inspect (interp c₁) (x ⃗)
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) | just (x₁ ⃗) | [ eq₁ ] = eval-toState₁ rs'
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷ ↦* ［ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ］▷
    rs' = ↦⃗₄ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊕ c₂ • ☐) ++↦ ↦⃗₁₁ ∷ ◾
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) | just (x₁ ⃖) | [ eq₁ ] = eval-toState₁ rs'
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ⟩◁
    rs' = ↦⃗₄ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊕ c₂ • ☐) ++↦ ↦⃖₄ ∷ ◾
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) | nothing      | [ eq₁ ] = eval-toState₁ rs'
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷ ↦* ⊠
    rs' = ↦⃗₄ ∷ appendκ↦*⊠ (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (☐⊕ c₂ • ☐)
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) with interp c₂ (y ⃗) | inspect (interp c₂) (y ⃗)
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) | just (y₁ ⃗) | [ eq₁ ] = eval-toState₁ rs'
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷ ↦* ［ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ］▷
    rs' = ↦⃗₅ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₁)) (λ ()) (λ ()) refl (c₁ ⊕☐• ☐) ++↦ ↦⃗₁₂ ∷ ◾
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) | just (y₁ ⃖) | [ eq₁ ] = eval-toState₁ rs'
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ⟩◁
    rs' = ↦⃗₅ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₁)) (λ ()) (λ ()) refl (c₁ ⊕☐• ☐) ++↦ ↦⃖₅ ∷ ◾
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) | nothing      | [ eq₁ ] = eval-toState₁ rs'
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷ ↦* ⊠
    rs' = ↦⃗₅ ∷ appendκ↦*⊠ (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₁)) (λ ()) (c₁ ⊕☐• ☐)
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) with interp c₁ (x ⃖) | inspect (interp c₁) (x ⃖)
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) | just (x₁ ⃗) | [ eq₁ ] = eval-toState₂ rs'
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁ ↦* ［ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ］▷
    rs' = ↦⃖₁₁ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (λ ()) refl (☐⊕ c₂ • ☐) ++↦ ↦⃗₁₁ ∷ ◾
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) | just (x₁ ⃖) | [ eq₁ ] = eval-toState₂ rs'
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ⟩◁
    rs' = ↦⃖₁₁ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (λ ()) refl (☐⊕ c₂ • ☐) ++↦ ↦⃖₄ ∷ ◾
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) | nothing     | [ eq₁ ] = eval-toState₂ rs'
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁ ↦* ⊠
    rs' = ↦⃖₁₁ ∷ appendκ↦*⊠ (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (☐⊕ c₂ • ☐)
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) with interp c₂ (y ⃖) | inspect (interp c₂) (y ⃖)
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) | just (y₁ ⃗) | [ eq₁ ] = eval-toState₂ rs'
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁ ↦* ［ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ］▷
    rs' = ↦⃖₁₂ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₁)) (λ ()) (λ ()) refl (c₁ ⊕☐• ☐) ++↦ ↦⃗₁₂ ∷ ◾
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) | just (y₁ ⃖) | [ eq₁ ] = eval-toState₂ rs'
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ⟩◁
    rs' = ↦⃖₁₂ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₁)) (λ ()) (λ ()) refl (c₁ ⊕☐• ☐) ++↦ ↦⃖₅ ∷ ◾
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) | nothing     | [ eq₁ ] = eval-toState₂ rs'
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁ ↦* ⊠
    rs' = ↦⃖₁₂ ∷ appendκ↦*⊠ (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₁)) (λ ()) (c₁ ⊕☐• ☐)
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) with interp c₁ (x ⃗) | inspect (interp c₁) (x ⃗)
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | just (x₁ ⃗) | [ eq₁ ] with interp c₂ (y ⃗) | inspect (interp c₂) (y ⃗)
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | just (x₁ ⃗) | [ eq₁ ] | just (y₁ ⃗) | [ eq₂ ] = eval-toState₁ rs'
    where
    rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ［ c₁ ⊗ c₂ ∣ (x₁ , y₁) ∣ ☐ ］▷
    rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y ]• ☐) ++↦
          ↦⃗₈ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x₁ ]⊗☐• ☐) ++↦ ↦⃗₉ ∷ ◾
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | just (x₁ ⃗) | [ eq₁ ] | just (y₁ ⃖) | [ eq₂ ] = eval-toState₁ rs'
    where
    rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊗ c₂ ∣ (x , y₁) ∣ ☐ ⟩◁
    rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y ]• ☐) ++↦
          ↦⃗₈ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x₁ ]⊗☐• ☐) ++↦
          ↦⃖₈ ∷ Rev* (appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y₁ ]• ☐)) (λ ()) (λ ()) ++↦ ↦⃖₆ ∷ ◾
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | just (x₁ ⃗) | [ eq₁ ] | nothing     | [ eq₂ ] = eval-toState₁ rs'
    where
    rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⊠
    rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y ]• ☐) ++↦
          ↦⃗₈ ∷ appendκ↦*⊠ (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₂)) (λ ()) ([ c₁ , x₁ ]⊗☐• ☐)
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | just (x₁ ⃖) | [ eq₁ ] = eval-toState₁ rs'
    where
    rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊗ c₂ ∣ (x₁ , y) ∣ ☐ ⟩◁
    rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y ]• ☐) ++↦ ↦⃖₆ ∷ ◾
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | nothing     | [ eq₁ ] = eval-toState₁ rs'
    where
    rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⊠
    rs' = ↦⃗₆ ∷ appendκ↦*⊠ (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (☐⊗[ c₂ , y ]• ☐)
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) with interp c₂ (y ⃖) | inspect (interp c₂) (y ⃖)
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | just (y₁ ⃗) | [ eq₂ ] = eval-toState₂ rs'
    where
    rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ［ c₁ ⊗ c₂ ∣ (x , y₁) ∣ ☐ ］▷
    rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x ]⊗☐• ☐) ++↦ ↦⃗₉ ∷ ◾
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | just (y₁ ⃖) | [ eq₂ ] with interp c₁ (x ⃖) | inspect (interp c₁) (x ⃖)
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | just (y₁ ⃖) | [ eq₂ ] | just (x₁ ⃗) | [ eq₁ ] = eval-toState₂ rs'
    where
    rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ［ c₁ ⊗ c₂ ∣ (x₁ , y) ∣ ☐ ］▷
    rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x ]⊗☐• ☐) ++↦
          ↦⃖₈ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y₁ ]• ☐) ++↦
          ↦⃗₈ ∷ Rev* (appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x₁ ]⊗☐• ☐)) (λ ()) (λ ()) ++↦ ↦⃗₉ ∷ ◾
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | just (y₁ ⃖) | [ eq₂ ] | just (x₁ ⃖) | [ eq₁ ] = eval-toState₂ rs'
    where
    rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ⟨ c₁ ⊗ c₂ ∣ (x₁ , y₁) ∣ ☐ ⟩◁
    rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x ]⊗☐• ☐) ++↦
          ↦⃖₈ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y₁ ]• ☐) ++↦ ↦⃖₆ ∷ ◾
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | just (y₁ ⃖) | [ eq₂ ] | nothing     | [ eq₁ ] = eval-toState₂ rs'
    where
    rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ⊠
    rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x ]⊗☐• ☐) ++↦
          ↦⃖₈ ∷ appendκ↦*⊠ (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (☐⊗[ c₂ , y₁ ]• ☐)
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | nothing     | [ eq₂ ] = eval-toState₂ rs'
    where
    rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ⊠
    rs' = ↦⃖₉ ∷ appendκ↦*⊠ (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) ([ c₁ , x ]⊗☐• ☐)

  private
    loop : ∀ {A B C x} {c₁ : A ↔ B} {c₂ : B ↔ C} (n : ℕ)
         → ∀ b → ((rs : ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷ ↦* toState (c₁ ⨾ c₂) x) → len↦ rs ≡ n → x ≡ c₁ ⨾[ b ⃗]⨾ c₂)
               × ((rs : ⟨ c₂ ∣ b ∣ c₁ ⨾☐• ☐ ⟩◁ ↦* toState (c₁ ⨾ c₂) x) → len↦ rs ≡ n → x ≡ c₁ ⨾[ b ⃖]⨾ c₂)
    loop {A} {B} {C} {x} {c₁} {c₂} = <′-rec (λ n → _) loop-rec
      where
      loop-rec : (n : ℕ) → (∀ m → m <′ n → _) → _
      loop-rec n R b = loop₁ , loop₂
        where
        loop₁ : (rs : ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷ ↦* toState (c₁ ⨾ c₂) x) → len↦ rs ≡ n → x ≡ c₁ ⨾[ b ⃗]⨾ c₂
        loop₁ rs refl with interp c₂ (b ⃗) | inspect (interp c₂) (b ⃗)
        loop₁ rs refl | just (c ⃗)  | [ eq ] = toState≡₁ (deterministic* rs rs' (is-stuck-toState _ _) (λ ()))
          where
          rs' : ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷ ↦* ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］▷
          rs' = ↦⃗₇ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (b ⃗)) eq)) (λ ()) (λ ()) refl (c₁ ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾
        loop₁ rs refl | just (b' ⃖) | [ eq ] = proj₂ (R (len↦ rs'') le b') rs'' refl
          where
          rs' : ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷ ↦* ⟨ c₂ ∣ b' ∣ c₁ ⨾☐• ☐ ⟩◁
          rs' = ↦⃗₇ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (b ⃗)) eq)) (λ ()) (λ ()) refl (c₁ ⨾☐• ☐)

          rs'' : ⟨ c₂ ∣ b' ∣ c₁ ⨾☐• ☐ ⟩◁ ↦* toState (c₁ ⨾ c₂) x
          rs'' = proj₁ (deterministic*' rs' rs (is-stuck-toState _ _))

          req : len↦ rs ≡ len↦ rs' + len↦ rs''
          req = proj₂ (deterministic*' rs' rs (is-stuck-toState _ _))

          le : len↦ rs'' <′ len↦ rs
          le rewrite req = s≤′s (n≤′m+n _ _)
        loop₁ rs refl | nothing     | [ eq ] = toState≡₃ (deterministic* rs rs' (is-stuck-toState _ _) (λ ()))
          where
          rs' : ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷ ↦* ⊠
          rs' = ↦⃗₇ ∷ appendκ↦*⊠ (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (b ⃗)) eq)) (λ ()) (c₁ ⨾☐• ☐)
        loop₂ : (rs : ⟨ c₂ ∣ b ∣ c₁ ⨾☐• ☐ ⟩◁ ↦* toState (c₁ ⨾ c₂) x) → len↦ rs ≡ n → x ≡ c₁ ⨾[ b ⃖]⨾ c₂
        loop₂ rs refl with interp c₁ (b ⃖) | inspect (interp c₁) (b ⃖)
        loop₂ rs refl | just (b' ⃗) | [ eq ] = proj₁ (R (len↦ rs'') le b') rs'' refl
          where
          rs' : ⟨ c₂ ∣ b ∣ c₁ ⨾☐• ☐ ⟩◁ ↦* ［ c₁ ∣ b' ∣ ☐⨾ c₂ • ☐ ］▷
          rs' = ↦⃖₇ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (b ⃖)) eq)) (λ ()) (λ ()) refl (☐⨾ c₂ • ☐)

          rs'' : ［ c₁ ∣ b' ∣ ☐⨾ c₂ • ☐ ］▷ ↦* toState (c₁ ⨾ c₂) x
          rs'' = proj₁ (deterministic*' rs' rs (is-stuck-toState _ _))

          req : len↦ rs ≡ len↦ rs' + len↦ rs''
          req = proj₂ (deterministic*' rs' rs (is-stuck-toState _ _))

          le : len↦ rs'' <′ len↦ rs
          le rewrite req = s≤′s (n≤′m+n _ _)
        loop₂ rs refl | just (a ⃖)  | [ eq ] = toState≡₂ (deterministic* rs rs' (is-stuck-toState _ _) (λ ()))
          where
          rs' : ⟨ c₂ ∣ b ∣ c₁ ⨾☐• ☐ ⟩◁ ↦* ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩◁
          rs' = ↦⃖₇ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (b ⃖)) eq)) (λ ()) (λ ()) refl (☐⨾ c₂ • ☐) ++↦ ↦⃖₃ ∷ ◾
        loop₂ rs refl | nothing     | [ eq ] = toState≡₃ (deterministic* rs rs' (is-stuck-toState _ _) (λ ()))
          where
          rs' : ⟨ c₂ ∣ b ∣ c₁ ⨾☐• ☐ ⟩◁ ↦* ⊠
          rs' = ↦⃖₇ ∷ appendκ↦*⊠ (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (b ⃖)) eq)) (λ ()) (☐⨾ c₂ • ☐)
