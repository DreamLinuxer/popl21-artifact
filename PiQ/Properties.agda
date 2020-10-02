module PiQ.Properties where
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Sum
open import Data.Product
open import Data.Maybe
open import Data.Maybe.Properties
open import Data.List as L hiding (_∷_)
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

-- Helper function
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

getₜᵣ⃗ : ∀ {A B} → (c : A ↔ B) → {v : ⟦ A ⟧} {v' : Maybe (Val B A)} → eval c (v ⃗) ≡ v'
       → let tr : Maybe (Val B A) → Set₁
             tr = (λ {(just (w ⃖)) → ⟨ c ∣ v ∣ ☐ ⟩▷ ↦*  ⟨ c ∣ w ∣ ☐ ⟩◁ ;
                      (just (w ⃗)) → ⟨ c ∣ v ∣ ☐ ⟩▷ ↦* ［ c ∣ w ∣ ☐ ］▷ ;
                      nothing      → ⟨ c ∣ v ∣ ☐ ⟩▷ ↦* ⊠ })
         in  tr v'
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
       → let tr : Maybe (Val B A) → Set₁
             tr = (λ {(just (w ⃖)) → ［ c ∣ v ∣ ☐ ］◁ ↦*  ⟨ c ∣ w ∣ ☐ ⟩◁ ;
                      (just (w ⃗)) → ［ c ∣ v ∣ ☐ ］◁ ↦* ［ c ∣ w ∣ ☐ ］▷ ;
                      nothing      → ［ c ∣ v ∣ ☐ ］◁ ↦* ⊠ })
         in  tr v'
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

toState : ∀ {A B C} → (A ↔ B) → (B ↔ C) → Maybe (Val C A) → State
toState c₁ c₂ (just (c ⃗)) = ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］▷
toState c₁ c₂ (just (a ⃖)) = ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩◁
toState c₁ c₂ nothing = ⊠

is-stuck-toState : ∀ {A B C} → (c₁ : A ↔ B) → (c₂ : B ↔ C) → (v : Maybe (Val C A)) → is-stuck (toState c₁ c₂ v)
is-stuck-toState c₁ c₂ (just (c ⃗)) = λ ()
is-stuck-toState c₁ c₂ (just (a ⃖)) = λ ()
is-stuck-toState c₁ c₂ nothing = λ ()

toStateEq₁ : ∀ {A B C c} → (c₁ : A ↔ B) → (c₂ : B ↔ C) → (x : Maybe (Val C A)) → ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］▷ ≡ toState c₁ c₂ x → just (c ⃗) ≡ x
toStateEq₁ c₁ c₂ (just (x ⃗)) refl = refl

toStateEq₂ : ∀ {A B C a} → (c₁ : A ↔ B) → (c₂ : B ↔ C) → (x : Maybe (Val C A)) → ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩◁ ≡ toState c₁ c₂ x → just (a ⃖) ≡ x
toStateEq₂ c₁ c₂ (just (x ⃖)) refl = refl

toStateEq₃ : ∀ {A B C} → (c₁ : A ↔ B) → (c₂ : B ↔ C) → (x : Maybe (Val C A)) → ⊠ ≡ toState c₁ c₂ x → nothing ≡ x
toStateEq₃ c₁ c₂ nothing refl = refl
toStateEq₃ c₁ c₂ (just (x ⃗)) ()
toStateEq₃ c₁ c₂ (just (x ⃖)) ()

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
  eval≡interp (c₁ ⨾ c₂) (a ⃗) with inspect⊎ (run ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩▷) (λ ()) | interp c₁ (a ⃗) | inspect (interp c₁) (a ⃗)
  eval≡interp (c₁ ⨾ c₂) (a ⃗) | inj₁ ((a' , rs) , eq) | just (b ⃗)  | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩▷ ↦* (toState c₁ c₂ (c₁ ⨾[ b ⃗]⨾ c₂))
    rs' = loop₁⃗ c₁ b c₂ (↦⃗₃ ∷ appendκ↦* ((getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (a ⃗)) eq₁))) (λ ()) (λ ()) refl (☐⨾ c₂ • ☐))

    lem : eval (c₁ ⨾ c₂) (a ⃗) ≡ (c₁ ⨾[ b ⃗]⨾ c₂)
    lem with deterministic* rs rs' (λ ()) (is-stuck-toState _ _ _)
    ... | eq' = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ (c₁ ⨾[ b ⃗]⨾ c₂)) eq (toStateEq₂ c₁ c₂ (c₁ ⨾[ b ⃗]⨾ c₂) eq')
  eval≡interp (c₁ ⨾ c₂) (a ⃗) | inj₁ ((a' , rs) , eq) | just (a₁ ⃖) | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⨾ c₂ ∣ a₁ ∣ ☐ ⟩◁
    rs' = ↦⃗₃ ∷ appendκ↦* ((getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (a ⃗)) eq₁))) (λ ()) (λ ()) refl (☐⨾ c₂ • ☐) ++↦ ↦⃖₃ ∷ ◾

    lem : eval (c₁ ⨾ c₂) (a ⃗) ≡ just (a₁ ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (a₁ ⃖)) eq refl
  eval≡interp (c₁ ⨾ c₂) (a ⃗) | inj₁ ((a' , rs) , eq) | nothing     | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩▷ ↦* ⊠
    rs' = ↦⃗₃ ∷ appendκ↦*⊠ ((getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (a ⃗)) eq₁))) (λ ()) (☐⨾ c₂ • ☐)

    lem : eval (c₁ ⨾ c₂) (a ⃗) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⨾ c₂) (a ⃗) | inj₂ (inj₁ ((c , rs) , eq)) | just (b ⃗)  | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩▷ ↦* (toState c₁ c₂ (c₁ ⨾[ b ⃗]⨾ c₂))
    rs' = loop₁⃗ c₁ b c₂ (↦⃗₃ ∷ appendκ↦* ((getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (a ⃗)) eq₁))) (λ ()) (λ ()) refl (☐⨾ c₂ • ☐))

    lem : eval (c₁ ⨾ c₂) (a ⃗) ≡ (c₁ ⨾[ b ⃗]⨾ c₂)
    lem with deterministic* rs rs' (λ ()) (is-stuck-toState _ _ _)
    ... | eq' = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ (c₁ ⨾[ b ⃗]⨾ c₂)) eq (toStateEq₁ c₁ c₂ (c₁ ⨾[ b ⃗]⨾ c₂) eq')
  eval≡interp (c₁ ⨾ c₂) (a ⃗) | inj₂ (inj₁ ((c , rs) , eq)) | just (a' ⃖) | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⨾ c₂ ∣ a' ∣ ☐ ⟩◁
    rs' = ↦⃗₃ ∷ appendκ↦* ((getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (a ⃗)) eq₁))) (λ ()) (λ ()) refl (☐⨾ c₂ • ☐) ++↦ ↦⃖₃ ∷ ◾

    lem : eval (c₁ ⨾ c₂) (a ⃗) ≡ just (a' ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⨾ c₂) (a ⃗) | inj₂ (inj₁ ((c , rs) , eq)) | nothing     | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩▷ ↦* ⊠
    rs' = ↦⃗₃ ∷ appendκ↦*⊠ ((getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (a ⃗)) eq₁))) (λ ()) (☐⨾ c₂ • ☐)

    lem : eval (c₁ ⨾ c₂) (a ⃗) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⨾ c₂) (a ⃗) | inj₂ (inj₂ (rs , eq)) | just (b ⃗)  | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩▷ ↦* (toState c₁ c₂ (c₁ ⨾[ b ⃗]⨾ c₂))
    rs' = loop₁⃗ c₁ b c₂ (↦⃗₃ ∷ appendκ↦* ((getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (a ⃗)) eq₁))) (λ ()) (λ ()) refl (☐⨾ c₂ • ☐))

    lem : eval (c₁ ⨾ c₂) (a ⃗) ≡ (c₁ ⨾[ b ⃗]⨾ c₂)
    lem with deterministic* rs rs' (λ ()) (is-stuck-toState _ _ _)
    ... | eq' = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ (c₁ ⨾[ b ⃗]⨾ c₂)) eq (toStateEq₃ c₁ c₂ (c₁ ⨾[ b ⃗]⨾ c₂) eq')
  eval≡interp (c₁ ⨾ c₂) (a ⃗) | inj₂ (inj₂ (rs , eq)) | just (a' ⃖) | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⨾ c₂ ∣ a' ∣ ☐ ⟩◁
    rs' = ↦⃗₃ ∷ appendκ↦* ((getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (a ⃗)) eq₁))) (λ ()) (λ ()) refl (☐⨾ c₂ • ☐) ++↦ ↦⃖₃ ∷ ◾

    lem : eval (c₁ ⨾ c₂) (a ⃗) ≡ just (a' ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⨾ c₂) (a ⃗) | inj₂ (inj₂ (rs , eq)) | nothing     | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⨾ c₂ ∣ a ∣ ☐ ⟩▷ ↦* ⊠
    rs' = ↦⃗₃ ∷ appendκ↦*⊠ ((getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (a ⃗)) eq₁))) (λ ()) (☐⨾ c₂ • ☐)

    lem : eval (c₁ ⨾ c₂) (a ⃗) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ nothing) eq refl
  eval≡interp (c₁ ⨾ c₂) (c ⃖) with inspect⊎ (run ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］◁) (λ ()) | interp c₂ (c ⃖) | inspect (interp c₂) (c ⃖)
  eval≡interp (c₁ ⨾ c₂) (c ⃖) | inj₁ ((a , rs) , eq) | just (c' ⃗) | [ eq' ] = lem
    where
    rs' : ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］◁ ↦* ［ c₁ ⨾ c₂ ∣ c' ∣ ☐ ］▷
    rs' = ↦⃖₁₀ ∷ appendκ↦* ((getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (c ⃖)) eq'))) (λ ()) (λ ()) refl (c₁ ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾

    lem : eval (c₁ ⨾ c₂) (c ⃖) ≡ just (c' ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⨾ c₂) (c ⃖) | inj₁ ((a , rs) , eq) | just (b ⃖)  | [ eq' ] = lem
    where
    rs' : ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］◁ ↦* (toState c₁ c₂ (c₁ ⨾[ b ⃖]⨾ c₂))
    rs' = loop₂⃖ c₁ b c₂ (↦⃖₁₀ ∷ appendκ↦* ((getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (c ⃖)) eq'))) (λ ()) (λ ()) refl (c₁ ⨾☐• ☐) ++↦ ↦⃖₇ ∷ ◾)

    lem : eval (c₁ ⨾ c₂) (c ⃖) ≡ (c₁ ⨾[ b ⃖]⨾ c₂)
    lem with deterministic* rs rs' (λ ()) (is-stuck-toState _ _ _)
    ... | eq' = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ (c₁ ⨾[ b ⃖]⨾ c₂)) eq (toStateEq₂ c₁ c₂ (c₁ ⨾[ b ⃖]⨾ c₂) eq')
  eval≡interp (c₁ ⨾ c₂) (c ⃖) | inj₁ ((a , rs) , eq) | nothing     | [ eq' ] = lem
    where
    rs' : ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］◁ ↦* ⊠
    rs' = ↦⃖₁₀ ∷ appendκ↦*⊠ ((getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (c ⃖)) eq'))) (λ ()) (c₁ ⨾☐• ☐)

    lem : eval (c₁ ⨾ c₂) (c ⃖) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⨾ c₂) (c ⃖) | inj₂ (inj₁ ((c' , rs) , eq)) | just (c'' ⃗) | [ eq' ] = lem
    where
    rs' : ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］◁ ↦* ［ c₁ ⨾ c₂ ∣ c'' ∣ ☐ ］▷
    rs' = ↦⃖₁₀ ∷ appendκ↦* ((getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (c ⃖)) eq'))) (λ ()) (λ ()) refl (c₁ ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾

    lem : eval (c₁ ⨾ c₂) (c ⃖) ≡ just (c'' ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (c'' ⃗)) eq refl
  eval≡interp (c₁ ⨾ c₂) (c ⃖) | inj₂ (inj₁ ((c' , rs) , eq)) | just (b ⃖)   | [ eq' ] = lem
    where
    rs' : ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］◁ ↦* (toState c₁ c₂ (c₁ ⨾[ b ⃖]⨾ c₂))
    rs' = loop₂⃖ c₁ b c₂ (↦⃖₁₀ ∷ appendκ↦* ((getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (c ⃖)) eq'))) (λ ()) (λ ()) refl (c₁ ⨾☐• ☐) ++↦ ↦⃖₇ ∷ ◾)

    lem : eval (c₁ ⨾ c₂) (c ⃖) ≡ (c₁ ⨾[ b ⃖]⨾ c₂)
    lem with deterministic* rs rs' (λ ()) (is-stuck-toState _ _ _)
    ... | eq' = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ (c₁ ⨾[ b ⃖]⨾ c₂)) eq (toStateEq₁ c₁ c₂ (c₁ ⨾[ b ⃖]⨾ c₂) eq')
  eval≡interp (c₁ ⨾ c₂) (c ⃖) | inj₂ (inj₁ ((c' , rs) , eq)) | nothing      | [ eq' ] = lem
    where
    rs' : ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］◁ ↦* ⊠
    rs' = ↦⃖₁₀ ∷ appendκ↦*⊠ ((getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (c ⃖)) eq'))) (λ ()) (c₁ ⨾☐• ☐)

    lem : eval (c₁ ⨾ c₂) (c ⃖) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⨾ c₂) (c ⃖) | inj₂ (inj₂ (rs , eq)) | just (c' ⃗) | [ eq' ] = lem
    where
    rs' : ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］◁ ↦* ［ c₁ ⨾ c₂ ∣ c' ∣ ☐ ］▷
    rs' = ↦⃖₁₀ ∷ appendκ↦* ((getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (c ⃖)) eq'))) (λ ()) (λ ()) refl (c₁ ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾

    lem : eval (c₁ ⨾ c₂) (c ⃖) ≡ just (c' ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⨾ c₂) (c ⃖) | inj₂ (inj₂ (rs , eq)) | just (b ⃖)  | [ eq' ] = lem
    where
    rs' : ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］◁ ↦* (toState c₁ c₂ (c₁ ⨾[ b ⃖]⨾ c₂))
    rs' = loop₂⃖ c₁ b c₂ (↦⃖₁₀ ∷ appendκ↦* ((getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (c ⃖)) eq'))) (λ ()) (λ ()) refl (c₁ ⨾☐• ☐) ++↦ ↦⃖₇ ∷ ◾)

    lem : eval (c₁ ⨾ c₂) (c ⃖) ≡ (c₁ ⨾[ b ⃖]⨾ c₂)
    lem with deterministic* rs rs' (λ ()) (is-stuck-toState _ _ _)
    ... | eq' = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ (c₁ ⨾[ b ⃖]⨾ c₂)) eq (toStateEq₃ c₁ c₂ (c₁ ⨾[ b ⃖]⨾ c₂) eq')
  eval≡interp (c₁ ⨾ c₂) (c ⃖) | inj₂ (inj₂ (rs , eq)) | nothing     | [ eq' ] = lem
    where
    rs' : ［ c₁ ⨾ c₂ ∣ c ∣ ☐ ］◁ ↦* ⊠
    rs' = ↦⃖₁₀ ∷ appendκ↦*⊠ ((getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (c ⃖)) eq'))) (λ ()) (c₁ ⨾☐• ☐)

    lem : eval (c₁ ⨾ c₂) (c ⃖) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ nothing) eq refl
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) with inspect⊎ (run ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷) (λ ()) | interp c₁ (x ⃗) | inspect (interp c₁) (x ⃗)
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) | inj₁ ((x' , rs) , eq) | just (x₁ ⃗) | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷ ↦* ［ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ］▷
    rs' = ↦⃗₄ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊕ c₂ • ☐) ++↦ ↦⃗₁₁ ∷ ◾

    lem : eval (c₁ ⊕ c₂) (inj₁ x ⃗) ≡ just (inj₁ x₁ ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()    
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) | inj₁ ((x' , rs) , eq) | just (x₁ ⃖) | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ⟩◁
    rs' = ↦⃗₄ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊕ c₂ • ☐) ++↦ ↦⃖₄ ∷ ◾

    lem : eval (c₁ ⊕ c₂) (inj₁ x ⃗) ≡ just (inj₁ x₁ ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (inj₁ x₁ ⃖)) eq refl
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) | inj₁ ((x' , rs) , eq) | nothing      | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷ ↦* ⊠
    rs' = ↦⃗₄ ∷ appendκ↦*⊠ (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (☐⊕ c₂ • ☐)

    lem : eval (c₁ ⊕ c₂) (inj₁ x ⃗) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) | inj₂ (inj₁ ((x' , rs) , eq)) | just (x₁ ⃗) | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷ ↦* ［ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ］▷
    rs' = ↦⃗₄ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊕ c₂ • ☐) ++↦ ↦⃗₁₁ ∷ ◾
    
    lem : eval (c₁ ⊕ c₂) (inj₁ x ⃗) ≡ just (inj₁ x₁ ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (inj₁ x₁ ⃗)) eq refl
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) | inj₂ (inj₁ ((x' , rs) , eq)) | just (x₁ ⃖) | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ⟩◁
    rs' = ↦⃗₄ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊕ c₂ • ☐) ++↦ ↦⃖₄ ∷ ◾

    lem : eval (c₁ ⊕ c₂) (inj₁ x ⃗) ≡ just (inj₁ x₁ ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) | inj₂ (inj₁ ((x' , rs) , eq)) | nothing      | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷ ↦* ⊠
    rs' = ↦⃗₄ ∷ appendκ↦*⊠ (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (☐⊕ c₂ • ☐)

    lem : eval (c₁ ⊕ c₂) (inj₁ x ⃗) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | () 
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) | inj₂ (inj₂ (rs , eq)) | just (x₁ ⃗) | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷ ↦* ［ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ］▷
    rs' = ↦⃗₄ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊕ c₂ • ☐) ++↦ ↦⃗₁₁ ∷ ◾
    
    lem : eval (c₁ ⊕ c₂) (inj₁ x ⃗) ≡ just (inj₁ x₁ ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) | inj₂ (inj₂ (rs , eq)) | just (x₁ ⃖) | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ⟩◁
    rs' = ↦⃗₄ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊕ c₂ • ☐) ++↦ ↦⃖₄ ∷ ◾

    lem : eval (c₁ ⊕ c₂) (inj₁ x ⃗) ≡ just (inj₁ x₁ ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃗) | inj₂ (inj₂ (rs , eq)) | nothing      | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ⟩▷ ↦* ⊠
    rs' = ↦⃗₄ ∷ appendκ↦*⊠ (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (☐⊕ c₂ • ☐)

    lem : eval (c₁ ⊕ c₂) (inj₁ x ⃗) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ nothing) eq refl
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) with inspect⊎ (run ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷) (λ ()) | interp c₂ (y ⃗) | inspect (interp c₂) (y ⃗)
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) | inj₁ ((y' , rs) , eq) | just (y₁ ⃗) | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷ ↦* ［ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ］▷
    rs' = ↦⃗₅ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₁)) (λ ()) (λ ()) refl (c₁ ⊕☐• ☐) ++↦ ↦⃗₁₂ ∷ ◾
    
    lem : eval (c₁ ⊕ c₂) (inj₂ y ⃗) ≡ just (inj₂ y₁ ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) | inj₁ ((y' , rs) , eq) | just (y₁ ⃖) | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ⟩◁
    rs' = ↦⃗₅ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₁)) (λ ()) (λ ()) refl (c₁ ⊕☐• ☐) ++↦ ↦⃖₅ ∷ ◾
    
    lem : eval (c₁ ⊕ c₂) (inj₂ y ⃗) ≡ just (inj₂ y₁ ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (inj₂ y₁ ⃖)) eq refl
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) | inj₁ ((y' , rs) , eq) | nothing      | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷ ↦* ⊠
    rs' = ↦⃗₅ ∷ appendκ↦*⊠ (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₁)) (λ ()) (c₁ ⊕☐• ☐)
    
    lem : eval (c₁ ⊕ c₂) (inj₂ y ⃗) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) | inj₂ (inj₁ ((y' , rs) , eq)) | just (y₁ ⃗) | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷ ↦* ［ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ］▷
    rs' = ↦⃗₅ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₁)) (λ ()) (λ ()) refl (c₁ ⊕☐• ☐) ++↦ ↦⃗₁₂ ∷ ◾
    
    lem : eval (c₁ ⊕ c₂) (inj₂ y ⃗) ≡ just (inj₂ y₁ ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (inj₂ y₁ ⃗)) eq refl
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) | inj₂ (inj₁ ((y' , rs) , eq)) | just (y₁ ⃖) | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ⟩◁
    rs' = ↦⃗₅ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₁)) (λ ()) (λ ()) refl (c₁ ⊕☐• ☐) ++↦ ↦⃖₅ ∷ ◾
    
    lem : eval (c₁ ⊕ c₂) (inj₂ y ⃗) ≡ just (inj₂ y₁ ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) | inj₂ (inj₁ ((y' , rs) , eq)) | nothing      | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷ ↦* ⊠
    rs' = ↦⃗₅ ∷ appendκ↦*⊠ (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₁)) (λ ()) (c₁ ⊕☐• ☐)
    
    lem : eval (c₁ ⊕ c₂) (inj₂ y ⃗) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) | inj₂ (inj₂ (rs , eq)) | just (y₁ ⃗) | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷ ↦* ［ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ］▷
    rs' = ↦⃗₅ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₁)) (λ ()) (λ ()) refl (c₁ ⊕☐• ☐) ++↦ ↦⃗₁₂ ∷ ◾
    
    lem : eval (c₁ ⊕ c₂) (inj₂ y ⃗) ≡ just (inj₂ y₁ ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) | inj₂ (inj₂ (rs , eq)) | just (y₁ ⃖) | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ⟩◁
    rs' = ↦⃗₅ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₁)) (λ ()) (λ ()) refl (c₁ ⊕☐• ☐) ++↦ ↦⃖₅ ∷ ◾
    
    lem : eval (c₁ ⊕ c₂) (inj₂ y ⃗) ≡ just (inj₂ y₁ ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃗) | inj₂ (inj₂ (rs , eq)) | nothing     | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ⟩▷ ↦* ⊠
    rs' = ↦⃗₅ ∷ appendκ↦*⊠ (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₁)) (λ ()) (c₁ ⊕☐• ☐)
    
    lem : eval (c₁ ⊕ c₂) (inj₂ y ⃗) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ nothing) eq refl
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) with inspect⊎ (run ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁) (λ ()) | interp c₁ (x ⃖) | inspect (interp c₁) (x ⃖)
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) | inj₁ ((x' , rs) , eq) | just (x₁ ⃗) | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁ ↦* ［ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ］▷
    rs' = ↦⃖₁₁ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (λ ()) refl (☐⊕ c₂ • ☐) ++↦ ↦⃗₁₁ ∷ ◾

    lem : eval (c₁ ⊕ c₂) (inj₁ x ⃖) ≡ just (inj₁ x₁ ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) | inj₁ ((x' , rs) , eq) | just (x₁ ⃖) | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ⟩◁
    rs' = ↦⃖₁₁ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (λ ()) refl (☐⊕ c₂ • ☐) ++↦ ↦⃖₄ ∷ ◾

    lem : eval (c₁ ⊕ c₂) (inj₁ x ⃖) ≡ just (inj₁ x₁ ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (inj₁ x₁ ⃖)) eq refl
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) | inj₁ ((x' , rs) , eq) | nothing     | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁ ↦* ⊠
    rs' = ↦⃖₁₁ ∷ appendκ↦*⊠ (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (☐⊕ c₂ • ☐)
    
    lem : eval (c₁ ⊕ c₂) (inj₁ x ⃖) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) | inj₂ (inj₁ ((x' , rs) , eq)) | just (x₁ ⃗) | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁ ↦* ［ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ］▷
    rs' = ↦⃖₁₁ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (λ ()) refl (☐⊕ c₂ • ☐) ++↦ ↦⃗₁₁ ∷ ◾

    lem : eval (c₁ ⊕ c₂) (inj₁ x ⃖) ≡ just (inj₁ x₁ ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (inj₁ x₁ ⃗)) eq refl
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) | inj₂ (inj₁ ((x' , rs) , eq)) | just (x₁ ⃖) | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ⟩◁
    rs' = ↦⃖₁₁ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (λ ()) refl (☐⊕ c₂ • ☐) ++↦ ↦⃖₄ ∷ ◾

    lem : eval (c₁ ⊕ c₂) (inj₁ x ⃖) ≡ just (inj₁ x₁ ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) | inj₂ (inj₁ ((x' , rs) , eq)) | nothing     | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁ ↦* ⊠
    rs' = ↦⃖₁₁ ∷ appendκ↦*⊠ (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (☐⊕ c₂ • ☐)
    
    lem : eval (c₁ ⊕ c₂) (inj₁ x ⃖) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) | inj₂ (inj₂ (rs , eq)) | just (x₁ ⃗) | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁ ↦* ［ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ］▷
    rs' = ↦⃖₁₁ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (λ ()) refl (☐⊕ c₂ • ☐) ++↦ ↦⃗₁₁ ∷ ◾

    lem : eval (c₁ ⊕ c₂) (inj₁ x ⃖) ≡ just (inj₁ x₁ ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) | inj₂ (inj₂ (rs , eq)) | just (x₁ ⃖) | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₁ x₁ ∣ ☐ ⟩◁
    rs' = ↦⃖₁₁ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (λ ()) refl (☐⊕ c₂ • ☐) ++↦ ↦⃖₄ ∷ ◾

    lem : eval (c₁ ⊕ c₂) (inj₁ x ⃖) ≡ just (inj₁ x₁ ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₁ x ⃖) | inj₂ (inj₂ (rs , eq)) | nothing     | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₁ x ∣ ☐ ］◁ ↦* ⊠
    rs' = ↦⃖₁₁ ∷ appendκ↦*⊠ (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (☐⊕ c₂ • ☐)
    
    lem : eval (c₁ ⊕ c₂) (inj₁ x ⃖) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ nothing) eq refl
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) with inspect⊎ (run ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁) (λ ()) | interp c₂ (y ⃖) | inspect (interp c₂) (y ⃖)
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) | inj₁ ((x' , rs) , eq) | just (y₁ ⃗) | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁ ↦* ［ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ］▷
    rs' = ↦⃖₁₂ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₁)) (λ ()) (λ ()) refl (c₁ ⊕☐• ☐) ++↦ ↦⃗₁₂ ∷ ◾

    lem : eval (c₁ ⊕ c₂) (inj₂ y ⃖) ≡ just (inj₂ y₁ ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) | inj₁ ((x' , rs) , eq) | just (y₁ ⃖) | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ⟩◁
    rs' = ↦⃖₁₂ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₁)) (λ ()) (λ ()) refl (c₁ ⊕☐• ☐) ++↦ ↦⃖₅ ∷ ◾

    lem : eval (c₁ ⊕ c₂) (inj₂ y ⃖) ≡ just (inj₂ y₁ ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (inj₂ y₁ ⃖)) eq refl
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) | inj₁ ((x' , rs) , eq) | nothing     | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁ ↦* ⊠
    rs' = ↦⃖₁₂ ∷ appendκ↦*⊠ (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₁)) (λ ()) (c₁ ⊕☐• ☐)
    
    lem : eval (c₁ ⊕ c₂) (inj₂ y ⃖) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) | inj₂ (inj₁ ((x' , rs) , eq)) | just (y₁ ⃗) | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁ ↦* ［ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ］▷
    rs' = ↦⃖₁₂ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₁)) (λ ()) (λ ()) refl (c₁ ⊕☐• ☐) ++↦ ↦⃗₁₂ ∷ ◾

    lem : eval (c₁ ⊕ c₂) (inj₂ y ⃖) ≡ just (inj₂ y₁ ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just (inj₂ y₁ ⃗)) eq refl
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) | inj₂ (inj₁ ((x' , rs) , eq)) | just (y₁ ⃖) | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ⟩◁
    rs' = ↦⃖₁₂ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₁)) (λ ()) (λ ()) refl (c₁ ⊕☐• ☐) ++↦ ↦⃖₅ ∷ ◾

    lem : eval (c₁ ⊕ c₂) (inj₂ y ⃖) ≡ just (inj₂ y₁ ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) | inj₂ (inj₁ ((x' , rs) , eq)) | nothing     | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁ ↦* ⊠
    rs' = ↦⃖₁₂ ∷ appendκ↦*⊠ (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₁)) (λ ()) (c₁ ⊕☐• ☐)
    
    lem : eval (c₁ ⊕ c₂) (inj₂ y ⃖) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) | inj₂ (inj₂ (rs , eq)) | just (y₁ ⃗) | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁ ↦* ［ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ］▷
    rs' = ↦⃖₁₂ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₁)) (λ ()) (λ ()) refl (c₁ ⊕☐• ☐) ++↦ ↦⃗₁₂ ∷ ◾

    lem : eval (c₁ ⊕ c₂) (inj₂ y ⃖) ≡ just (inj₂ y₁ ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) | inj₂ (inj₂ (rs , eq)) | just (y₁ ⃖) | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁ ↦* ⟨ c₁ ⊕ c₂ ∣ inj₂ y₁ ∣ ☐ ⟩◁
    rs' = ↦⃖₁₂ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₁)) (λ ()) (λ ()) refl (c₁ ⊕☐• ☐) ++↦ ↦⃖₅ ∷ ◾

    lem : eval (c₁ ⊕ c₂) (inj₂ y ⃖) ≡ just (inj₂ y₁ ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊕ c₂) (inj₂ y ⃖) | inj₂ (inj₂ (rs , eq)) | nothing     | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊕ c₂ ∣ inj₂ y ∣ ☐ ］◁ ↦* ⊠
    rs' = ↦⃖₁₂ ∷ appendκ↦*⊠ (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₁)) (λ ()) (c₁ ⊕☐• ☐)
    
    lem : eval (c₁ ⊕ c₂) (inj₂ y ⃖) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ nothing) eq refl
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) with inspect⊎ (run ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷) (λ ()) | interp c₁ (x ⃗) | inspect (interp c₁) (x ⃗)
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₁ (((x' , y') , rs) , eq) | just (x₁ ⃗) | [ eq₁ ] with interp c₂ (y ⃗) | inspect (interp c₂) (y ⃗)
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₁ (((x' , y') , rs) , eq) | just (x₁ ⃗) | [ eq₁ ] | just (y₁ ⃗) | [ eq₂ ] = lem
    where
    rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ［ c₁ ⊗ c₂ ∣ (x₁ , y₁) ∣ ☐ ］▷
    rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y ]• ☐) ++↦
          ↦⃗₈ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x₁ ]⊗☐• ☐) ++↦ ↦⃗₉ ∷ ◾
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃗) ≡ just ((x₁ , y₁) ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₁ (((x' , y') , rs) , eq) | just (x₁ ⃗) | [ eq₁ ] | just (y₁ ⃖) | [ eq₂ ] = lem
    where
    rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊗ c₂ ∣ (x , y₁) ∣ ☐ ⟩◁
    rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y ]• ☐) ++↦
          ↦⃗₈ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x₁ ]⊗☐• ☐) ++↦
          ↦⃖₈ ∷ Rev* (appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y₁ ]• ☐)) (λ ()) (λ ()) ++↦ ↦⃖₆ ∷ ◾
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃗) ≡ just ((x , y₁) ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ z → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ z ≡ just ((x , y₁) ⃖)) eq refl
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₁ (((x' , y') , rs) , eq) | just (x₁ ⃗) | [ eq₁ ] | nothing     | [ eq₂ ] = lem
    where
    rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⊠
    rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y ]• ☐) ++↦
          ↦⃗₈ ∷ appendκ↦*⊠ (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₂)) (λ ()) ([ c₁ , x₁ ]⊗☐• ☐)
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃗) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₁ (((x' , y') , rs) , eq) | just (x₁ ⃖) | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊗ c₂ ∣ (x₁ , y) ∣ ☐ ⟩◁
    rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y ]• ☐) ++↦ ↦⃖₆ ∷ ◾

    lem : eval (c₁ ⊗ c₂) ((x , y) ⃗) ≡ just ((x₁ , y) ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ x → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ x ≡ just ((x₁ , y) ⃖)) eq refl
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₁ (((x' , y') , rs) , eq) | nothing     | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⊠
    rs' = ↦⃗₆ ∷ appendκ↦*⊠ (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (☐⊗[ c₂ , y ]• ☐)
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃗) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₂ (inj₁ (((x' , y') , rs) , eq)) | just (x₁ ⃗) | [ eq₁ ] with interp c₂ (y ⃗) | inspect (interp c₂) (y ⃗)
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₂ (inj₁ (((x' , y') , rs) , eq)) | just (x₁ ⃗) | [ eq₁ ] | just (y₁ ⃗) | [ eq₂ ] = lem
    where
    rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ［ c₁ ⊗ c₂ ∣ (x₁ , y₁) ∣ ☐ ］▷
    rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y ]• ☐) ++↦
          ↦⃗₈ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x₁ ]⊗☐• ☐) ++↦ ↦⃗₉ ∷ ◾
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃗) ≡ just ((x₁ , y₁) ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ z → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ z ≡ just ((x₁ , y₁) ⃗)) eq refl
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₂ (inj₁ (((x' , y') , rs) , eq)) | just (x₁ ⃗) | [ eq₁ ] | just (y₁ ⃖) | [ eq₂ ] = lem
    where
    rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊗ c₂ ∣ (x , y₁) ∣ ☐ ⟩◁
    rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y ]• ☐) ++↦
          ↦⃗₈ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x₁ ]⊗☐• ☐) ++↦
          ↦⃖₈ ∷ Rev* (appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y₁ ]• ☐)) (λ ()) (λ ()) ++↦ ↦⃖₆ ∷ ◾
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃗) ≡ just ((x , y₁) ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₂ (inj₁ (((x' , y') , rs) , eq)) | just (x₁ ⃗) | [ eq₁ ] | nothing     | [ eq₂ ] = lem
    where
    rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⊠
    rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y ]• ☐) ++↦
          ↦⃗₈ ∷ appendκ↦*⊠ (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₂)) (λ ()) ([ c₁ , x₁ ]⊗☐• ☐)
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃗) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₂ (inj₁ (((x' , y') , rs) , eq)) | just (x₁ ⃖) | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊗ c₂ ∣ (x₁ , y) ∣ ☐ ⟩◁
    rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y ]• ☐) ++↦ ↦⃖₆ ∷ ◾

    lem : eval (c₁ ⊗ c₂) ((x , y) ⃗) ≡ just ((x₁ , y) ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₂ (inj₁ (((x' , y') , rs) , eq)) | nothing     | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⊠
    rs' = ↦⃗₆ ∷ appendκ↦*⊠ (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (☐⊗[ c₂ , y ]• ☐)
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃗) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₂ (inj₂ (rs , eq)) | just (x₁ ⃗) | [ eq₁ ] with interp c₂ (y ⃗) | inspect (interp c₂) (y ⃗)
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₂ (inj₂ (rs , eq)) | just (x₁ ⃗) | [ eq₁ ] | just (y₁ ⃗) | [ eq₂ ] = lem
    where
    rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ［ c₁ ⊗ c₂ ∣ (x₁ , y₁) ∣ ☐ ］▷
    rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y ]• ☐) ++↦
          ↦⃗₈ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x₁ ]⊗☐• ☐) ++↦ ↦⃗₉ ∷ ◾
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃗) ≡ just ((x₁ , y₁) ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₂ (inj₂ (rs , eq)) | just (x₁ ⃗) | [ eq₁ ] | just (y₁ ⃖) | [ eq₂ ] = lem
    where
    rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊗ c₂ ∣ (x , y₁) ∣ ☐ ⟩◁
    rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y ]• ☐) ++↦
          ↦⃗₈ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x₁ ]⊗☐• ☐) ++↦
          ↦⃖₈ ∷ Rev* (appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y₁ ]• ☐)) (λ ()) (λ ()) ++↦ ↦⃖₆ ∷ ◾
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃗) ≡ just ((x , y₁) ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₂ (inj₂ (rs , eq)) | just (x₁ ⃗) | [ eq₁ ] | nothing     | [ eq₂ ] = lem
    where
    rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⊠
    rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y ]• ☐) ++↦
          ↦⃗₈ ∷ appendκ↦*⊠ (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (y ⃗)) eq₂)) (λ ()) ([ c₁ , x₁ ]⊗☐• ☐)
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃗) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ z → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ z ≡ nothing) eq refl
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₂ (inj₂ (rs , eq)) | just (x₁ ⃖) | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⟨ c₁ ⊗ c₂ ∣ (x₁ , y) ∣ ☐ ⟩◁
    rs' = ↦⃗₆ ∷ appendκ↦* (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y ]• ☐) ++↦ ↦⃖₆ ∷ ◾

    lem : eval (c₁ ⊗ c₂) ((x , y) ⃗) ≡ just ((x₁ , y) ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃗) | inj₂ (inj₂ (rs , eq)) | nothing     | [ eq₁ ] = lem
    where
    rs' : ⟨ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ⟩▷ ↦* ⊠
    rs' = ↦⃗₆ ∷ appendκ↦*⊠ (getₜᵣ⃗ c₁ (trans (eval≡interp c₁ (x ⃗)) eq₁)) (λ ()) (☐⊗[ c₂ , y ]• ☐)
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃗) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ z → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ z ≡ nothing) eq refl
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) with inspect⊎ (run ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁) (λ ()) | interp c₂ (y ⃖) | inspect (interp c₂) (y ⃖)
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₁ (((x' , y') , rs) , eq) | just (y₁ ⃗) | [ eq₂ ] = lem
    where
    rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ［ c₁ ⊗ c₂ ∣ (x , y₁) ∣ ☐ ］▷
    rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x ]⊗☐• ☐) ++↦ ↦⃗₉ ∷ ◾
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃖) ≡ just ((x , y₁) ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₁ (((x' , y') , rs) , eq) | just (y₁ ⃖) | [ eq₂ ] with interp c₁ (x ⃖) | inspect (interp c₁) (x ⃖)
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₁ (((x' , y') , rs) , eq) | just (y₁ ⃖) | [ eq₂ ] | just (x₁ ⃗) | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ［ c₁ ⊗ c₂ ∣ (x₁ , y) ∣ ☐ ］▷
    rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x ]⊗☐• ☐) ++↦
          ↦⃖₈ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y₁ ]• ☐) ++↦
          ↦⃗₈ ∷ Rev* (appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x₁ ]⊗☐• ☐)) (λ ()) (λ ()) ++↦ ↦⃗₉ ∷ ◾
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃖) ≡ just ((x₁ , y) ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₁ (((x' , y') , rs) , eq) | just (y₁ ⃖) | [ eq₂ ] | just (x₁ ⃖) | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ⟨ c₁ ⊗ c₂ ∣ (x₁ , y₁) ∣ ☐ ⟩◁
    rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x ]⊗☐• ☐) ++↦
          ↦⃖₈ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y₁ ]• ☐) ++↦ ↦⃖₆ ∷ ◾
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃖) ≡ just ((x₁ , y₁) ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ z → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ z ≡ just ((x₁ , y₁) ⃖)) eq refl
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₁ (((x' , y') , rs) , eq) | just (y₁ ⃖) | [ eq₂ ] | nothing     | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ⊠
    rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x ]⊗☐• ☐) ++↦
          ↦⃖₈ ∷ appendκ↦*⊠ (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (☐⊗[ c₂ , y₁ ]• ☐)
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃖) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₁ (((x' , y') , rs) , eq) | nothing     | [ eq₂ ] = lem
    where
    rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ⊠
    rs' = ↦⃖₉ ∷ appendκ↦*⊠ (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) ([ c₁ , x ]⊗☐• ☐)
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃖) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₂ (inj₁ (((x' , y') , rs) , eq)) | just (y₁ ⃗) | [ eq₂ ] = lem
    where
    rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ［ c₁ ⊗ c₂ ∣ (x , y₁) ∣ ☐ ］▷
    rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x ]⊗☐• ☐) ++↦ ↦⃗₉ ∷ ◾
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃖) ≡ just ((x , y₁) ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ z → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ z ≡ just ((x , y₁) ⃗)) eq refl
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₂ (inj₁ (((x' , y') , rs) , eq)) | just (y₁ ⃖) | [ eq₂ ] with interp c₁ (x ⃖) | inspect (interp c₁) (x ⃖)
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₂ (inj₁ (((x' , y') , rs) , eq)) | just (y₁ ⃖) | [ eq₂ ] | just (x₁ ⃗) | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ［ c₁ ⊗ c₂ ∣ (x₁ , y) ∣ ☐ ］▷
    rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x ]⊗☐• ☐) ++↦
          ↦⃖₈ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y₁ ]• ☐) ++↦
          ↦⃗₈ ∷ Rev* (appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x₁ ]⊗☐• ☐)) (λ ()) (λ ()) ++↦ ↦⃗₉ ∷ ◾
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃖) ≡ just ((x₁ , y) ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ z → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ z ≡ just ((x₁ , y) ⃗)) eq refl
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₂ (inj₁ (((x' , y') , rs) , eq)) | just (y₁ ⃖) | [ eq₂ ] | just (x₁ ⃖) | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ⟨ c₁ ⊗ c₂ ∣ (x₁ , y₁) ∣ ☐ ⟩◁
    rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x ]⊗☐• ☐) ++↦
          ↦⃖₈ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y₁ ]• ☐) ++↦ ↦⃖₆ ∷ ◾
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃖) ≡ just ((x₁ , y₁) ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₂ (inj₁ (((x' , y') , rs) , eq)) | just (y₁ ⃖) | [ eq₂ ] | nothing     | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ⊠
    rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x ]⊗☐• ☐) ++↦
          ↦⃖₈ ∷ appendκ↦*⊠ (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (☐⊗[ c₂ , y₁ ]• ☐)
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃖) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₂ (inj₁ (((x' , y') , rs) , eq)) | nothing     | [ eq₂ ] = lem
    where
    rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ⊠
    rs' = ↦⃖₉ ∷ appendκ↦*⊠ (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) ([ c₁ , x ]⊗☐• ☐)
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃖) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₂ (inj₂ (rs , eq)) | just (y₁ ⃗) | [ eq₂ ] = lem
    where
    rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ［ c₁ ⊗ c₂ ∣ (x , y₁) ∣ ☐ ］▷
    rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x ]⊗☐• ☐) ++↦ ↦⃗₉ ∷ ◾
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃖) ≡ just ((x , y₁) ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₂ (inj₂ (rs , eq)) | just (y₁ ⃖) | [ eq₂ ] with interp c₁ (x ⃖) | inspect (interp c₁) (x ⃖)
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₂ (inj₂ (rs , eq)) | just (y₁ ⃖) | [ eq₂ ] | just (x₁ ⃗) | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ［ c₁ ⊗ c₂ ∣ (x₁ , y) ∣ ☐ ］▷
    rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x ]⊗☐• ☐) ++↦
          ↦⃖₈ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y₁ ]• ☐) ++↦
          ↦⃗₈ ∷ Rev* (appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x₁ ]⊗☐• ☐)) (λ ()) (λ ()) ++↦ ↦⃗₉ ∷ ◾
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃖) ≡ just ((x₁ , y) ⃗)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₂ (inj₂ (rs , eq)) | just (y₁ ⃖) | [ eq₂ ] | just (x₁ ⃖) | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ⟨ c₁ ⊗ c₂ ∣ (x₁ , y₁) ∣ ☐ ⟩◁
    rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x ]⊗☐• ☐) ++↦
          ↦⃖₈ ∷ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (λ ()) refl (☐⊗[ c₂ , y₁ ]• ☐) ++↦ ↦⃖₆ ∷ ◾
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃖) ≡ just ((x₁ , y₁) ⃖)
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | ()
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₂ (inj₂ (rs , eq)) | just (y₁ ⃖) | [ eq₂ ] | nothing     | [ eq₁ ] = lem
    where
    rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ⊠
    rs' = ↦⃖₉ ∷ appendκ↦* (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) (λ ()) refl ([ c₁ , x ]⊗☐• ☐) ++↦
          ↦⃖₈ ∷ appendκ↦*⊠ (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (x ⃖)) eq₁)) (λ ()) (☐⊗[ c₂ , y₁ ]• ☐)
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃖) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ z → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ z ≡ nothing) eq refl
  eval≡interp (c₁ ⊗ c₂) ((x , y) ⃖) | inj₂ (inj₂ (rs , eq)) | nothing     | [ eq₂ ] = lem
    where
    rs' : ［ c₁ ⊗ c₂ ∣ (x , y) ∣ ☐ ］◁ ↦* ⊠
    rs' = ↦⃖₉ ∷ appendκ↦*⊠ (getₜᵣ⃖ c₂ (trans (eval≡interp c₂ (y ⃖)) eq₂)) (λ ()) ([ c₁ , x ]⊗☐• ☐)
    
    lem : eval (c₁ ⊗ c₂) ((x , y) ⃖) ≡ nothing
    lem with deterministic* rs rs' (λ ()) (λ ())
    ... | refl = subst (λ z → [ just ∘ _⃖ ∘ proj₁ , [ just ∘ _⃗ ∘ proj₁ , (λ _ → nothing) ]′ ]′ z ≡ nothing) eq refl

  -- Termination is guarantee by PiQ.NoRepeat:
  -- The execution trace in the argument will grow in every mutual recursive call, but it can only has finite length.
  {-# TERMINATING #-}
  loop₁⃗ : ∀ {A B C a₀} → (c₁ : A ↔ B) → (b : ⟦ B ⟧) → (c₂ : B ↔ C)
         → ⟨ c₁ ⨾ c₂ ∣ a₀ ∣ ☐ ⟩▷ ↦* ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷
         → ⟨ c₁ ⨾ c₂ ∣ a₀ ∣ ☐ ⟩▷ ↦* (toState c₁ c₂ (c₁ ⨾[ b ⃗]⨾ c₂))
  loop₁⃗ c₁ b c₂ rsₐ with interp c₂ (b ⃗) | inspect (interp c₂) (b ⃗)
  loop₁⃗ c₁ b c₂ rsₐ | just (c ⃗)  | [ eq ] = rsₐ ++↦ ↦⃗₇ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (b ⃗)) eq)) (λ ()) (λ ()) refl (c₁ ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾
  loop₁⃗ c₁ b c₂ rsₐ | just (b' ⃖) | [ eq ] = loop₂⃗ c₁ b' c₂ (rsₐ ++↦ ↦⃗₇ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (b ⃗)) eq)) (λ ()) (λ ()) refl (c₁ ⨾☐• ☐) ++↦ ↦⃖₇ ∷ ◾)
  loop₁⃗ c₁ b c₂ rsₐ | nothing     | [ eq ] = rsₐ ++↦ ↦⃗₇ ∷ appendκ↦*⊠ (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (b ⃗)) eq)) (λ ()) (c₁ ⨾☐• ☐)  
  
  loop₂⃗ : ∀ {A B C a₀} → (c₁ : A ↔ B) → (b : ⟦ B ⟧) → (c₂ : B ↔ C)
        → ⟨ c₁ ⨾ c₂ ∣ a₀ ∣ ☐ ⟩▷ ↦* ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］◁
        → ⟨ c₁ ⨾ c₂ ∣ a₀ ∣ ☐ ⟩▷ ↦* (toState c₁ c₂ (c₁ ⨾[ b ⃖]⨾ c₂))
  loop₂⃗ c₁ b c₂ rsₐ with interp c₁ (b ⃖) | inspect (interp c₁) (b ⃖)
  loop₂⃗ c₁ b c₂ rsₐ | just (b' ⃗) | [ eq ] = loop₁⃗ c₁ b' c₂ (rsₐ ++↦ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (b ⃖)) eq)) (λ ()) (λ ()) refl (☐⨾ c₂ • ☐))
  loop₂⃗ c₁ b c₂ rsₐ | just (a ⃖)  | [ eq ] = rsₐ ++↦ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (b ⃖)) eq)) (λ ()) (λ ()) refl (☐⨾ c₂ • ☐) ++↦ ↦⃖₃ ∷ ◾
  loop₂⃗ c₁ b c₂ rsₐ | nothing     | [ eq ] = rsₐ ++↦ appendκ↦*⊠ (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (b ⃖)) eq)) (λ ()) (☐⨾ c₂ • ☐)

  loop₁⃖ : ∀ {A B C c₀} → (c₁ : A ↔ B) → (b : ⟦ B ⟧) → (c₂ : B ↔ C)
         → ［ c₁ ⨾ c₂ ∣ c₀ ∣ ☐ ］◁ ↦* ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］▷
         → ［ c₁ ⨾ c₂ ∣ c₀ ∣ ☐ ］◁ ↦* (toState c₁ c₂ (c₁ ⨾[ b ⃗]⨾ c₂))
  loop₁⃖ c₁ b c₂ rsₐ with interp c₂ (b ⃗) | inspect (interp c₂) (b ⃗)
  loop₁⃖ c₁ b c₂ rsₐ | just (c ⃗)  | [ eq ] = rsₐ ++↦ ↦⃗₇ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (b ⃗)) eq)) (λ ()) (λ ()) refl (c₁ ⨾☐• ☐) ++↦ ↦⃗₁₀ ∷ ◾
  loop₁⃖ c₁ b c₂ rsₐ | just (b' ⃖) | [ eq ] = loop₂⃖ c₁ b' c₂ (rsₐ ++↦ ↦⃗₇ ∷ appendκ↦* (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (b ⃗)) eq)) (λ ()) (λ ()) refl (c₁ ⨾☐• ☐) ++↦ ↦⃖₇ ∷ ◾)
  loop₁⃖ c₁ b c₂ rsₐ | nothing     | [ eq ] = rsₐ ++↦ ↦⃗₇ ∷ appendκ↦*⊠ (getₜᵣ⃗ c₂ (trans (eval≡interp c₂ (b ⃗)) eq)) (λ ()) (c₁ ⨾☐• ☐)

  loop₂⃖ : ∀ {A B C c₀} → (c₁ : A ↔ B) → (b : ⟦ B ⟧) → (c₂ : B ↔ C)
        → ［ c₁ ⨾ c₂ ∣ c₀ ∣ ☐ ］◁ ↦* ［ c₁ ∣ b ∣ ☐⨾ c₂ • ☐ ］◁
        → ［ c₁ ⨾ c₂ ∣ c₀ ∣ ☐ ］◁ ↦* (toState c₁ c₂ (c₁ ⨾[ b ⃖]⨾ c₂))
  loop₂⃖ c₁ b c₂ rsₐ with interp c₁ (b ⃖) | inspect (interp c₁) (b ⃖)
  loop₂⃖ c₁ b c₂ rsₐ | just (b' ⃗)  | [ eq ] = loop₁⃖ c₁ b' c₂ (rsₐ ++↦ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (b ⃖)) eq)) (λ ()) (λ ()) refl (☐⨾ c₂ • ☐))
  loop₂⃖ c₁ b c₂ rsₐ | just (a ⃖)   | [ eq ] = rsₐ ++↦ appendκ↦* (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (b ⃖)) eq)) (λ ()) (λ ()) refl (☐⨾ c₂ • ☐) ++↦ ↦⃖₃ ∷ ◾
  loop₂⃖ c₁ b c₂ rsₐ | nothing      | [ eq ] = rsₐ ++↦ appendκ↦*⊠ (getₜᵣ⃖ c₁ (trans (eval≡interp c₁ (b ⃖)) eq)) (λ ()) (☐⨾ c₂ • ☐)
