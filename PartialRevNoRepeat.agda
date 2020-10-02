import Level as L
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import RevMachine

module PartialRevNoRepeat {ℓ} (M : PartialRevMachine {ℓ}) where
  infix  99 _ᵣₑᵥ
  infixr 10 _∷_
  infixr 10 _++↦_

  open RevMachine.PartialRevMachine M

  is-stuck : State → Set _
  is-stuck st = ∄[ st' ] (st ↦ st')

  is-initial : State → Set _
  is-initial st = ∄[ st' ] (st' ↦ st)

  data _↦ᵣₑᵥ_ : State → State → Set (L.suc ℓ) where
    _ᵣₑᵥ : ∀ {st₁ st₂} → st₁ ↦ st₂ → st₂ ↦ᵣₑᵥ st₁

  data _↦*_ : State → State → Set (L.suc ℓ) where
    ◾ : {st : State} → st ↦* st
    _∷_ : {st₁ st₂ st₃ : State} → st₁ ↦ st₂ → st₂ ↦* st₃ → st₁ ↦* st₃

  _++↦_ : {st₁ st₂ st₃ : State} → st₁ ↦* st₂ → st₂ ↦* st₃ → st₁ ↦* st₃
  ◾ ++↦ st₁↦*st₂ = st₁↦*st₂
  (st₁↦st₁' ∷ st₁'↦*st₂) ++↦ st₂'↦*st₃ = st₁↦st₁' ∷ (st₁'↦*st₂ ++↦ st₂'↦*st₃)

  data _↦ᵣₑᵥ*_ : State → State → Set (L.suc ℓ) where
    ◾ : ∀ {st} → st ↦ᵣₑᵥ* st
    _∷_ : ∀ {st₁ st₂ st₃} → st₁ ↦ᵣₑᵥ st₂ → st₂ ↦ᵣₑᵥ* st₃ → st₁ ↦ᵣₑᵥ* st₃

  _++↦ᵣₑᵥ_ : ∀ {st₁ st₂ st₃} → st₁ ↦ᵣₑᵥ* st₂ → st₂ ↦ᵣₑᵥ* st₃ → st₁ ↦ᵣₑᵥ* st₃
  ◾ ++↦ᵣₑᵥ st₁↦ᵣₑᵥ*st₂ = st₁↦ᵣₑᵥ*st₂
  (st₁↦ᵣₑᵥst₁' ∷ st₁'↦ᵣₑᵥ*st₂) ++↦ᵣₑᵥ st₂'↦ᵣₑᵥ*st₃ = st₁↦ᵣₑᵥst₁' ∷ (st₁'↦ᵣₑᵥ*st₂ ++↦ᵣₑᵥ st₂'↦ᵣₑᵥ*st₃)

  Rev↦ : ∀ {st₁ st₂} → st₁ ↦* st₂ → st₂ ↦ᵣₑᵥ* st₁
  Rev↦ ◾ = ◾
  Rev↦ (r ∷ rs) = Rev↦ rs ++↦ᵣₑᵥ ((r ᵣₑᵥ) ∷ ◾)

  Rev↦ᵣₑᵥ : ∀ {st₁ st₂} → st₁ ↦ᵣₑᵥ* st₂ → st₂ ↦* st₁
  Rev↦ᵣₑᵥ ◾ = ◾
  Rev↦ᵣₑᵥ ((r ᵣₑᵥ) ∷ rs) = Rev↦ᵣₑᵥ rs ++↦ (r ∷ ◾)

  deterministic* : ∀ {st st₁ st₂} → st ↦* st₁ → st ↦* st₂
                 → is-stuck st₁ → is-stuck st₂
                 → st₁ ≡ st₂
  deterministic* ◾ ◾ stuck₁ stuck₂ = refl
  deterministic* ◾ (r ∷ ↦*₂) stuck₁ stuck₂ = ⊥-elim (stuck₁ (_ , r))
  deterministic* (r ∷ ↦*₁) ◾ stuck₁ stuck₂ = ⊥-elim (stuck₂ (_ , r))
  deterministic* (r₁ ∷ ↦*₁) (r₂ ∷ ↦*₂) stuck₁ stuck₂ with deterministic r₁ r₂
  ... | refl = deterministic* ↦*₁ ↦*₂ stuck₁ stuck₂

  deterministicᵣₑᵥ* : ∀ {st st₁ st₂} → st ↦ᵣₑᵥ* st₁ → st ↦ᵣₑᵥ* st₂ → ¬ (is-fail st)
                    → is-initial st₁ → is-initial st₂
                    → st₁ ≡ st₂
  deterministicᵣₑᵥ* ◾ ◾ _ initial₁ initial₂ = refl
  deterministicᵣₑᵥ* ◾ (r ᵣₑᵥ ∷ ↦ᵣₑᵥ*₂) _ initial₁ initial₂ = ⊥-elim (initial₁ (_ , r))
  deterministicᵣₑᵥ* (r ᵣₑᵥ ∷ ↦ᵣₑᵥ*₁) ◾ _ initial₁ initial₂ = ⊥-elim (initial₂ (_ , r))
  deterministicᵣₑᵥ* (_∷_ {_} {st'} {_} (r₁ ᵣₑᵥ) ↦ᵣₑᵥ*₁) (r₂ ᵣₑᵥ ∷ ↦ᵣₑᵥ*₂) nf initial₁ initial₂ with is-fail? st'
  ... | yes st'-f  = ⊥-elim (fail-is-stuck st'-f (_ , r₁))
  ... | no  st'-nf with deterministicᵣₑᵥ r₁ r₂ nf
  ... | refl = deterministicᵣₑᵥ* ↦ᵣₑᵥ*₁ ↦ᵣₑᵥ*₂ st'-nf initial₁ initial₂

  data _↦[_]_ : State → ℕ → State → Set (L.suc ℓ) where
    ◾ : ∀ {st} → st ↦[ 0 ] st
    _∷_ : ∀ {st₁ st₂ st₃ n} → st₁ ↦ st₂ → st₂ ↦[ n ] st₃ → st₁ ↦[ suc n ] st₃

  _++↦ⁿ_ : ∀ {st₁ st₂ st₃ n m} → st₁ ↦[ n ] st₂ → st₂ ↦[ m ] st₃ → st₁ ↦[ n + m ] st₃
  ◾ ++↦ⁿ st₁↦*st₂ = st₁↦*st₂
  (st₁↦st₁' ∷ st₁'↦*st₂) ++↦ⁿ st₂'↦*st₃ = st₁↦st₁' ∷ (st₁'↦*st₂ ++↦ⁿ st₂'↦*st₃)

  data _↦ᵣₑᵥ[_]_ : State → ℕ → State → Set (L.suc ℓ) where
    ◾ : ∀ {st} → st ↦ᵣₑᵥ[ 0 ] st
    _∷_ : ∀ {st₁ st₂ st₃ n} → st₁ ↦ᵣₑᵥ st₂ → st₂ ↦ᵣₑᵥ[ n ] st₃ → st₁ ↦ᵣₑᵥ[ suc n ] st₃

  _++↦ᵣₑᵥⁿ_ : ∀ {st₁ st₂ st₃ n m} → st₁ ↦ᵣₑᵥ[ n ] st₂ → st₂ ↦ᵣₑᵥ[ m ] st₃ → st₁ ↦ᵣₑᵥ[ n + m ] st₃
  ◾ ++↦ᵣₑᵥⁿ st₁↦*st₂ = st₁↦*st₂
  (st₁↦st₁' ∷ st₁'↦*st₂) ++↦ᵣₑᵥⁿ st₂'↦*st₃ = st₁↦st₁' ∷ (st₁'↦*st₂ ++↦ᵣₑᵥⁿ st₂'↦*st₃)

  deterministicⁿ : ∀ {st st₁ st₂ n} → st ↦[ n ] st₁ → st ↦[ n ] st₂
                 → st₁ ≡ st₂
  deterministicⁿ ◾ ◾ = refl
  deterministicⁿ (r₁ ∷ rs₁) (r₂ ∷ rs₂) with deterministic r₁ r₂
  ... | refl = deterministicⁿ rs₁ rs₂

  deterministicᵣₑᵥⁿ : ∀ {st st₁ st₂ n} → st ↦ᵣₑᵥ[ n ] st₁ → st ↦ᵣₑᵥ[ n ] st₂ → ¬ (is-fail st)
                    → st₁ ≡ st₂
  deterministicᵣₑᵥⁿ ◾ ◾ _ = refl
  deterministicᵣₑᵥⁿ (_∷_ {_} {st'} {_} (r₁ ᵣₑᵥ)  rs₁) (r₂ ᵣₑᵥ ∷ rs₂) nf with is-fail? st'
  ... | yes st'-f  = ⊥-elim (fail-is-stuck st'-f (_ , r₁))
  ... | no  st'-nf with deterministicᵣₑᵥ r₁ r₂ nf
  ... | refl = deterministicᵣₑᵥⁿ rs₁ rs₂ st'-nf

  private
    split↦ⁿ : ∀ {st st'' n m} → st ↦[ n + m ] st''
            → ∃[ st' ] (st ↦[ n ] st' × st' ↦[ m ] st'')
    split↦ⁿ {n = 0} {m} rs = _ , ◾ , rs
    split↦ⁿ {n = suc n} {m} (r ∷ rs) with split↦ⁿ {n = n} {m} rs
    ... | st' , st↦ⁿst' , st'↦ᵐst'' = st' , (r ∷ st↦ⁿst') , st'↦ᵐst''

    split↦ᵣₑᵥⁿ : ∀ {st st'' n m} → st ↦ᵣₑᵥ[ n + m ] st''
               → ∃[ st' ] (st ↦ᵣₑᵥ[ n ] st' × st' ↦ᵣₑᵥ[ m ] st'')
    split↦ᵣₑᵥⁿ {n = 0} {m} rs = _ , ◾ , rs
    split↦ᵣₑᵥⁿ {n = suc n} {m} (r ∷ rs) with split↦ᵣₑᵥⁿ {n = n} {m} rs
    ... | st' , st↦ⁿst' , st'↦ᵐst'' = st' , (r ∷ st↦ⁿst') , st'↦ᵐst''

    diff : ∀ {n m} → n < m → ∃[ k ] (0 < k × n + k ≡ m)
    diff {0} {(suc m)} (s≤s z≤n) = suc m , s≤s z≤n , refl
    diff {(suc n)} {(suc (suc m))} (s≤s (s≤s n≤m)) with diff {n} {suc m} (s≤s n≤m)
    ... | k , 0<k , eq = k , 0<k , cong suc eq

  Revⁿ : ∀ {st st' n} → st ↦[ n ] st' → st' ↦ᵣₑᵥ[ n ] st
  Revⁿ {n = 0} ◾ = ◾
  Revⁿ {n = suc n} (r ∷ rs) rewrite +-comm 1 n = Revⁿ rs ++↦ᵣₑᵥⁿ (r ᵣₑᵥ ∷ ◾)

  NoRepeat : ∀ {st₀ stₙ stₘ n m}
           → is-initial st₀
           → n < m
           → st₀ ↦[ n ] stₙ
           → st₀ ↦[ m ] stₘ
           → stₙ ≢ stₘ
  NoRepeat {stₙ = st} {_} {m} st₀-is-init n<m st₀↦ᵐst st₀↦ᵐ⁺ᵏ⁺¹st refl with diff n<m
  ... | suc k , 0<k , refl with is-fail? st
  ... | yes st-is-f with split↦ⁿ {n = m} {1 + k} st₀↦ᵐ⁺ᵏ⁺¹st
  ... | st′ , st₀↦ᵐst′ , (r ∷ rs) with deterministicⁿ st₀↦ᵐst st₀↦ᵐst′
  ... | refl = ⊥-elim (fail-is-stuck st-is-f (_ , r))
  NoRepeat {stₙ = st} {_} {m} st₀-is-init n<m st₀↦ᵐst st₀↦ᵐ⁺ᵏ⁺¹st refl | suc k , 0<k , refl | no st-is-nf with (Revⁿ st₀↦ᵐst , Revⁿ st₀↦ᵐ⁺ᵏ⁺¹st)
  ... | st'↦ᵐst₀' , st'↦ᵐ⁺ᵏ⁺¹st₀' with split↦ᵣₑᵥⁿ st'↦ᵐ⁺ᵏ⁺¹st₀'
  ... | st′ , st'↦ᵐst′ , st′↦ᵏ⁺¹st₀' with deterministicᵣₑᵥⁿ st'↦ᵐst₀' st'↦ᵐst′ st-is-nf
  ... | refl with st′↦ᵏ⁺¹st₀'
  ... | r ᵣₑᵥ ∷ rs = ⊥-elim (st₀-is-init (_ , r))

