module TimeSpace where
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Pi.Syntax
open import Pi.Opsem
open import Pi.Eval
open import Pi.Examples

-- 𝔹+ n = 𝔹 +ᵤ … +ᵤ 𝔹
𝔹+ : ℕ → 𝕌
𝔹+ 0 = 𝟘
𝔹+ 1 = 𝔹
𝔹+ (suc (suc n)) = 𝔹 +ᵤ (𝔹+ (suc n))

-- 𝔹* n = 𝔹 ×ᵤ … ×ᵤ 𝔹
𝔹* : ℕ → 𝕌
𝔹* 0 = 𝔹
𝔹* (suc n) = 𝔹 ×ᵤ 𝔹* n

convert : ∀ {n} → 𝔹+ (2 ^ n) ↔ 𝔹* n
convert {0} = id↔
convert {1} = (uniti⋆l ⊕ uniti⋆l) ⨾ factor
convert {suc (suc n)} = split ⨾ (convert {suc n} ⊕ (coe {n} ⨾ convert {suc n})) ⨾ (uniti⋆l ⊕ uniti⋆l) ⨾ factor
  where
  coe : ∀ {n} → 𝔹+ ((2 ^ n) + ((2 ^ n) + 0) + 0) ↔ 𝔹+ (2 ^ (1 + n))
  coe {n} rewrite +-identityʳ ((2 ^ n) + ((2 ^ n) + 0)) = id↔
    
  split : ∀ {n m} → 𝔹+ (n + m) ↔ (𝔹+ n +ᵤ 𝔹+ m)
  split {0} {m} = uniti₊l
  split {1} {0} = uniti₊r
  split {1} {1} = id↔
  split {1} {suc (suc m)} = id↔
  split {suc (suc n)} {m} = (id↔ ⊕ split) ⨾ assocl₊

-- flip the last 𝔹
flip+ : (n : ℕ) → 𝔹+ n ↔ 𝔹+ n
flip+ 0 = id↔
flip+ 1 = swap₊
flip+ (suc (suc n)) = id↔ ⊕ flip+ (suc n)

-- flip* n (b₁,…,bₙ,b) = (b₁,…,bₙ,b xor (b₁ ∧ … ∧ bₙ)) 
flip* : (n : ℕ) → (𝔹* n) ↔ (𝔹* n)
flip* 0 = swap₊
flip* (suc n) = dist ⨾ (id↔ ⊕ (id↔ ⊗ flip* n)) ⨾ factor

v* : (n : ℕ) → ⟦ 𝔹* n ⟧
v* 0 = 𝔽
v* 1 = 𝕋 , v* 0
v* (suc (suc n)) = 𝕋 , v* (suc n)

v+ : (n : ℕ) → n ≢ 0 → ⟦ 𝔹+ n ⟧
v+ 0 0≠0 = 0≠0 refl
v+ 1 _ = 𝔽
v+ (suc (suc n)) _ = inj₂ (v+ (suc n) (λ ()))

-- Counting number of values in given context
#ctx : ∀ {A B} → Context {A} {B} → ℕ
#ctx ☐ = 0
#ctx (☐⨾ c₂ • κ) = #ctx κ
#ctx (c₁ ⨾☐• κ) = #ctx κ
#ctx (☐⊕ c₂ • κ) = #ctx κ
#ctx (c₁ ⊕☐• κ) = #ctx κ
#ctx (☐⊗[ c₂ , x ]• κ) = 1 + #ctx κ
#ctx ([ c₁ , x ]⊗☐• κ) = 1 + #ctx κ

#st : State → ℕ
#st ⟨ c ∣ v ∣ κ ⟩ = 1 + #ctx κ
#st ［ c ∣ v ∣ κ ］ = 1 + #ctx κ

-- Returns the number of steps and maximum #st in a execution trace
runST : ∀ {A B} → A ↔ B → ⟦ A ⟧ → List State × ℕ × ℕ
runST c v = states , length states , foldl (λ { s st → s ⊔ #st st }) 0 states
  where states = evalₜᵣ c v

-- Examples
ex1 : ℕ × ℕ
ex1 = let(_ , t , s) = runST (flip* 9) (v* 9)
      in (t , s)  -- t=128 , s=10

ex2 : ℕ × ℕ
ex2 = let (_ , t , s) = runST (flip+ 512) (v+ 512 (λ ()))
      in  (t , s) -- t=1024 , s=1
