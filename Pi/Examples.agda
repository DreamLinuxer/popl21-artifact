module Pi.Examples where
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Vec as V hiding (map)
open import Pi.Syntax
open import Pi.Opsem
open import Pi.Eval

pattern 𝔹 = 𝟙 +ᵤ 𝟙
pattern 𝔽 = inj₁ tt
pattern 𝕋 = inj₂ tt

𝔹^ : ℕ → 𝕌
𝔹^ 0 = 𝟙
𝔹^ 1 = 𝔹
𝔹^ (suc (suc n)) = 𝔹 ×ᵤ 𝔹^ (suc n)

-----------------------------------------------------------------------------
-- Adaptors 

[A+B]+C=[C+B]+A : ∀ {A B C} → (A +ᵤ B) +ᵤ C ↔ (C +ᵤ B) +ᵤ A
[A+B]+C=[C+B]+A = assocr₊ ⨾ (id↔ ⊕ swap₊) ⨾ swap₊

[A+B]+C=[A+C]+B : ∀ {A B C} → (A +ᵤ B) +ᵤ C ↔ (A +ᵤ C) +ᵤ B
[A+B]+C=[A+C]+B = assocr₊ ⨾ (id↔ ⊕ swap₊) ⨾ assocl₊

[A+B]+[C+D]=[A+C]+[B+D] : {A B C D : 𝕌} → (A +ᵤ B) +ᵤ (C +ᵤ D) ↔ (A +ᵤ C) +ᵤ (B +ᵤ D)
[A+B]+[C+D]=[A+C]+[B+D] =  assocl₊ ⨾ (assocr₊ ⊕ id↔) ⨾ ((id↔ ⊕ swap₊) ⊕ id↔) ⨾ (assocl₊ ⊕ id↔) ⨾ assocr₊

Ax[BxC]=Bx[AxC] : {A B C : 𝕌} → A ×ᵤ (B ×ᵤ C) ↔ B ×ᵤ (A ×ᵤ C)
Ax[BxC]=Bx[AxC] = assocl⋆ ⨾ (swap⋆ ⊗ id↔) ⨾  assocr⋆

[AxB]×C=[A×C]xB : ∀ {A B C} → (A ×ᵤ B) ×ᵤ C ↔ (A ×ᵤ C) ×ᵤ B
[AxB]×C=[A×C]xB = assocr⋆ ⨾ (id↔ ⊗ swap⋆) ⨾ assocl⋆

[A×B]×[C×D]=[A×C]×[B×D] : {A B C D : 𝕌} → (A ×ᵤ B) ×ᵤ (C ×ᵤ D) ↔ (A ×ᵤ C) ×ᵤ (B ×ᵤ D)
[A×B]×[C×D]=[A×C]×[B×D] = assocl⋆ ⨾ (assocr⋆ ⊗ id↔) ⨾ ((id↔ ⊗ swap⋆) ⊗ id↔) ⨾ (assocl⋆ ⊗ id↔) ⨾ assocr⋆

-- FST2LAST(b₁,b₂,…,bₙ) = (b₂,…,bₙ,b₁)
FST2LAST : ∀ {n} → 𝔹^ n ↔ 𝔹^ n
FST2LAST {0} = id↔
FST2LAST {1} = id↔
FST2LAST {2} = swap⋆
FST2LAST {suc (suc (suc n))} = Ax[BxC]=Bx[AxC] ⨾ (id↔ ⊗ FST2LAST)

FST2LAST⁻¹ : ∀ {n} → 𝔹^ n ↔ 𝔹^ n
FST2LAST⁻¹ = ! FST2LAST

-- NOT(b) = ¬b
NOT : 𝔹 ↔ 𝔹
NOT = swap₊

-- CNOT(b₁,b₂) = (b₁,b₁ xor b₂)
CNOT : 𝔹 ×ᵤ 𝔹 ↔ 𝔹 ×ᵤ 𝔹
CNOT = dist ⨾ (id↔ ⊕ (id↔ ⊗ swap₊)) ⨾ factor

-- CIF(c₁,c₂)(𝔽,a) = (𝔽,c₁ a)
-- CIF(c₁,c₂)(𝕋,a) = (𝕋,c₂ a)
CIF : {A : 𝕌} → (c₁ c₂ : A ↔ A) → 𝔹 ×ᵤ A ↔ 𝔹 ×ᵤ A
CIF c₁ c₂ = dist ⨾ ((id↔ ⊗ c₁) ⊕ (id↔ ⊗ c₂)) ⨾ factor

CIF₁ CIF₂ : {A : 𝕌} → (c : A ↔ A) → 𝔹 ×ᵤ A ↔ 𝔹 ×ᵤ A
CIF₁ c = CIF c id↔
CIF₂ c = CIF id↔ c

-- TOFFOLI(b₁,…,bₙ,b) = (b₁,…,bₙ,b xor (b₁ ∧ … ∧ bₙ))
TOFFOLI : {n : ℕ} → 𝔹^ n ↔ 𝔹^ n
TOFFOLI {0} = id↔
TOFFOLI {1} = swap₊
TOFFOLI {suc (suc n)} = CIF₂ TOFFOLI

-- TOFFOLI(b₁,…,bₙ,b) = (b₁,…,bₙ,b xor (¬b₁ ∧ … ∧ ¬bₙ))
TOFFOLI' : ∀ {n} → 𝔹^ n ↔ 𝔹^ n
TOFFOLI' {0} = id↔
TOFFOLI' {1} = swap₊
TOFFOLI' {suc (suc n)} = CIF₁ TOFFOLI'

-- RESET(b₁,…,bₙ) = (b₁ xor (b₁ ∨ … ∨ bₙ),…,bₙ)
RESET : ∀ {n} → 𝔹 ×ᵤ 𝔹^ n ↔ 𝔹 ×ᵤ 𝔹^ n
RESET {0} = id↔
RESET {1} = swap⋆ ⨾ CNOT ⨾ swap⋆
RESET {suc (suc n)} = Ax[BxC]=Bx[AxC] ⨾ CIF RESET (swap₊ ⊗ id↔) ⨾ Ax[BxC]=Bx[AxC]

-----------------------------------------------------------------------------
-- Reversible Copy
-- copy(𝔽,b₁,…,bₙ) = (b₁,b₁,…,bₙ)
COPY : ∀ {n} → 𝔹 ×ᵤ 𝔹^ n ↔ 𝔹 ×ᵤ 𝔹^ n
COPY {0} = id↔
COPY {1} = swap⋆ ⨾ CNOT ⨾ swap⋆
COPY {suc (suc n)} = assocl⋆ ⨾ (COPY {1} ⊗ id↔) ⨾ assocr⋆

-----------------------------------------------------------------------------
-- Arithmetic
-- INCR(b̅) = INCR(b̅ + 1)
INCR : ∀ {n} → 𝔹^ n ↔ 𝔹^ n
INCR {0} = id↔
INCR {1} = swap₊
INCR {suc (suc n)} = (id↔ ⊗ INCR) ⨾ FST2LAST ⨾ TOFFOLI' ⨾ FST2LAST⁻¹

iterate : (n : ℕ) → (𝔹^ n ↔ 𝔹^ n) → Vec ⟦ 𝔹^ n ⟧ (2 ^ n)
iterate n f = go initial
  where
    initial : ∀ {m} → ⟦ 𝔹^ m ⟧
    initial {zero} = tt
    initial {suc zero} = 𝔽
    initial {suc (suc m)} = 𝔽 , initial

    go : ∀ {m} → ⟦ 𝔹^ n ⟧ → Vec ⟦ 𝔹^ n ⟧ m 
    go {0} v = []
    go {suc m} v = let v' = eval f v
                   in  v ∷ go v'

INCRₜₑₛₜ = iterate 4 INCR
