module Pi-.Examples where
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
open import Data.List as L
open import Function using (_∘_)
open import Pi-.Syntax
open import Pi-.Opsem
open import Pi-.Eval

-----------------------------------------------------------------------------
-- Patterns and data definitions

pattern 𝔹 = 𝟙 +ᵤ 𝟙
pattern 𝔽 = inj₁ tt
pattern 𝕋 = inj₂ tt

𝔹+ : ℕ → 𝕌
𝔹+ 0 = 𝟘
𝔹+ 1 = 𝔹
𝔹+ (suc (suc n)) = 𝔹 +ᵤ (𝔹+ (suc n))

𝔹^ : ℕ → 𝕌
𝔹^ 0 = 𝟙
𝔹^ 1 = 𝔹
𝔹^ (suc (suc n)) = 𝔹 ×ᵤ 𝔹^ (suc n)

𝔹* : ℕ → 𝕌
𝔹* n = 𝔹^ (1 + n)

𝔽^ : (n : ℕ) → ⟦ 𝔹^ n ⟧
𝔽^ 0 = tt
𝔽^ 1 = 𝔽
𝔽^ (suc (suc n)) = 𝔽 , 𝔽^ (suc n)

-----------------------------------------------------------------------------
-- Adaptors 

[A+B]+C=[C+B]+A : ∀ {A B C} → (A +ᵤ B) +ᵤ C ↔ (C +ᵤ B) +ᵤ A
[A+B]+C=[C+B]+A = assocr₊ ⨾ (id↔ ⊕ swap₊) ⨾ swap₊

[A+B]+C=[A+C]+B : ∀ {A B C} → (A +ᵤ B) +ᵤ C ↔ (A +ᵤ C) +ᵤ B
[A+B]+C=[A+C]+B = assocr₊ ⨾ (id↔ ⊕ swap₊) ⨾ assocl₊

[A+B]+[C+D]=[A+C]+[B+D] : {A B C D : 𝕌} → (A +ᵤ B) +ᵤ (C +ᵤ D) ↔ (A +ᵤ C) +ᵤ (B +ᵤ D)
[A+B]+[C+D]=[A+C]+[B+D] = assocl₊ ⨾ (assocr₊ ⊕ id↔) ⨾ ((id↔ ⊕ swap₊) ⊕ id↔) ⨾ (assocl₊ ⊕ id↔) ⨾ assocr₊

Ax[BxC]=Bx[AxC] : {A B C : 𝕌} → A ×ᵤ (B ×ᵤ C) ↔ B ×ᵤ (A ×ᵤ C)
Ax[BxC]=Bx[AxC] = assocl⋆ ⨾ (swap⋆ ⊗ id↔) ⨾  assocr⋆

[AxB]×C=[A×C]xB : ∀ {A B C} → (A ×ᵤ B) ×ᵤ C ↔ (A ×ᵤ C) ×ᵤ B
[AxB]×C=[A×C]xB = assocr⋆ ⨾ (id↔ ⊗ swap⋆) ⨾ assocl⋆

[A×B]×[C×D]=[A×C]×[B×D] : {A B C D : 𝕌} →
  (A ×ᵤ B) ×ᵤ (C ×ᵤ D) ↔ (A ×ᵤ C) ×ᵤ (B ×ᵤ D)
[A×B]×[C×D]=[A×C]×[B×D] = assocl⋆ ⨾ (assocr⋆ ⊗ id↔) ⨾ ((id↔ ⊗ swap⋆) ⊗ id↔) ⨾ (assocl⋆ ⊗ id↔) ⨾ assocr⋆

-- FST2LAST(b₁,b₂,…,bₙ) = (b₂,…,bₙ,b₁)
FST2LAST : ∀ {n} → 𝔹^ n ↔ 𝔹^ n
FST2LAST {0} = id↔
FST2LAST {1} = id↔
FST2LAST {2} = swap⋆
FST2LAST {suc (suc (suc n))} = Ax[BxC]=Bx[AxC] ⨾ (id↔ ⊗ FST2LAST)

FST2LAST⁻¹ : ∀ {n} → 𝔹^ n ↔ 𝔹^ n
FST2LAST⁻¹ = ! FST2LAST

-----------------------------------------------------------------------------
-- Reversible Conditionals

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

-----------------------------------------------------------------------------
-- Control flow
zigzag : 𝔹 ↔ 𝔹
zigzag = uniti₊l ⨾ (η₊ ⊕ id↔) ⨾ [A+B]+C=[C+B]+A ⨾ (ε₊ ⊕ id↔) ⨾ unite₊l
zigzagₜᵣ = evalₜᵣ zigzag 𝔽

-----------------------------------------------------------------------------
-- Iteration

trace₊ : ∀ {A B C} → A +ᵤ C ↔ B +ᵤ C → A ↔ B
trace₊ f = uniti₊r ⨾ (id↔ ⊕ η₊) ⨾ assocl₊ ⨾ (f ⊕ id↔) ⨾ assocr₊ ⨾ (id↔ ⊕ ε₊) ⨾ unite₊r

-- Given reversible F : 𝔹^n ↔ 𝔹^n, generate a circuit to find x̅ such that F(x̅) = (𝔽,…)
-- via running (LOOP F)(𝔽,𝔽̅).
-- (id↔ ⊗ F)((LOOP F)(𝔽,𝔽̅)) = (𝔽,𝔽,…)
LOOP : ∀ {n} → 𝔹^ n ↔ 𝔹^ n → 𝔹 ×ᵤ 𝔹^ n ↔ 𝔹 ×ᵤ 𝔹^ n
LOOP {0} F = id↔
LOOP {1} F = id↔ ⊗ F
LOOP {suc (suc n)} F = trace₊ ((dist ⊕ id↔) ⨾ [A+B]+C=[A+C]+B ⨾ (factor ⊕ id↔) ⨾
                               ((RESET ⨾ (id↔ ⊗ F) ⨾ COPY ⨾ (id↔ ⊗ ! F)) ⊕ id↔) ⨾
                               (dist ⊕ id↔) ⨾ [A+B]+C=[A+C]+B ⨾ (factor ⊕ (id↔ ⊗ INCR)))


module loop_test where
  -- Examples
  -- AND(𝔽,a,b) = AND(a∧b,a,b)
  AND : 𝔹^ 3 ↔ 𝔹^ 3
  AND = FST2LAST ⨾ (dist ⨾ (id↔ ⊕ (id↔ ⊗ (dist ⨾ (id↔ ⊕ (id↔ ⊗ swap₊)) ⨾ factor))) ⨾ factor) ⨾ FST2LAST⁻¹

  NAND : 𝔹^ 3 ↔ 𝔹^ 3
  NAND = AND ⨾ (NOT ⊗ id↔)

  -- OR(𝔽,a,b) = OR(a∨b,a,b)
  OR : 𝔹^ 3 ↔ 𝔹^ 3
  OR = FST2LAST ⨾ (dist ⨾ ((id↔ ⊗ (dist ⨾ (id↔ ⊕ (id↔ ⊗ swap₊)) ⨾ factor)) ⊕ (id↔ ⊗ (id↔ ⊗ swap₊))) ⨾ factor) ⨾ FST2LAST⁻¹

  NOR : 𝔹^ 3 ↔ 𝔹^ 3
  NOR = OR ⨾ (NOT ⊗ id↔)

  -- XOR(a,b) = XOR(a xor b,b)
  XOR : 𝔹^ 2 ↔ 𝔹^ 2
  XOR = distl ⨾ (id↔ ⊕ (swap₊ ⊗ id↔)) ⨾ factorl

  tests : List (∃[ n ] (𝔹^ n ↔ 𝔹^ n))
  tests = (_ , LOOP AND) ∷ (_ , LOOP NAND) ∷ (_ , LOOP OR) ∷ (_ , LOOP NOR) ∷ (_ , LOOP XOR) ∷ []

  results : List (Σ[ t ∈ 𝕌 ] ⟦ t ⟧)
  results = L.map (λ {(_ , c) → proj₁ (eval' c (𝔽^ _))}) tests
  -- (_ , 𝔽 , 𝔽 , 𝔽 , 𝔽) ∷
  -- (_ , 𝔽 , 𝔽 , 𝕋 , 𝕋) ∷
  -- (_ , 𝔽 , 𝔽 , 𝔽 , 𝔽) ∷
  -- (_ , 𝔽 , 𝔽 , 𝔽 , 𝕋) ∷
  -- (_ , 𝔽 , 𝔽 , 𝔽) ∷ []

-----------------------------------------------------------------------------
-- Data Structures Conversions

convert : ∀ {n} → 𝔹+ (2 ^ n) ↔ 𝔹* n
convert {0} = id↔
convert {1} = (uniti⋆l ⊕ uniti⋆l) ⨾ factor
convert {suc (suc n)} =
  split ⨾ 
  (convert {suc n} ⊕ (coe {n} ⨾ convert {suc n})) ⨾
  (uniti⋆l ⊕ uniti⋆l) ⨾ 
  factor

  where

    coe : ∀ {n} → 𝔹+ ((2 ^ n) + ((2 ^ n) + 0) + 0) ↔ 𝔹+ (2 ^ (1 + n))
    coe {n} rewrite +-identityʳ ((2 ^ n) + ((2 ^ n) + 0)) = id↔
    
    split : ∀ {n m} → 𝔹+ (n + m) ↔ (𝔹+ n +ᵤ 𝔹+ m)
    split {0} {m} = uniti₊l
    split {1} {0} = uniti₊r
    split {1} {1} = id↔
    split {1} {suc (suc m)} = id↔
    split {suc (suc n)} {m} = (id↔ ⊕ split) ⨾ assocl₊

1023→2¹⁰-1 : 𝔹+ 1023 ↔ (- 𝔹 +ᵤ 𝔹* 10)
1023→2¹⁰-1 =
  uniti₊l ⨾
  ((η₊ ⨾ swap₊) ⊕ id↔) ⨾
  assocr₊ ⨾ 
  (id↔ ⊕ convert {10})

2047→2¹¹-1 : 𝔹+ 2047 ↔ (- 𝔹 +ᵤ 𝔹* 11)
2047→2¹¹-1 =
  uniti₊l ⨾
  ((η₊ ⨾ swap₊) ⊕ id↔) ⨾ 
  assocr₊ ⨾ 
  (id↔ ⊕ convert {11})

incr* : 𝔹* 11 ↔ 𝔹* 11
incr* = apply1023 {11} INCR
  where
    apply1023 : ∀ {n} → (𝔹 ↔ 𝔹) → 𝔹* n ↔ 𝔹* n
    apply1023 {0} c = id↔
    apply1023 {1} c = CIF₂ c
    apply1023 {suc (suc n)} c = CIF₂ (apply1023 c)

incr+ : 𝔹+ 2047 ↔ 𝔹+ 2047
incr+ = applyLast₊ {2047} INCR
  where
    applyLast₊ : ∀ {n} → (𝔹 ↔ 𝔹) → 𝔹+ n ↔ 𝔹+ n
    applyLast₊ {0} c = id↔
    applyLast₊ {1} c = c
    applyLast₊ {suc (suc n)} c = id↔ ⊕ applyLast₊ c

incr+' : 𝔹+ 2047 ↔ 𝔹+ 2047
incr+' = 2047→2¹¹-1 ⨾ (id↔ ⊕ incr*) ⨾ ! 2047→2¹¹-1

v : (n : ℕ) → ¬ n ≡ 0 → ⟦ 𝔹+ n ⟧
v 0 0≠0 = 0≠0 refl
v 1 _ = 𝔽 
v (suc (suc n)) _ = inj₂ (v (suc n) (λ ()))

len1 len2 : ℕ
len1 = proj₂ (eval' incr+  (v 2047 (λ ())))   -- 4093
len2 = proj₂ (eval' incr+' (v 2047 (λ ())))   -- 25041
len3 = proj₂ (eval' 2047→2¹¹-1 (v 2047 (λ ()))) -- 12439
v' = (proj₂ ∘ proj₁) (eval' 2047→2¹¹-1 (v 2047 (λ ())))
len4 = proj₂ (eval' (id↔ ⊕ incr*) v') -- 157
v'' = (proj₂ ∘ proj₁) (eval' (id↔ ⊕ incr*) v')
len5 = proj₂ (eval' (! 2047→2¹¹-1) v'') -- 12439

-----------------------------------------------------------------------------
-- Higher-Order Combinators
hof- : {A B : 𝕌} → (A ↔ B) → (𝟘 ↔ - A +ᵤ B)
hof- c = η₊ ⨾ (c ⊕ id↔) ⨾ swap₊

comp- : {A B C : 𝕌} → (- A +ᵤ B) +ᵤ (- B +ᵤ C) ↔ (- A +ᵤ C)
comp- = assocl₊ ⨾ (assocr₊ ⊕ id↔) ⨾ ((id↔ ⊕ ε₊) ⊕ id↔) ⨾ (unite₊r ⊕ id↔)

app- : {A B : 𝕌} → (- A +ᵤ B) +ᵤ A ↔ B
app- = swap₊ ⨾ assocl₊ ⨾ (ε₊ ⊕ id↔) ⨾ unite₊l 


-----------------------------------------------------------------------------
-- Algebraic Identities

inv- : {A : 𝕌} → A ↔ - (- A)
inv- = uniti₊r ⨾ (id↔ ⊕ η₊) ⨾ assocl₊ ⨾ (ε₊ ⊕ id↔) ⨾ unite₊l

dist- : {A B : 𝕌} → - (A +ᵤ B) ↔ - A +ᵤ - B
dist- = uniti₊l ⨾ (η₊ ⊕ id↔) ⨾ uniti₊l ⨾ (η₊ ⊕ id↔) ⨾ assocl₊ ⨾ 
        ([A+B]+[C+D]=[A+C]+[B+D] ⊕ id↔) ⨾ 
        (swap₊ ⊕ id↔) ⨾ assocr₊ ⨾ (id↔ ⊕ ε₊) ⨾ unite₊r

neg- : {A B : 𝕌} → (A ↔ B) →  (- A ↔ - B)
neg- c = uniti₊r ⨾ (id↔ ⊕ η₊) ⨾
         (id↔ ⊕ ! c ⊕ id↔) ⨾ assocl₊ ⨾
         ((swap₊ ⨾ ε₊) ⊕ id↔) ⨾ unite₊l

