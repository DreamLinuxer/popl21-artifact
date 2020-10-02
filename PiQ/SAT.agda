module PiQ.SAT where
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Nat
open import Data.Nat.Properties
open import Data.List as L
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import PiQ.Syntax
open import PiQ.Eval
open import PiQ.Examples

-- Given reversible F : 𝔹^n ↔ 𝔹^n, generate a circuit to find x̅ such that F(x̅) = (𝔽,…)
-- via running (LOOP F)(𝔽,𝔽̅).
-- (id↔ ⊗ F)((LOOP F)(𝔽,𝔽̅)) = (𝔽,𝔽,…)
LOOP : ∀ {n} → 𝔹^ n ↔ 𝔹^ n → 𝔹 ×ᵤ 𝔹^ n ↔ 𝔹 ×ᵤ 𝔹^ n
LOOP {0} F = id↔
LOOP {1} F = id↔ ⊗ F
LOOP {suc (suc n)} F = trace₊ ((dist ⊕ id↔) ⨾ [A+B]+C=[A+C]+B ⨾ (factor ⊕ id↔) ⨾
                               ((RESET ⨾ (id↔ ⊗ F) ⨾ COPY ⨾ (id↔ ⊗ ! F)) ⊕ id↔) ⨾
                               (dist ⊕ id↔) ⨾ [A+B]+C=[A+C]+B ⨾ (factor ⊕ (id↔ ⊗ INCR)))

MERGE : (n m : ℕ) → 𝔹^ n ×ᵤ 𝔹^ m ↔ 𝔹^ (n + m)
MERGE 0 m = unite⋆l
MERGE 1 0 = unite⋆r
MERGE 1 (suc m) = id↔
MERGE (suc (suc n)) m = assocr⋆ ⨾ (id↔ ⊗ MERGE (suc n) m)

SPLIT : (n m : ℕ) → 𝔹^ (n + m) ↔ 𝔹^ n ×ᵤ 𝔹^ m 
SPLIT n m = ! MERGE n m

~_ : ∀ {n} → 𝔹^ (1 + n) ↔ 𝔹^ (1 + n) → 𝔹^ (1 + n) ↔ 𝔹^ (1 + n)
~_ {zero} F = F
~_ {suc n} F = F ⨾ NOT ⊗ id↔

-- Given a function G : 𝔹^n → 𝔹 there exists a reversible Gʳ : 𝔹^(1+n) ↔ 𝔹^(1+n) such that Gʳ(𝔽,xⁿ) = (F(xⁿ),…)
-- SAT(Gʳ) = tt iff ∃ xⁿ . G(xⁿ) = 𝕋
SAT : ∀ {n} → 𝔹^ (1 + n) ↔ 𝔹^ (1 + n) → 𝟙 ↔ 𝟙
SAT {n} Gʳ = trace⋆ (𝔽^ (3 + n)) (id↔ ⊗ ((id↔ ⊗ (LOOP (~ Gʳ) ⨾ (id↔ ⊗ SPLIT 1 n))) ⨾
                                         (id↔ ⊗ (assocl⋆ ⨾ (COPY ⊗ id↔) ⨾ assocr⋆)) ⨾
                                         assocl⋆ ⨾ (swap⋆ ⊗ id↔) ⨾ assocr⋆ ⨾
                                         (id↔ ⊗ ((id↔ ⊗ MERGE 1 n) ⨾ LOOP⁻¹ (~ Gʳ)))))
    where
    LOOP⁻¹ : ∀ {n} → 𝔹^ n ↔ 𝔹^ n → 𝔹 ×ᵤ 𝔹^ n ↔ 𝔹 ×ᵤ 𝔹^ n
    LOOP⁻¹ F = ! (LOOP F)

module SAT_test where
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

  tests : List ⟦ 𝔹^ 3 ⟧
  tests = (𝔽 , 𝔽 , 𝔽) ∷ (𝔽 , 𝔽 , 𝕋) ∷ (𝔽 , 𝕋 , 𝔽) ∷ (𝔽 , 𝕋 , 𝕋) ∷ (𝕋 , 𝔽 , 𝔽) ∷ (𝕋 , 𝔽 , 𝕋) ∷ (𝕋 , 𝕋 , 𝔽) ∷ (𝕋 , 𝕋 , 𝕋) ∷ []
  
  -- Ex₁(𝔽,a,b) = ((a∧b) xor (a∧b),_,_)
  -- ¬∃a,b . Ex₁(𝔽,a,b) = (𝕋,…)
  Ex₁ : 𝔹^ 3 ↔ 𝔹^ 3
  Ex₁ = trace⋆ (𝔽^ 1) (swap⋆ ⨾
                       (id↔ ⊗ AND) ⨾
                       assocl⋆ ⨾ (swap⋆ ⊗ id↔) ⨾ assocr⋆ ⨾
                       (id↔ ⊗ AND) ⨾
                       assocl⋆ ⨾ (XOR ⊗ id↔) ⨾ assocr⋆ ⨾
                       (id↔ ⊗ ! AND) ⨾
                       assocl⋆ ⨾ (swap⋆ ⊗ id↔) ⨾ assocr⋆ ⨾
                       swap⋆ )
  tests₁ = L.map (eval' Ex₁) tests

  -- Ex₂(𝔽,a,b) = ((a∧b) xor (a∨b),_,_)
  -- ∃a,b . Ex₂(𝔽,a,b) = (𝕋,…)
  Ex₂ : 𝔹^ 3 ↔ 𝔹^ 3
  Ex₂ = trace⋆ (𝔽^ 1) (swap⋆ ⨾
                       (id↔ ⊗ AND) ⨾
                       assocl⋆ ⨾ (swap⋆ ⊗ id↔) ⨾ assocr⋆ ⨾
                       (id↔ ⊗ OR) ⨾
                       assocl⋆ ⨾ (XOR ⊗ id↔) ⨾ assocr⋆ ⨾
                       (id↔ ⊗ ! OR) ⨾
                       assocl⋆ ⨾ (swap⋆ ⊗ id↔) ⨾ assocr⋆ ⨾
                       swap⋆ )
  tests₂ = L.map (eval' Ex₂) tests

  -- Ex₃(𝔽,a,b) = (((a∧b) ∧ (a xor b)),_,_)
  -- ¬∃a,b . Ex₃(𝔽,a,b) = (𝕋,…)
  Ex₃ : 𝔹^ 3 ↔ 𝔹^ 3
  Ex₃ = trace⋆ (𝔽^ 1) (swap⋆ ⨾
                       assocl⋆ ⨾ (swap⋆ ⊗ id↔) ⨾ assocr⋆ ⨾
                       id↔ ⊗ F ⨾
                       (id↔ ⊗ assocl⋆) ⨾ assocl⋆ ⨾
                       (AND ⊗ id↔) ⨾
                       assocr⋆ ⨾ (id↔ ⊗ assocr⋆) ⨾
                       id↔ ⊗ ! F ⨾
                       assocl⋆ ⨾ (swap⋆ ⊗ id↔) ⨾ assocr⋆ ⨾
                       swap⋆)
     where
     F : 𝔹^ 3 ↔ 𝔹^ 3
     F = AND ⨾ (id↔ ⊗ XOR)
  tests₃ = L.map (eval' Ex₃) tests

  -- Ex₄(𝔽,a,b) = (((a∨b) ∧ (a xor b)),_,_)
  -- ∃a,b . Ex₄(𝔽,a,b) = (𝕋,…)
  Ex₄ : 𝔹^ 3 ↔ 𝔹^ 3
  Ex₄ = trace⋆ (𝔽^ 1) (swap⋆ ⨾
                       assocl⋆ ⨾ (swap⋆ ⊗ id↔) ⨾ assocr⋆ ⨾
                       id↔ ⊗ F ⨾
                       (id↔ ⊗ assocl⋆) ⨾ assocl⋆ ⨾
                       (AND ⊗ id↔) ⨾
                       assocr⋆ ⨾ (id↔ ⊗ assocr⋆) ⨾
                       id↔ ⊗ ! F ⨾
                       assocl⋆ ⨾ (swap⋆ ⊗ id↔) ⨾ assocr⋆ ⨾
                       swap⋆)
     where
     F : 𝔹^ 3 ↔ 𝔹^ 3
     F = OR ⨾ (id↔ ⊗ XOR)
  tests₄ = L.map (eval' Ex₄) tests

  SAT-tests : List (𝟙 ↔ 𝟙)
  SAT-tests = (SAT AND) ∷ (SAT OR) ∷ (SAT XOR) ∷ (SAT Ex₁) ∷ (SAT Ex₂) ∷ (SAT Ex₃) ∷ (SAT Ex₄) ∷ []

  results : List (Maybe (Σ[ t ∈ 𝕌 ] ⟦ t ⟧) × ℕ)
  results = L.map (λ c → eval' c tt) SAT-tests
  -- (just (𝟙 , tt) , 3923) ∷
  -- (just (𝟙 , tt) , 2035) ∷
  -- (just (𝟙 , tt) , 1347) ∷
  -- (nothing , 10386) ∷
  -- (just (𝟙 , tt) , 4307) ∷
  -- (nothing , 11442) ∷
  -- (just (𝟙 , tt) , 4827) ∷ []
