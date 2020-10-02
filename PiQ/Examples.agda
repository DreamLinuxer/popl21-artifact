module PiQ.Examples where
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Sum
open import Data.Product
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import PiQ.Syntax
open import PiQ.Opsem
open import PiQ.Eval
open import PiQ.Interp

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

[A+B]+[C+D]=[A+C]+[B+D] : {A B C D : 𝕌} →
  (A +ᵤ B) +ᵤ (C +ᵤ D) ↔ (A +ᵤ C) +ᵤ (B +ᵤ D)
[A+B]+[C+D]=[A+C]+[B+D] = assocl₊ ⨾ (assocr₊ ⊕ id↔) ⨾ ((id↔ ⊕ swap₊) ⊕ id↔) ⨾ (assocl₊ ⊕ id↔) ⨾ assocr₊

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

-----------------------------------------------------------------------------
-- Reversible Conditionals

-- not(b) = ¬b
NOT : 𝔹 ↔ 𝔹
NOT = swap₊

-- cnot(b₁,b₂) = (b₁,b₁ xor b₂)
CNOT : 𝔹 ×ᵤ 𝔹 ↔ 𝔹 ×ᵤ 𝔹
CNOT = dist ⨾ (id↔ ⊕ (id↔ ⊗ swap₊)) ⨾ factor

-- CIF(c₁,c₂)(𝔽,a) = (𝔽,c₁ a)
-- CIF(c₁,c₂)(𝕋,a) = (𝕋,c₂ a)
CIF : {A : 𝕌} → (c₁ c₂ : A ↔ A) → 𝔹 ×ᵤ A ↔ 𝔹 ×ᵤ A
CIF c₁ c₂ = dist ⨾ ((id↔ ⊗ c₁) ⊕ (id↔ ⊗ c₂)) ⨾ factor

CIF₁ CIF₂ : {A : 𝕌} → (c : A ↔ A) → 𝔹 ×ᵤ A ↔ 𝔹 ×ᵤ A
CIF₁ c = CIF c id↔
CIF₂ c = CIF id↔ c

-- toffoli(b₁,…,bₙ,b) = (b₁,…,bₙ,b xor (b₁ ∧ … ∧ bₙ))
TOFFOLI : {n : ℕ} → 𝔹^ n ↔ 𝔹^ n
TOFFOLI {0} = id↔
TOFFOLI {1} = swap₊
TOFFOLI {suc (suc n)} = CIF₂ TOFFOLI

-- TOFFOLI(b₁,…,bₙ,b) = (b₁,…,bₙ,b xor (¬b₁ ∧ … ∧ ¬bₙ))
TOFFOLI' : ∀ {n} → 𝔹^ n ↔ 𝔹^ n
TOFFOLI' {0} = id↔
TOFFOLI' {1} = swap₊
TOFFOLI' {suc (suc n)} = CIF₁ TOFFOLI'

-- reset(b₁,b₂,…,bₙ) = (b₁ xor (b₂ ∨ … ∨ bₙ),b₂,…,bₙ)
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
-- incr(b̅) = incr(b̅ + 1)
INCR : ∀ {n} → 𝔹^ n ↔ 𝔹^ n
INCR {0} = id↔
INCR {1} = swap₊
INCR {suc (suc n)} = (id↔ ⊗ INCR) ⨾ FST2LAST ⨾ TOFFOLI' ⨾ FST2LAST⁻¹

-----------------------------------------------------------------------------
-- Iteration
trace₊ : ∀ {A B C} → A +ᵤ C ↔ B +ᵤ C → A ↔ B
trace₊ f = uniti₊r ⨾ (id↔ ⊕ η₊) ⨾ assocl₊ ⨾ (f ⊕ id↔) ⨾ assocr₊ ⨾ (id↔ ⊕ ε₊) ⨾ unite₊r

-----------------------------------------------------------------------------
-- Ancilla Management

trace⋆ : ∀ {A B C} → (c : ⟦ C ⟧) → A ×ᵤ C ↔ B ×ᵤ C → A ↔ B
trace⋆ c f = uniti⋆r ⨾ (id↔ ⊗ ηₓ c) ⨾ assocl⋆ ⨾
             (f ⊗ id↔) ⨾
             assocr⋆ ⨾ (id↔ ⊗ εₓ _) ⨾ unite⋆r

-----------------------------------------------------------------------------
-- Higher-Order Combinators

hof- : {A B : 𝕌} → (A ↔ B) → (𝟘 ↔ - A +ᵤ B)
hof- c = η₊ ⨾ (c ⊕ id↔) ⨾ swap₊

comp- : {A B C : 𝕌} → (- A +ᵤ B) +ᵤ (- B +ᵤ C) ↔ (- A +ᵤ C)
comp- = assocl₊ ⨾ (assocr₊ ⊕ id↔) ⨾ ((id↔ ⊕ ε₊) ⊕ id↔) ⨾ (unite₊r ⊕ id↔)

app- : {A B : 𝕌} → (- A +ᵤ B) +ᵤ A ↔ B
app- = swap₊ ⨾ assocl₊ ⨾ (ε₊ ⊕ id↔) ⨾ unite₊l 

curry- : {A B C : 𝕌} → (A +ᵤ B ↔ C) → (A ↔ - B +ᵤ C)
curry- c = uniti₊l ⨾ (η₊ ⊕ id↔) ⨾ swap₊ ⨾ assocl₊ ⨾ (c ⊕ id↔) ⨾ swap₊   

hof/ : {A B : 𝕌} → (A ↔ B) → (v : ⟦ A ⟧) → (𝟙 ↔ 𝟙/ v ×ᵤ B)
hof/ c v = ηₓ v ⨾ (c ⊗ id↔) ⨾ swap⋆

comp/ : {A B C : 𝕌} {v : ⟦ A ⟧} → (w : ⟦ B ⟧) → 
        (𝟙/ v ×ᵤ B) ×ᵤ (𝟙/ w ×ᵤ C) ↔ (𝟙/ v ×ᵤ C)
comp/ w = assocl⋆ ⨾ (assocr⋆ ⊗ id↔) ⨾ ((id↔ ⊗ εₓ w) ⊗ id↔) ⨾ (unite⋆r ⊗ id↔)

app/ : {A B : 𝕌} → (v : ⟦ A ⟧) → (𝟙/ v ×ᵤ B) ×ᵤ A ↔ B
app/ v = swap⋆ ⨾ assocl⋆ ⨾ (εₓ _ ⊗ id↔) ⨾ unite⋆l 

curry/ : {A B C : 𝕌} → (A ×ᵤ B ↔ C) → (v : ⟦ B ⟧) → (A ↔ 𝟙/ v ×ᵤ C)
curry/ c v = uniti⋆l ⨾ (ηₓ v ⊗ id↔) ⨾ swap⋆ ⨾ assocl⋆ ⨾ (c ⊗ id↔) ⨾ swap⋆

-----------------------------------------------------------------------------
-- Algebraic Identities

inv- : {A : 𝕌} → A ↔ - (- A)
inv- = uniti₊r ⨾ (id↔ ⊕ η₊) ⨾ assocl₊ ⨾ (ε₊ ⊕ id↔) ⨾ unite₊l

dist- : {A B : 𝕌} → - (A +ᵤ B) ↔ - A +ᵤ - B
dist- = 
  uniti₊l ⨾ (η₊ ⊕ id↔) ⨾ uniti₊l ⨾ (η₊ ⊕ id↔) ⨾ assocl₊ ⨾ 
  ([A+B]+[C+D]=[A+C]+[B+D] ⊕ id↔) ⨾ 
  (swap₊ ⊕ id↔) ⨾ assocr₊ ⨾ (id↔ ⊕ ε₊) ⨾ unite₊r

neg- : {A B : 𝕌} → (A ↔ B) →  (- A ↔ - B)
neg- c =
  uniti₊r ⨾ (id↔ ⊕ η₊) ⨾
  (id↔ ⊕ ! c ⊕ id↔) ⨾ assocl₊ ⨾
  ((swap₊ ⨾ ε₊) ⊕ id↔) ⨾ unite₊l

inv/ : {A : 𝕌} {v : ⟦ A ⟧} → A ↔ (𝟙/_ {𝟙/ v} ↻)
inv/ = uniti⋆r ⨾ (id↔ ⊗ ηₓ _) ⨾ assocl⋆ ⨾ (εₓ _ ⊗ id↔) ⨾ unite⋆l

dist/ : {A B : 𝕌} {a : ⟦ A ⟧} {b : ⟦ B ⟧} → 𝟙/ (a , b) ↔ 𝟙/ a ×ᵤ 𝟙/ b
dist/ {A} {B} {a} {b} = 
  uniti⋆l ⨾ (ηₓ b ⊗ id↔) ⨾ uniti⋆l ⨾ (ηₓ a ⊗ id↔) ⨾ assocl⋆ ⨾ 
  ([A×B]×[C×D]=[A×C]×[B×D] ⊗ id↔) ⨾ 
  (swap⋆ ⊗ id↔) ⨾ assocr⋆ ⨾ (id↔ ⊗ εₓ (a , b)) ⨾ unite⋆r

neg/ : {A B : 𝕌} {a : ⟦ A ⟧} {b : ⟦ B ⟧} → (A ↔ B) → (𝟙/ a ↔ 𝟙/ b)
neg/ {A} {B} {a} {b} c =
  uniti⋆r ⨾ (id↔ ⊗ ηₓ _) ⨾
  (id↔ ⊗ ! c ⊗ id↔) ⨾ assocl⋆ ⨾
  ((swap⋆ ⨾ εₓ _) ⊗ id↔) ⨾ unite⋆l

dist×- : {A B : 𝕌} → (- A) ×ᵤ B ↔ - (A ×ᵤ B)
dist×- =
  uniti₊r ⨾ (id↔ ⊕ η₊) ⨾ assocl₊ ⨾
  ((factor ⨾ ((swap₊ ⨾ ε₊) ⊗ id↔) ⨾ absorbr) ⊕ id↔) ⨾
  unite₊l

neg× : {A B : 𝕌} → A ×ᵤ B ↔ (- A) ×ᵤ (- B)
neg× = inv- ⨾ neg- (! dist×- ⨾ swap⋆) ⨾ ! dist×- ⨾ swap⋆

fracDist : ∀ {A B} {a : ⟦ A ⟧} {b : ⟦ B ⟧} → 𝟙/ a ×ᵤ 𝟙/ b ↔ 𝟙/ (a , b)
fracDist =
  uniti⋆l ⨾ ((ηₓ _ ⨾ swap⋆) ⊗ id↔) ⨾ assocr⋆ ⨾ 
  (id↔ ⊗ ([A×B]×[C×D]=[A×C]×[B×D] ⨾ (εₓ _ ⊗ εₓ _) ⨾ unite⋆l)) ⨾ unite⋆r

mulFrac : ∀ {A B C D} {b : ⟦ B ⟧} {d : ⟦ D ⟧}
        → (A ×ᵤ 𝟙/ b) ×ᵤ (C ×ᵤ 𝟙/ d) ↔ (A ×ᵤ C) ×ᵤ (𝟙/ (b , d))
mulFrac = [A×B]×[C×D]=[A×C]×[B×D] ⨾ (id↔ ⊗ fracDist)

addFracCom : ∀ {A B C} {v : ⟦ C ⟧} 
        → (A ×ᵤ 𝟙/ v) +ᵤ (B ×ᵤ 𝟙/ v) ↔ (A +ᵤ B) ×ᵤ (𝟙/ v)
addFracCom = factor

addFrac : ∀ {A B C D} → (v : ⟦ C ⟧) → (w : ⟦ D ⟧) 
        → (A ×ᵤ 𝟙/_ {C} v) +ᵤ (B ×ᵤ 𝟙/_ {D} w) ↔ 
         ((A ×ᵤ D) +ᵤ (C ×ᵤ B)) ×ᵤ (𝟙/_ {C ×ᵤ D} (v , w))
addFrac v w = ((uniti⋆r ⨾ (id↔ ⊗ ηₓ w)) ⊕ (uniti⋆l  ⨾ (ηₓ v ⊗ id↔))) ⨾
              [A×B]×[C×D]=[A×C]×[B×D] ⊕ [A×B]×[C×D]=[A×C]×[B×D] ⨾
              ((id↔ ⊗ fracDist) ⊕ (id↔ ⊗ fracDist)) ⨾ factor

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
