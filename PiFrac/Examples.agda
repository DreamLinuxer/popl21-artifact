module PiFrac.Examples where
open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Sum
open import Data.Product
open import Data.Nat
open import Relation.Binary.Core
open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Maybe

open import PiFrac.Syntax
open import PiFrac.Opsem
open import PiFrac.Eval

-----------------------------------------------------------------------------
-- Patterns and data definitions

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
[A+B]+[C+D]=[A+C]+[B+D] = assocl₊ ⨾ (assocr₊ ⊕ id↔) ⨾ ((id↔ ⊕ swap₊) ⊕ id↔) ⨾ (assocl₊ ⊕ id↔) ⨾ assocr₊

Ax[BxC]=Bx[AxC] : {A B C : 𝕌} → A ×ᵤ (B ×ᵤ C) ↔ B ×ᵤ (A ×ᵤ C)
Ax[BxC]=Bx[AxC] = assocl⋆ ⨾ (swap⋆ ⊗ id↔) ⨾  assocr⋆

[AxB]×C=[A×C]xB : ∀ {A B C} → (A ×ᵤ B) ×ᵤ C ↔ (A ×ᵤ C) ×ᵤ B
[AxB]×C=[A×C]xB = assocr⋆ ⨾ (id↔ ⊗ swap⋆) ⨾ assocl⋆

[A×B]×[C×D]=[A×C]×[B×D] : {A B C D : 𝕌} → (A ×ᵤ B) ×ᵤ (C ×ᵤ D) ↔ (A ×ᵤ C) ×ᵤ (B ×ᵤ D)
[A×B]×[C×D]=[A×C]×[B×D] = assocl⋆ ⨾ (assocr⋆ ⊗ id↔) ⨾ ((id↔ ⊗ swap⋆) ⊗ id↔) ⨾ (assocl⋆ ⊗ id↔) ⨾ assocr⋆

-- CNOT(b₁,b₂) = (b₁,b₁ xor b₂)
CNOT : 𝔹 ×ᵤ 𝔹 ↔ 𝔹 ×ᵤ 𝔹
CNOT = dist ⨾ (id↔ ⊕ (id↔ ⊗ swap₊)) ⨾ factor

-- Trace
trace⋆ : ∀ {A B C} → (c : ⟦ C ⟧) → A ×ᵤ C ↔ B ×ᵤ C → A ↔ B
trace⋆ c f = uniti⋆r ⨾ (id↔ ⊗ ηₓ c) ⨾ assocl⋆ ⨾
             (f ⊗ id↔) ⨾
             assocr⋆ ⨾ (id↔ ⊗ εₓ _) ⨾ unite⋆r

ex1 ex2 : Maybe ⟦ 𝟙 +ᵤ 𝟙 ⟧
ex1 = eval (trace⋆ (inj₁ tt) swap⋆) (inj₁ tt) -- just (inj₁ tt)
ex2 = eval (trace⋆ (inj₁ tt) swap⋆) (inj₂ tt) -- nothing

-----------------------------------------------------------------------------
-- Higher-Order Combinators
hof/ : {A B : 𝕌} → (A ↔ B) → (v : ⟦ A ⟧) → (𝟙 ↔ 𝟙/ v ×ᵤ B)
hof/ c v = ηₓ v ⨾ (c ⊗ id↔) ⨾ swap⋆

comp/ : {A B C : 𝕌} {v : ⟦ A ⟧} → (w : ⟦ B ⟧) → 
        (𝟙/ v ×ᵤ B) ×ᵤ (𝟙/ w ×ᵤ C) ↔ (𝟙/ v ×ᵤ C)
comp/ w = assocl⋆ ⨾ (assocr⋆ ⊗ id↔) ⨾ ((id↔ ⊗ εₓ w) ⊗ id↔) ⨾ (unite⋆r ⊗ id↔)

app/ : {A B : 𝕌} → (v : ⟦ A ⟧) → (𝟙/ v ×ᵤ B) ×ᵤ A ↔ B
app/ v = swap⋆ ⨾ assocl⋆ ⨾ (εₓ _ ⊗ id↔) ⨾ unite⋆l 

curry/ : {A B C : 𝕌} → (A ×ᵤ B ↔ C) → (v : ⟦ B ⟧) → (A ↔ 𝟙/ v ×ᵤ C)
curry/ c v = uniti⋆l ⨾ (ηₓ v ⊗ id↔) ⨾ swap⋆ ⨾ assocl⋆ ⨾ (c ⊗ id↔) ⨾ swap⋆

-- h.o. version of cnot specialized to input input (v , w)

htf : ∀ (v w : _) → 𝟙 ↔ 𝟙/ (v , w) ×ᵤ (𝔹 ×ᵤ 𝔹)
htf v w = hof/ CNOT (v , w)

-- applying htf to incoming input
htfc : ∀ (v w : _) → (𝔹 ×ᵤ 𝔹) ↔ (𝔹 ×ᵤ 𝔹)
htfc v w = uniti⋆l ⨾ (htf v w ⊗ id↔) ⨾ app/ (v , w)

htfca : ⟦ 𝔹 ×ᵤ 𝔹 ⟧ → Maybe ⟦ 𝔹 ×ᵤ 𝔹 ⟧
htfca (v , w) = eval (htfc v w) (v , w)

x1 x2 x3 x4 : Maybe ⟦ 𝔹 ×ᵤ 𝔹 ⟧
x1 = htfca (𝔽 , 𝔽) -- just (𝔽 , 𝔽)
x2 = htfca (𝔽 , 𝕋) -- just (𝔽 , 𝕋)
x3 = htfca (𝕋 , 𝔽) -- just (𝕋 , 𝕋)
x4 = htfca (𝕋 , 𝕋) -- just (𝕋 , 𝔽)

-----------------------------------------------------------------------------
-- Algebraic Identities
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
  (id↔ ⊗ (! c) ⊗ id↔) ⨾ assocl⋆ ⨾
  ((swap⋆ ⨾ εₓ _) ⊗ id↔) ⨾ unite⋆l

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
