module Base where
open import Relation.Binary.PropositionalEquality

is-prop : Set → Set
is-prop X = (x y : X) → x ≡ y

_∼_ : {A B : Set} → (f g : A → B) → Set
f ∼ g = ∀ a → f a ≡ g a

