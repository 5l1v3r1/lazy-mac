module Lattice.Base where

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

record Lattice : Set₁ where
  constructor Lat
  field
    Label : Set
    _⊑_ : Label -> Label -> Set
    _⊑?_ : (l₁ l₂ : Label) -> Dec (l₁ ⊑ l₂)

    -- Even though this lemma is not strictly necessary it does simplify
    -- some proofs.
    -- This decision is consistent with the corresponding Haskell type class which
    -- requires at most one instance for every pair of label.
    extensional : ∀ {l₁ l₂} -> (x y : l₁ ⊑ l₂) -> x ≡ y

    refl-⊑ : ∀ {l} -> l ⊑ l
    trans-⊑ : ∀ {l₁ l₂ l₃} -> l₁ ⊑ l₂ -> l₂ ⊑ l₃ -> l₁ ⊑ l₃

    _≟_ : (l₁ l₂ : Label) -> Dec (l₁ ≡ l₂)


-- TODO add what other postulates about lattices we have

  module Lemma (𝓛 : Lattice) where

    open import Data.Empty
    
    trans-⋢  : ∀ {a b c} -> a ⊑ b -> ¬ (a ⊑ c) -> ¬ (b ⊑ c)
    trans-⋢ a⊑b ¬a⊑c b⊑c = ⊥-elim (¬a⊑c (trans-⊑ a⊑b b⊑c))
