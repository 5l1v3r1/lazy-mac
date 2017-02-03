import Lattice as L

module Sequential.PINI (𝓛 : L.Lattice) (A : L.Label 𝓛) where

open import Types 𝓛
open import Sequential.Calculus 𝓛
open import Sequential.Semantics 𝓛
open import Sequential.Determinism 𝓛
open import Sequential.Erasure 𝓛 A

open import Relation.Binary.PropositionalEquality

data _≈ᴾ_ {l ls τ} (p₁ p₂ : Program l ls τ) : Set where
  ε-refl : εᴾ p₁ ≡ εᴾ p₂ -> p₁ ≈ᴾ p₂

pini : ∀ {l ls τ} {p₁ p₁' p₂ p₂' : Program l ls τ} -> p₁ ≈ᴾ p₂ -> p₁ ⟼ p₁' -> p₂ ⟼ p₂' -> p₁' ≈ᴾ p₂'
pini (ε-refl eq) s₁ s₂ = ε-refl (aux eq (εᴾ-sim s₁) (εᴾ-sim s₂))
  where aux : ∀ {l ls τ} {p₁ p₁' p₂ p₂' : Program l ls τ} -> p₁ ≡ p₂ -> p₁ ⟼ p₁' -> p₂ ⟼ p₂' -> p₁' ≡ p₂'
        aux refl x y = determinism⟼ x y
