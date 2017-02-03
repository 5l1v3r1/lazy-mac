module MAC  where

open import Lattice.TwoPoint

open import Sequential 2-point
open import Sequential.PINI 2-point L

mac-is-pini : ∀ {l τ} {p₁ p₁' p₂ p₂' : Program l lh τ} -> p₁ ≈ᴾ p₂ -> p₁ ⟼ p₁' -> p₂ ⟼ p₂' -> p₁' ≈ᴾ p₂'
mac-is-pini eq step = pini eq step
