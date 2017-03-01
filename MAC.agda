module MAC  where

open import Lattice.TwoPoint

open import Sequential 2-point
open import Sequential.LowEq 2-point L
open import Sequential.PINI 2-point L

mac-is-pini : ∀ {l τ} {p₁ p₁' p₂ p₂' : Program l lh τ} -> p₁ ≅ᴾ p₂ -> p₁ ⟼ p₁' -> p₂ ⟼ p₂' -> p₁' ≅ᴾ p₂'
mac-is-pini eq step = pini eq step

open import Scheduler.RoundRobin 2-point
open import Scheduler.RoundRobin.Security {2-point} L

open import Concurrent 2-point RR
open import Concurrent.Erasure L RR-is-NI
open import Concurrent.LowEq L RR-is-NI
open import Concurrent.PSNI L RR-is-NI
open import Data.Product

mac-is-psni : ∀ {l n} {g₁ g₁' g₂ : Global lh} -> g₁ ≅ᴳ g₂ -> ( l , n )  ⊢ g₁ ↪ g₁' -> ∃ (λ g₂' → g₂ ↪⋆ g₂' × g₁' ≅ᴳ g₂')
mac-is-psni eq s = psni eq s
