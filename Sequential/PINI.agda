import Lattice as L

module Sequential.PINI (𝓛 : L.Lattice) (A : L.Label 𝓛) where

open import Types 𝓛


import Sequential.Calculus as S
open S 𝓛

import Sequential.Semantics as S₁
open S₁ 𝓛

open import Sequential.Determinism 𝓛
open import Sequential.Erasure 𝓛 A

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty

data _≈ᴾ_ {l ls τ} (p₁ p₂ : Program l ls τ) : Set where
  εᴾ-refl : εᴾ p₁ ≡ εᴾ p₂ -> p₁ ≈ᴾ p₂

pini : ∀ {l ls τ} {p₁ p₁' p₂ p₂' : Program l ls τ} -> p₁ ≈ᴾ p₂ -> p₁ ⟼ p₁' -> p₂ ⟼ p₂' -> p₁' ≈ᴾ p₂'
pini (εᴾ-refl eq) s₁ s₂ = εᴾ-refl (aux eq (εᴾ-sim s₁) (εᴾ-sim s₂))
  where aux : ∀ {l ls τ} {p₁ p₁' p₂ p₂' : Program l ls τ} -> p₁ ≡ p₂ -> p₁ ⟼ p₁' -> p₂ ⟼ p₂' -> p₁' ≡ p₂'
        aux refl x y = determinismᴾ x y

stepᴴ : ∀ {H ls τ} {p₁ p₂ : Program H ls τ} -> H ⋤ A -> p₁ ⟼ p₂ -> p₁ ≈ᴾ p₂
stepᴴ {H} {ls} {τ} H⋤A step = εᴾ-refl (aux (H ⊑? A))
  where aux : ∀ {p₁ p₂ : Program H ls τ} -> (x : Dec (H ⊑ A)) -> ε₁ᴾ x p₁ ≡ ε₁ᴾ x p₂
        aux (yes H⊑A) = ⊥-elim (H⋤A H⊑A)
        aux (no _) = refl

-- Simulation of low-step (shows that we maintain the program structure)
stepᴸ : ∀ {ls π₁ π₂ τ l τ₁ τ₂} {Γ₁ Γ₂ : Heaps ls} {t₁ : Term π₁ τ₁} {t₂ : Term π₂ τ₂} {S₁ : Stack l _ τ} {S₂ : Stack l _ τ}
             -> l ⊑ A -> ⟨ Γ₁ , t₁ , S₁ ⟩ ⟼ ⟨ Γ₂ , t₂ , S₂ ⟩ -> ⟨ εᴴ Γ₁ , εᵀ t₁ , εˢ S₁ ⟩ ⟼ ⟨ εᴴ Γ₂ , εᵀ t₂ , εˢ S₂ ⟩
stepᴸ l⊑A step = ε₁ᴾ-sim (yes l⊑A) step

stepᴴ-Γ : ∀ {H ls τ₁ τ₂ τ π₁ π₂} {Γ₁ Γ₂ : Heaps ls} {t₁ : Term π₁ τ₁} {t₂ : Term π₂ τ₂} {S₁ : Stack H _ τ } {S₂ : Stack _ _ _} ->
          H ⋤ A -> ⟨ Γ₁ , t₁ , S₁ ⟩ ⟼ ⟨ Γ₂ , t₂ , S₂ ⟩ -> εᴴ Γ₁ ≡ εᴴ Γ₂
stepᴴ-Γ H⋤A (S₁.Pure l∈Γ step uᴴ) = writeᴹ∙-≡ H⋤A l∈Γ uᴴ
stepᴴ-Γ H⋤A (S₁.New {l⊑h = L⊑H} H∈Γ uᴴ) = writeᴹ∙-≡ (trans-⋢ L⊑H H⋤A) H∈Γ uᴴ
stepᴴ-Γ H⋤A S₁.New∙ = refl
stepᴴ-Γ H⋤A (S₁.Write₂ {l⊑H = L⊑H} H∈Γ uᴹ uᴴ) = writeᴹ∙-≡ (trans-⋢ L⊑H H⋤A) H∈Γ uᴴ
stepᴴ-Γ H⋤A (S₁.Writeᴰ₂ {l⊑H = L⊑H} H∈Γ uᴹ uᴴ) = writeᴹ∙-≡ (trans-⋢ L⊑H H⋤A) H∈Γ uᴴ
stepᴴ-Γ H⋤A S₁.Write∙₂ = refl
stepᴴ-Γ H⋤A (S₁.Read₂ l∈Γ n∈M) = refl
stepᴴ-Γ H⋤A (S₁.Readᴰ₂ L∈Γ n∈M) = refl
stepᴴ-Γ H⋤A (S₁.DeepDupˢ L⊏l L∈Γ t∈Δ) = refl
