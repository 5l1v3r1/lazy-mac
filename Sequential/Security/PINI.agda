import Lattice as L

module Sequential.Security.PINI (𝓛 : L.Lattice) (A : L.Label 𝓛) where

open import Types 𝓛


import Sequential.Calculus as S
open S 𝓛

import Sequential.Semantics as S₁
open S₁ 𝓛

open import Sequential.Determinism 𝓛
open import Sequential.Security.Erasure 𝓛 A

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty

open import Sequential.Security.Graph 𝓛 A
open import Sequential.Security.LowEq 𝓛 A

pini : ∀ {l ls τ} {p₁ p₁' p₂ p₂' : Program l ls τ} -> p₁ ≅ᴾ p₂ -> p₁ ⟼ p₁' -> p₂ ⟼ p₂' -> p₁' ≅ᴾ p₂'
pini eq s₁ s₂ = aux eq (εᴾ-sim s₁) (εᴾ-sim s₂)
  where aux : ∀ {l ls τ} {p₁ p₁' p₂ p₂' : Program l ls τ} -> p₁ ≡ p₂ -> p₁ ⟼ p₁' -> p₂ ⟼ p₂' -> p₁' ≡ p₂'
        aux refl x y = determinismᴾ x y

-- Simulation of low-step (shows that we maintain the program structure)
stepᴸ : ∀ {ls τ l Ms₁ Ms₂} {Γ₁ Γ₂ : Heaps ls} {Ts₁ Ts₂ : TS∙ l τ}
             -> (l⊑A : l ⊑ A) -> ⟨ Ms₁ , Γ₁ , Ts₁ ⟩ ⟼ ⟨ Ms₂ , Γ₂ , Ts₂ ⟩ ->
                ⟨ map-εᴹ Ms₁ , map-εᴴ Γ₁ , εᵀˢ (yes l⊑A) Ts₁ ⟩ ⟼ ⟨ map-εᴹ Ms₂ , map-εᴴ Γ₂ , εᵀˢ (yes l⊑A) Ts₂ ⟩
stepᴸ l⊑A step = ε₁ᴾ-sim (yes l⊑A) step

-- We need these lemmas separatedly from stepᴴ, because if we collapse
-- the whole program we loose information about memories
stepᴴ-≅ᴹ : ∀ {H ls τ} {p₁ p₂ : Program H ls τ } -> H ⋤ A -> p₁ ⟼ p₂ -> (Ms p₁)  map-≅ᴹ  (Ms p₂)
stepᴴ-≅ᴹ H⋤A (S₁.Pure l∈Γ step uᴴ-≅ᴹ) = refl
stepᴴ-≅ᴹ H⋤A (S₁.New {l⊑H = l⊑H} H∈Γ uᴴ-≅ᴹ) = writeᴹ∙-≡ (trans-⋤ l⊑H H⋤A) H∈Γ uᴴ-≅ᴹ
stepᴴ-≅ᴹ H⋤A S₁.New∙ = refl
stepᴴ-≅ᴹ H⋤A (S₁.Write₂ {l⊑H = l⊑H} H∈Γ uᴹ uˢ) = writeᴹ∙-≡ (trans-⋤ l⊑H H⋤A) H∈Γ uˢ
stepᴴ-≅ᴹ H⋤A (S₁.Writeᴰ₂ {l⊑H = l⊑H} H∈Γ uᴹ uˢ) = writeᴹ∙-≡ (trans-⋤ l⊑H H⋤A) H∈Γ uˢ
stepᴴ-≅ᴹ H⋤A S₁.Write∙₂ = refl
stepᴴ-≅ᴹ H⋤A (S₁.Read₂ l∈Γ n∈M) = refl
stepᴴ-≅ᴹ H⋤A (S₁.Readᴰ₂ L∈Γ n∈M) = refl
stepᴴ-≅ᴹ H⋤A (S₁.DeepDup₁ ¬var l∈Γ uᴱ) = refl
stepᴴ-≅ᴹ H⋤A (S₁.DeepDup₂ τ∈π L∈Γ t∈Δ l∈Γ uᴱ) = refl
stepᴴ-≅ᴹ _ Hole = refl

stepᴴ-≅ᴴ : ∀ {H ls τ} {p₁ p₂ : Program H ls τ } -> H ⋤ A -> p₁ ⟼ p₂ -> (Γ p₁) map-≅ᴴ (Γ p₂)
stepᴴ-≅ᴴ H⋤A (S₁.Pure l∈Γ step uᴱ) = writeᴴ∙-≡ H⋤A l∈Γ uᴱ
stepᴴ-≅ᴴ H⋤A (S₁.New H∈Γ uᴴ) = refl
stepᴴ-≅ᴴ H⋤A S₁.New∙ = refl
stepᴴ-≅ᴴ H⋤A (S₁.Write₂ H∈Γ uᴹ uˢ) = refl
stepᴴ-≅ᴴ H⋤A (S₁.Writeᴰ₂ H∈Γ uᴹ uˢ) = refl
stepᴴ-≅ᴴ H⋤A S₁.Write∙₂ = refl
stepᴴ-≅ᴴ H⋤A (S₁.Read₂ l∈Γ n∈M) = refl
stepᴴ-≅ᴴ H⋤A (S₁.Readᴰ₂ L∈Γ n∈M) = refl
stepᴴ-≅ᴴ H⋤A (S₁.DeepDup₁ ¬var l∈Γ uᴱ) = writeᴴ∙-≡ H⋤A l∈Γ uᴱ
stepᴴ-≅ᴴ H⋤A (S₁.DeepDup₂ τ∈π H∈Γ t∈Δ l∈Γ uᴱ) = writeᴴ∙-≡ H⋤A l∈Γ uᴱ
stepᴴ-≅ᴴ _ Hole = refl

stepᴴ : ∀ {H ls τ} {p₁ p₂ : Program H ls τ} -> (H⋤A : H ⋤ A) -> p₁ ⟼ p₂ -> p₁ ≈ᴾ⟨ no H⋤A ⟩ p₂
stepᴴ {H} {ls} {τ} {p₁} {p₂} H⋤A step
  = ⟨ map-⌜ stepᴴ-≅ᴹ H⋤A step ⌝ᴹ , map-⌜ stepᴴ-≅ᴴ H⋤A step ⌝ᴴ  , (Kᵀˢ (lift-εᵀˢ (no H⋤A) (TS p₁)) (lift-εᵀˢ (no H⋤A) (TS p₂))) ⟩
