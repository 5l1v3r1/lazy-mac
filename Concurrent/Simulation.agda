import Lattice as L
import Scheduler as S
open import Scheduler.Security

module Concurrent.Simulation {𝓛 : L.Lattice} {𝓢 : S.Scheduler 𝓛} (A : L.Label 𝓛) (𝓝 : NIˢ 𝓛 A 𝓢) where

open import Types 𝓛
open import Data.Product as P
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Sequential.Calculus 𝓛 renaming (⟨_,_⟩ to mkᵀ)
open import Sequential.Security 𝓛 A


open import Concurrent.Calculus 𝓛 𝓢
open import Concurrent.Semantics 𝓛 𝓢 public
open import Concurrent.Erasure A 𝓝
open import Concurrent.LowEq A 𝓝
open import Concurrent.Valid 𝓛 𝓢 as V hiding (memberᴾ)

open Scheduler.Security.NIˢ 𝓛 A 𝓝 renaming (State to Stateˢ)

-- Square
εᴳ-simᴸ : ∀ {l n ls} {g₁ g₂ : Global ls} {{v : validᴳ g₁}} -> l ⊑ A ->  ( l , n ) ⊢ g₁ ↪ g₂ -> ( l , n ) ⊢ (εᴳ g₁) ↪ (εᴳ g₂)
εᴳ-simᴸ l⊑A (step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ)
  = step-∅ (memberᴾ l⊑A l∈P) (memberᵀ l⊑A t∈T) (¬fork-ε l⊑A ¬fork) (stepᴸ l⊑A step) (εˢ-simᴸ l⊑A sch) (updateᵀᴸ l⊑A uᵀ) (updateᴾᴸ l⊑A uᴾ)
εᴳ-simᴸ l⊑A (fork {H = H} {tᴴ = tᴴ} {Tᴴ = Tᴴ} l∈P t∈T uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ) with memberᵀ l⊑A t∈T | εˢ-simᴸ l⊑A sch
... | t∈T' | sch' with H ⊑? A
... | yes H⊑A rewrite lengthᵀ-ε-≡ H⊑A Tᴴ
    = fork (memberᴾ l⊑A l∈P) t∈T' (updateᵀᴸ l⊑A uᵀ) (updateᴾᴸ l⊑A u₁ᴾ) (memberᴾ H⊑A H∈P₂) sch' (updateᴾ-▻ Tᴴ (mkᵀ tᴴ [] ) H⊑A u₂ᴾ)
εᴳ-simᴸ l⊑A (fork {tᴴ = tᴴ} {P₂ = P₂} {Tᴴ = Tᴴ} l∈P t∈T uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ) | t∈T' | sch' | no H⋤A
  rewrite newᴾ∙ Tᴴ (mkᵀ tᴴ []) H⋤A u₂ᴾ = fork∙ {P₂ = map-εᴾ P₂} (memberᴾ l⊑A l∈P) t∈T' (updateᵀᴸ l⊑A uᵀ) (updateᴾᴸ l⊑A u₁ᴾ) sch'
εᴳ-simᴸ l⊑A (fork∙ l∈P t∈T uᵀ u₁ᴾ sch)
  = fork∙ (memberᴾ l⊑A l∈P) (memberᵀ l⊑A t∈T) (updateᵀᴸ l⊑A uᵀ) (updateᴾᴸ l⊑A u₁ᴾ) (εˢ-simᴸ l⊑A sch)
εᴳ-simᴸ {{ Msⱽ , Γⱽ , Psⱽ }} l⊑A (skip l∈P t∈T stuck sch)
  = skip (memberᴾ l⊑A l∈P) (memberᵀ l⊑A t∈T) (stuck-ε {{ Msⱽ , Γⱽ , V.memberᴾ (V.memberᴾˢ Psⱽ l∈P) t∈T }} l⊑A stuck) (εˢ-simᴸ l⊑A sch)
εᴳ-simᴸ l⊑A (done l∈P t∈T don sch) = done (memberᴾ l⊑A l∈P) (memberᵀ l⊑A t∈T) (done-ε l⊑A don) (εˢ-simᴸ l⊑A sch)


-- Triangle
εᴳ-simᴴ : ∀ {H n ls} {g₁ g₂ : Global ls} -> H ⋤ A -> ( H , n ) ⊢ g₁ ↪ g₂ -> g₁ ≅ᴳ g₂
εᴳ-simᴴ H⋤A (step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ)
  = lift-εᴳ (⌞ εˢ-simᴴ H⋤A sch ⌟) (stepᴴ-≅ᴹ H⋤A step) (stepᴴ-≅ᴴ H⋤A step) (updateᴾ∙ H⋤A uᴾ)
εᴳ-simᴴ H⋤A (fork {l⊑H = L⊑H} l∈P t∈T uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ)
  = lift-εᴳ (⌞ εˢ-simᴴ H⋤A sch ⌟) refl refl (trans (updateᴾ∙ H⋤A u₁ᴾ) (updateᴾ∙ (trans-⋤ L⊑H H⋤A) u₂ᴾ))
εᴳ-simᴴ H⋤A (fork∙ l∈P t∈T uᵀ u₁ᴾ sch) = lift-εᴳ (⌞ εˢ-simᴴ H⋤A sch ⌟) refl refl (updateᴾ∙ H⋤A u₁ᴾ)
εᴳ-simᴴ H⋤A (skip l∈P t∈T stuck sch) = lift-εᴳ (⌞ εˢ-simᴴ H⋤A sch ⌟) refl refl refl
εᴳ-simᴴ H⋤A (done l∈P t∈T don sch) = lift-εᴳ (⌞ εˢ-simᴴ H⋤A sch ⌟) refl refl refl

--------------------------------------------------------------------------------
