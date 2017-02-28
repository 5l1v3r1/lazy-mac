import Lattice as L
import Scheduler as S
open import Scheduler.Security

module Concurrent.Lemmas {𝓛 : L.Lattice} {𝓢 : S.Scheduler 𝓛} (A : L.Label 𝓛) (𝓝 : NIˢ 𝓛 A 𝓢) where

open import Types 𝓛
open import Data.Product using (∃ ; _×_ ; proj₁ ; proj₂ )
import Data.Product as P

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
--------------------------------------------------------------------------------
-- Temporarily side-step bug #2245

import Sequential.Calculus as SC
open SC 𝓛


import Concurrent.Calculus as C
open C 𝓛 𝓢
-- open import Concurrent.Calculus 𝓛 𝓢

import Concurrent.Semantics as CS
open CS 𝓛 𝓢
-- open import Concurrent.Semantics 𝓛 𝓢 public

open import Sequential.Erasure 𝓛 A as SE hiding (εᵀ ; εᴾ ; εˢ)
open import Sequential.PINI 𝓛 A using (stepᴸ ; stepᴴ-≅ᴹ ; stepᴴ-≅ᴴ)

--------------------------------------------------------------------------------

open Scheduler.Security.NIˢ 𝓛 A 𝓝 renaming (State to Stateˢ)
open import Concurrent.Erasure A 𝓝

import Concurrent.LowEq as L₁
open L₁ A 𝓝

open import Data.Product renaming (_,_ to ⟨_,_⟩)

-- Square
εᴳ-simᴸ : ∀ {l n ls} {g₁ g₂ : Global ls} -> l ⊑ A ->  ⟨ l , n ⟩ ⊢ g₁ ↪ g₂ -> ⟨ l , n ⟩ ⊢ (εᴳ g₁) ↪ (εᴳ g₂)
εᴳ-simᴸ l⊑A (CS.step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ)
  = step-∅ (memberᴾ l⊑A l∈P) (memberᵀ l⊑A t∈T) (εᵀ¬Fork ¬fork) (stepᴸ l⊑A step) (εˢ-simᴸ l⊑A sch) (updateᵀ l⊑A uᵀ) (updateᴾ l⊑A uᴾ)
εᴳ-simᴸ l⊑A (CS.fork {H = H} {tᴴ = tᴴ} {Tᴴ = Tᴴ} l∈P t∈T uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ) with memberᵀ l⊑A t∈T | εˢ-simᴸ l⊑A sch
... | t∈T' | sch' with H ⊑? A
... | yes H⊑A rewrite lengthᵀ-ε-≡ H⊑A Tᴴ
    = fork (memberᴾ l⊑A l∈P) t∈T' (updateᵀ l⊑A uᵀ) (updateᴾ l⊑A u₁ᴾ) (memberᴾ H⊑A H∈P₂) sch' (updateᴾ-▻ Tᴴ (⟨ tᴴ , [] ⟩) H⊑A u₂ᴾ)
εᴳ-simᴸ l⊑A (CS.fork {tᴴ = tᴴ} {P₂ = P₂} {Tᴴ = Tᴴ} l∈P t∈T uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ) | t∈T' | sch' | no H⋤A
  rewrite newᴾ∙ Tᴴ ⟨ tᴴ , [] ⟩ H⋤A u₂ᴾ = fork∙ {P₂ = map-εᴾ P₂} (memberᴾ l⊑A l∈P) t∈T' (updateᵀ l⊑A uᵀ) (updateᴾ l⊑A u₁ᴾ) sch'
εᴳ-simᴸ l⊑A (CS.fork∙ l∈P t∈T uᵀ u₁ᴾ sch)
  = fork∙ (memberᴾ l⊑A l∈P) (memberᵀ l⊑A t∈T) (updateᵀ l⊑A uᵀ) (updateᴾ l⊑A u₁ᴾ) (εˢ-simᴸ l⊑A sch)
εᴳ-simᴸ l⊑A (CS.skip l∈P t∈T stuck sch) = skip (memberᴾ l⊑A l∈P) (memberᵀ l⊑A t∈T) (stuck-ε l⊑A stuck) (εˢ-simᴸ l⊑A sch)
εᴳ-simᴸ l⊑A (CS.done l∈P t∈T don sch) = done (memberᴾ l⊑A l∈P) (memberᵀ l⊑A t∈T) (done-ε l⊑A don) (εˢ-simᴸ l⊑A sch)


-- Triangle
εᴳ-simᴴ : ∀ {H n ls} {g₁ g₂ : Global ls} -> H ⋤ A -> ⟨ H , n ⟩ ⊢ g₁ ↪ g₂ -> g₁ ≅ᴳ g₂
εᴳ-simᴴ H⋤A (CS.step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ)
  = lift-εᴳ (⌞ εˢ-simᴴ H⋤A sch ⌟) (stepᴴ-≅ᴹ H⋤A step) (stepᴴ-≅ᴴ H⋤A step) (updateᴾ∙ H⋤A uᴾ)
εᴳ-simᴴ H⋤A (CS.fork {l⊑H = L⊑H} l∈P t∈T uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ)
  = lift-εᴳ (⌞ εˢ-simᴴ H⋤A sch ⌟) refl refl (trans (updateᴾ∙ H⋤A u₁ᴾ) (updateᴾ∙ (trans-⋤ L⊑H H⋤A) u₂ᴾ))
εᴳ-simᴴ H⋤A (CS.fork∙ l∈P t∈T uᵀ u₁ᴾ sch) = lift-εᴳ (⌞ εˢ-simᴴ H⋤A sch ⌟) refl refl (updateᴾ∙ H⋤A u₁ᴾ)
εᴳ-simᴴ H⋤A (CS.skip l∈P t∈T stuck sch) = lift-εᴳ (⌞ εˢ-simᴴ H⋤A sch ⌟) refl refl refl
εᴳ-simᴴ H⋤A (CS.done l∈P t∈T don sch) = lift-εᴳ (⌞ εˢ-simᴴ H⋤A sch ⌟) refl refl refl
