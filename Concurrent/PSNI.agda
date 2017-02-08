import Lattice as L
import Scheduler as S
open import Scheduler.Security


module Concurrent.PSNI {𝓛 : L.Lattice} {𝓢 : S.Scheduler 𝓛} (A : L.Label 𝓛) (𝓝 : NIˢ 𝓛 A 𝓢) where

open import Types 𝓛
open import Data.Product renaming (_,_ to ⟨_,_⟩)

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
open import Sequential.PINI 𝓛 A using (stepᴸ ; stepᴴ-Γ)

--------------------------------------------------------------------------------

open Scheduler.Security.NIˢ 𝓛 A 𝓝 renaming (State to Stateˢ)
open import Concurrent.Erasure A 𝓝
open import Concurrent.LowEq A 𝓝

εᴳ-simᴸ : ∀ {l n ls} {g₁ g₂ : Global ls} -> l ⊑ A ->  ⟨ l , n ⟩ ⊢ g₁ ↪ g₂ -> ⟨ l , n ⟩ ⊢ (εᴳ g₁) ↪ (εᴳ g₂)
εᴳ-simᴸ l⊑A (CS.step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ)
  = step-∅ (memberᴾ l⊑A l∈P) (memberᵀ l⊑A t∈T) (εᵀ¬Fork ¬fork) (stepᴸ l⊑A step) (εˢ-simᴸ l⊑A sch) (updateᵀ l⊑A uᵀ) (updateᴾ l⊑A uᴾ)
εᴳ-simᴸ l⊑A (CS.fork {H = H} {tᴴ = tᴴ} {Tᴴ = Tᴴ} l∈P t∈T step uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ) with memberᵀ l⊑A t∈T | stepᴸ l⊑A step | εˢ-simᴸ l⊑A sch
... | t∈T' | step' | sch' with H ⊑? A
... | yes H⊑A rewrite lengthᵀ-ε-≡ H⊑A Tᴴ
    = fork (memberᴾ l⊑A l∈P) t∈T' step' (updateᵀ l⊑A uᵀ) (updateᴾ l⊑A u₁ᴾ) (memberᴾ H⊑A H∈P₂) sch' (updateᴾ-▻ Tᴴ (⟨ tᴴ , [] ⟩) H⊑A u₂ᴾ)
εᴳ-simᴸ l⊑A (CS.fork {tᴴ = tᴴ} {P₂ = P₂} {Tᴴ = Tᴴ} l∈P t∈T step uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ) | t∈T' | step' | sch' | no H⋤A
  rewrite newᴾ∙ Tᴴ ⟨ tᴴ , [] ⟩ H⋤A u₂ᴾ = fork∙ {P₂ = εᴾ P₂} (memberᴾ l⊑A l∈P) t∈T' step' (updateᵀ l⊑A uᵀ) (updateᴾ l⊑A u₁ᴾ) sch'
εᴳ-simᴸ l⊑A (CS.fork∙ l∈P t∈T step uᵀ u₁ᴾ sch)
  = fork∙ (memberᴾ l⊑A l∈P) (memberᵀ l⊑A t∈T) (stepᴸ l⊑A step) (updateᵀ l⊑A uᵀ) (updateᴾ l⊑A u₁ᴾ) (εˢ-simᴸ l⊑A sch)
εᴳ-simᴸ l⊑A (CS.skip l∈P t∈T stuck sch) = skip (memberᴾ l⊑A l∈P) (memberᵀ l⊑A t∈T) (stuck-ε l⊑A stuck) (εˢ-simᴸ l⊑A sch)
εᴳ-simᴸ l⊑A (CS.done l∈P t∈T don sch) = done (memberᴾ l⊑A l∈P) (memberᵀ l⊑A t∈T) (done-ε l⊑A don) (εˢ-simᴸ l⊑A sch)

εᴳ-simᴴ : ∀ {H n ls} {g₁ g₂ : Global ls} -> H ⋤ A -> ⟨ H , n ⟩ ⊢ g₁ ↪ g₂ -> g₁ ≅ᴳ g₂
εᴳ-simᴴ H⋤A (CS.step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ) = εᴳ-refl (lift-εᴳ (⌞ εˢ-simᴴ H⋤A sch ⌟) (stepᴴ-Γ H⋤A step) (updateᴾ∙ H⋤A uᴾ))
εᴳ-simᴴ H⋤A (CS.fork {l⊑H = L⊑H} l∈P t∈T step uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ)
  = εᴳ-refl (lift-εᴳ (⌞ εˢ-simᴴ H⋤A sch ⌟) (stepᴴ-Γ H⋤A step) (trans (updateᴾ∙ H⋤A u₁ᴾ) (updateᴾ∙ (trans-⋢ L⊑H H⋤A) u₂ᴾ)))
εᴳ-simᴴ H⋤A (CS.fork∙ l∈P t∈T step uᵀ u₁ᴾ sch) = εᴳ-refl (lift-εᴳ (⌞ εˢ-simᴴ H⋤A sch ⌟) (stepᴴ-Γ H⋤A step) (updateᴾ∙ H⋤A u₁ᴾ))
εᴳ-simᴴ H⋤A (CS.skip l∈P t∈T stuck sch) = εᴳ-refl (lift-εᴳ (⌞ εˢ-simᴴ H⋤A sch ⌟) refl refl)
εᴳ-simᴴ H⋤A (CS.done l∈P t∈T don sch) = εᴳ-refl (lift-εᴳ (⌞ εˢ-simᴴ H⋤A sch ⌟) refl refl)

--------------------------------------------------------------------------------

data  _↪⋆-≈ᴳ_ {ls} (g₁' : Global ls) (g₂ : Global ls) : Set where
   Cᴳ : ∀ (g₂' : Global ls) -> g₂' ≈ᴳ g₂ -> g₁' ↪⋆ g₂' -> g₁' ↪⋆-≈ᴳ g₂

open import Data.Nat

-- memberᵀ : ∀ {ls L} {T₁ : Pool L} {P₁ P₂ : Pools ls} -> L ⊑ A -> L ↦ T₁ ∈ᴾ P₁ -> P₁ ≈ᴾ P₂ -> ∃ (λ T₂ -> L ↦ T₂ ∈ᴾ P₂)
-- memberᵀ = ?

εᴳ-simᴸ⋆ : ∀ {L n n₁ ls} {Σ₁ Σ₁' Σ₂ : Stateˢ} {Γ₁ Γ₁' Γ₂ : Heaps ls} {P₁ P₁' P₂ : Pools ls} ->
               (n₂ : SC.ℕ) ->
               Σ₁ ≈ˢ-⟨ n₁ , n₂ ⟩ Σ₂ ->
               let g₁ = ⟨ Σ₁ , Γ₁ , P₁ ⟩
                   g₁' = ⟨ Σ₁' , Γ₁' , P₁' ⟩
                   g₂ = ⟨ Σ₂ , Γ₂ , P₂ ⟩ in
               L ⊑ A -> ⟨ L , n ⟩ ⊢ g₁ ↪ g₁' -> g₁ ≈ᴳ g₂ -> g₁' ↪⋆-≈ᴳ g₂
εᴳ-simᴸ⋆ SC.zero Σ₁≈Σ₂ L⊑A step g₁'≈g₂' with squareˢ L⊑A Σ₁≈Σ₂ (getSchStep step)
εᴳ-simᴸ⋆ zero Σ₁≈Σ₂ L⊑A (CS.step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ) g₁'≈g₂' | sch' = {!!}
εᴳ-simᴸ⋆ zero Σ₁≈Σ₂ L⊑A (CS.fork l∈P t∈T step uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ) g₁'≈g₂' | sch' = {!!}
εᴳ-simᴸ⋆ zero Σ₁≈Σ₂ L⊑A (CS.fork∙ l∈P t∈T step uᵀ uᴾ sch) g₁'≈g₂' | sch' = {!!}
εᴳ-simᴸ⋆ zero Σ₁≈Σ₂ L⊑A (CS.skip l∈P t∈T stuck sch) g₁'≈g₂' | sch' = {!!}

εᴳ-simᴸ⋆ zero Σ₁≈Σ₂ L⊑A (CS.done l∈P t∈T don sch) g₁'≈g₂' | ⟨ Σ₂' , sch' ⟩
  = Cᴳ ⟨ Σ₂' , {!!} , {!!} ⟩ {!!} (done {!!} {!!} (done-ε L⊑A {!don!}) {!sch'!} ∷ [])

-- εᴳ-simᴸ⋆ {n₂ = zero} {g₁' = C.⟨ Σ , Γ , P ⟩} Σ₁≈Σ₂ L⊑A step g₁'≈g₂' | ⟨ Σ₂' , sch' ⟩ = ?
-- Cᴳ ⟨ Σ₂' , {!!} , {!!} ⟩ {!!} ({!!} ∷ [])
εᴳ-simᴸ⋆ (SC.suc n₂) Σ₁≈Σ₂ L⊑A step g₁'≈g₂' = {!!}

εᴳ-sim⋆ : ∀ {l n ls} {g₁ g₁' g₂ : Global ls} -> Dec (l ⊑ A) -> ⟨ l , n ⟩ ⊢ g₁ ↪ g₁' -> g₁ ≈ᴳ g₂ -> g₁' ↪⋆-≈ᴳ g₂
εᴳ-sim⋆ (yes L⊑A) step x = εᴳ-simᴸ⋆ _ (align (Σ₁≈Σ₂ x)) L⊑A step x
εᴳ-sim⋆ {g₁ = g₁} {g₁' = g₁'} {g₂ = g₂} (no H⋤A) stepᴴ g₁≈g₂ = Cᴳ g₁' (trans-≈ᴳ (sym-≅ᴳ (εᴳ-simᴴ H⋤A stepᴴ)) ?) [] -- g₁≈g₂) []
