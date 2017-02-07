import Lattice as L
import Scheduler as S
open import Scheduler.Security


module Concurrent.PSNI {𝓛 : L.Lattice} {𝓢 : S.Scheduler 𝓛} (A : L.Label 𝓛) (𝓝 : NIˢ 𝓛 A 𝓢) where

open import Types 𝓛

open import Data.Product renaming (_,_ to ⟨_,_⟩)

open import Relation.Nullary

open import Sequential.Calculus 𝓛

--------------------------------------------------------------------------------
-- Temporarily side-step bug #2245
import Concurrent.Calculus as C
open C 𝓛 𝓢
-- open import Concurrent.Calculus 𝓛 𝓢

import Concurrent.Semantics as CS
open CS 𝓛 𝓢
-- open import Concurrent.Semantics 𝓛 𝓢 public
--------------------------------------------------------------------------------

open Scheduler.Security.NIˢ 𝓛 A 𝓝 renaming (State to Stateˢ)
open import Concurrent.Erasure A 𝓝

data  _↪⋆-≈ᴳ_ {ls} (g₁' : Global ls) (g₂ : Global ls) : Set where
   Cᴳ : ∀ (g₂' : Global ls) -> g₂' ≈ᴳ g₂ -> g₁' ↪⋆ g₂' -> g₁' ↪⋆-≈ᴳ g₂

εᴳ-simᴸ⋆ : ∀ {L n n₁ n₂ ls g₁'} {Σ₁ Σ₂ : Stateˢ} {Γ₁ Γ₂ : Heaps ls} {P₁ P₂ : Pools ls} ->
               Σ₁ ≈ˢ-⟨ n₁ , n₂ ⟩ Σ₂ ->
               let g₁ = ⟨ Σ₁ , Γ₁ , P₁ ⟩
                   g₂ = ⟨ Σ₂ , Γ₂ , P₂ ⟩ in
               L ⊑ A -> ⟨ L , n ⟩ ⊢ g₁ ↪ g₁' -> g₁ ≈ᴳ g₂ -> g₁' ↪⋆-≈ᴳ g₂
εᴳ-simᴸ⋆ Σ₁≈Σ₂ L⊑A step g₁'≈g₂' = {!!}

εᴳ-sim⋆ : ∀ {l n ls} {g₁ g₁' g₂ : Global ls} -> Dec (l ⊑ A) -> ⟨ l , n ⟩ ⊢ g₁ ↪ g₁' -> g₁ ≈ᴳ g₂ -> g₁' ↪⋆-≈ᴳ g₂
εᴳ-sim⋆ (yes L⊑A) step x = εᴳ-simᴸ⋆ (align (≈ᴳ-≈ˢ x)) L⊑A step x
εᴳ-sim⋆ {g₁ = g₁} {g₁' = g₁'} {g₂ = g₂} (no H⋤A) stepᴴ g₁≈g₂ = Cᴳ g₁' (trans-≈ᴳ (sym-≈ᴳ (εᴳ-simᴴ H⋤A stepᴴ)) g₁≈g₂) []
