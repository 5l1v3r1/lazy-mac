import Lattice as L
import Scheduler as S
open import Scheduler.Security


module Concurrent.PSNI {𝓛 : L.Lattice} {𝓢 : S.Scheduler 𝓛} (A : L.Label 𝓛) (𝓝 : NIˢ 𝓛 A 𝓢) where

open import Types 𝓛

open import Data.Product as P

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
--------------------------------------------------------------------------------
-- Temporarily side-step bug #2245

import Sequential.Calculus as SC renaming (⟨_,_⟩ to mkᵀᴴ ; ⟨_,_,_⟩ to mkᴾ)
open SC 𝓛

import Sequential.Semantics as SS
open SS 𝓛

import Concurrent.Calculus as C hiding (lookupᴾ)
open C 𝓛 𝓢
-- open import Concurrent.Calculus 𝓛 𝓢

import Concurrent.Semantics as CS
open CS 𝓛 𝓢
-- open import Concurrent.Semantics 𝓛 𝓢 public

open import Sequential.Security.Erasure 𝓛 A as SE -- hiding (εᵀ ; εᴾ ; εˢ)
open import Sequential.Security.PINI 𝓛 A as P₂ using (stepᴸ ; stepᴴ-≅ᴴ ; stepᴴ-≅ᴹ ; stepᴴ)

open import Data.Nat as N
--------------------------------------------------------------------------------

open Scheduler.Security.NIˢ 𝓛 A 𝓝 renaming (State to Stateˢ)
open import Scheduler.Base 𝓛

open import Concurrent.Erasure A 𝓝
open import Concurrent.Simulation A 𝓝

import Concurrent.LowEq
module L₁ = Concurrent.LowEq A 𝓝
open L₁

import Sequential.Security.LowEq renaming (_≈ᵀˢ⟨_⟩_ to _≈ᵀᴴ⟨_⟩_ ; ⌞_⌟ᵀˢ to ⌞_⌟ᵀᴴ ; ⌜_⌝ᵀˢ to ⌜_⌝ᵀᴴ ; ⟨_,_,_⟩ to mk≈ᴾ) hiding (_≈ˢ_)
module L₂  = Sequential.Security.LowEq  𝓛 A
open L₂

import Concurrent.Graph
module G₁ = Concurrent.Graph A 𝓝
open G₁

import Sequential.Security.Graph
module G₂ = Sequential.Security.Graph 𝓛 A

open import Concurrent.Valid 𝓛 𝓢 as V hiding (memberᴾ ; updateᴾ)

open import Sequential.Security.Graph 𝓛 A
open import Concurrent.Lemmas A 𝓝
open import Concurrent.Determinism 𝓛 𝓢

data  _↪⋆-≈ᴳ_ {ls} (g₂ : Global ls) (g₁' : Global ls) : Set where
   Cᴳ : ∀ (g₂' : Global ls) -> g₁' ≈ᴳ g₂' -> g₂ ↪⋆ g₂' -> g₂ ↪⋆-≈ᴳ g₁'


squareᴸ : ∀ {l ls n} {g₁ g₁' g₂ g₂' : Global ls} {{v₁ : validᴳ g₁}} {{v₂ : validᴳ g₂}} ->
            (l ⊑ A) -> g₁ ≈ᴳ g₂ -> ( l , n ) ⊢ g₁ ↪ g₁' -> ( l , n ) ⊢ g₂ ↪ g₂' -> g₁' ≈ᴳ g₂'
squareᴸ l⊑A g₁≈g₂ step₁ step₂ = ⌜ aux ⌞ g₁≈g₂ ⌟ᴳ (εᴳ-simᴸ l⊑A step₁) (εᴳ-simᴸ l⊑A step₂) ⌝ᴳ
  where aux : ∀ {ls n l} {g₁ g₁' g₂ g₂' : Global ls} -> g₁ ≡ g₂ -> (l , n) ⊢ g₁ ↪ g₁' -> (l , n) ⊢ g₂ ↪ g₂' -> g₁' ≡ g₂'
        aux refl x y = determinismᶜ x y


triangleᴴ : ∀ {L H ls i j n m} {g₁ g₁' g₂ g₂' : Global ls} {{v₁ : validᴳ g₁}} {{v₂ : validᴳ g₂}} ->
            L ⊑ A -> g₁ ≈ᴳ-⟨ i , suc j ⟩ g₂ -> ( L , n ) ⊢ g₁ ↪ g₁' -> ( H , m ) ⊢ g₂ ↪ g₂' -> g₁ ≈ᴳ-⟨ i , j ⟩ g₂'
triangleᴴ L⊑A L₁.⟨ Σ₁≈Σ₂ , Ms₁≈Ms₂ , Γ₁≈Γ₂ , Ps₁≈Ps₂ ⟩ step₁ step₂ with ≈ˢ-> L⊑A Σ₁≈Σ₂ (getSchStep step₁) (getSchStep step₂)
... | H⋤A , Σ₁≈Σ₂' with ⌜ εᴳ-simᴴ H⋤A step₂ ⌝ᴳ
... | L₁.⟨ Σ₂≈Σ₂' , Ms₂≈Ms₂' , Γ₂≈Γ₂' , Ps₂≈Ps₂' ⟩
  = L₁.⟨ Σ₁≈Σ₂' , (trans-≈ᴹ Ms₁≈Ms₂ Ms₂≈Ms₂') , trans-≈ᴴ Γ₁≈Γ₂ Γ₂≈Γ₂' , L₁.trans-≈ᴾ Ps₁≈Ps₂ Ps₂≈Ps₂' ⟩

εᴳ-simᴸ⋆ : ∀ {L n n₁ ls} {g₁ g₁' g₂ : Global ls} {{v₁ : validᴳ g₁}} {{v₂ : validᴳ g₂}} (n₂ : ℕ) ->
             L ⊑ A -> (L , n)  ⊢ g₁ ↪ g₁' -> g₁ ≈ᴳ-⟨ n₁ , n₂ ⟩ g₂ -> g₂ ↪⋆-≈ᴳ g₁'
εᴳ-simᴸ⋆ N.zero L⊑A step g₁≈g₂ with redexᴳ-≈ L⊑A g₁≈g₂ step
... | CS.Step step' = Cᴳ _ (squareᴸ L⊑A (forgetᴳ g₁≈g₂) step step') (step' ∷ [])


εᴳ-simᴸ⋆ {ls = ls} {g₂ = g₂} {{v₁}} {{v₂ = v₂}} (N.suc n₂) L⊑A step g₁≈g₂ with redexᴳ-≈ᴴ L⊑A g₁≈g₂ step
... | (H , m) , (Step step') with triangleᴴ L⊑A g₁≈g₂ step step'
... | g₁≈g₂' with εᴳ-simᴸ⋆ {{v₂ = valid↪ step' v₂}} n₂ L⊑A step g₁≈g₂'
... | Cᴳ g₂'' g₁≈g₂'' ss = Cᴳ g₂'' g₁≈g₂'' (step' ∷ ss)

εᴳ-sim⋆ : ∀ {l n ls} {g₁ g₁' g₂ : Global ls} {{v₁ : validᴳ g₁}} {{v₂ : validᴳ g₂}} -> Dec (l ⊑ A) -> ( l , n ) ⊢ g₁ ↪ g₁' -> g₁ ≈ᴳ g₂ -> g₂ ↪⋆-≈ᴳ g₁'
εᴳ-sim⋆ (yes L⊑A) step x = εᴳ-simᴸ⋆ _ L⊑A step (alignᴳ x)
εᴳ-sim⋆ {g₁ = g₁} {g₁' = g₁'} {g₂ = g₂} (no H⋤A) stepᴴ g₁≈g₂ = Cᴳ g₂ ( trans-≈ᴳ (sym-≈ᴳ (⌜ εᴳ-simᴴ H⋤A stepᴴ ⌝ᴳ)) g₁≈g₂) []


psni : ∀ {l n ls} {g₁ g₁' g₂ : Global ls} {{v₁ : validᴳ g₁}} {{v₂ : validᴳ g₂}} -> g₁ ≅ᴳ g₂ -> (l , n)  ⊢ g₁ ↪ g₁' -> ∃ (λ g₂' → g₂ ↪⋆ g₂' × g₁' ≅ᴳ g₂')
psni {l} eq s with εᴳ-sim⋆ (l ⊑? A) s ⌜ eq ⌝ᴳ
psni eq s | Cᴳ g₂' g₁'≈ᴳg₂'  g₂↪⋆g₂' = g₂' , (g₂↪⋆g₂' , ⌞ g₁'≈ᴳg₂' ⌟ᴳ)
