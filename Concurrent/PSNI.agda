import Lattice as L
import Scheduler as S
open import Scheduler.Security


module Concurrent.PSNI {𝓛 : L.Lattice} {𝓢 : S.Scheduler 𝓛} (A : L.Label 𝓛) (𝓝 : NIˢ 𝓛 A 𝓢) where

open import Data.Product as P
open import Data.Nat
open import Types 𝓛

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Concurrent.Calculus 𝓛 𝓢 as C hiding (lookupᴾ)
open import Concurrent.Semantics 𝓛 𝓢
open import Concurrent.Simulation A 𝓝
open import Concurrent.Lemmas A 𝓝
open import Concurrent.Determinism 𝓛 𝓢

import Concurrent.LowEq
module L₁ = Concurrent.LowEq A 𝓝
open L₁


open Scheduler.Security.NIˢ 𝓛 A 𝓝 hiding (State)
open import Scheduler.Base 𝓛

open import Sequential.Security.LowEq 𝓛 A using (trans-≈ᴹ ; trans-≈ᴴ)

open import Concurrent.Valid 𝓛 𝓢 as V hiding (memberᴾ ; updateᴾ)


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
εᴳ-simᴸ⋆ zero L⊑A step g₁≈g₂ with redexᴳ-≈ L⊑A g₁≈g₂ step
... | Step step' = Cᴳ _ (squareᴸ L⊑A (forgetᴳ g₁≈g₂) step step') (step' ∷ [])
εᴳ-simᴸ⋆ {{v₂ = v₂}} (suc n₂) L⊑A step g₁≈g₂  with redexᴳ-≈ᴴ L⊑A g₁≈g₂ step
... | (H , m) , (Step step') with triangleᴴ L⊑A g₁≈g₂ step step'
... | g₁≈g₂' with εᴳ-simᴸ⋆ {{v₂ = valid↪ step' v₂}} n₂ L⊑A step g₁≈g₂'
... | Cᴳ g₂'' g₁≈g₂'' ss = Cᴳ g₂'' g₁≈g₂'' (step' ∷ ss)

εᴳ-sim⋆ : ∀ {l n ls} {g₁ g₁' g₂ : Global ls} {{v₁ : validᴳ g₁}} {{v₂ : validᴳ g₂}}
            -> Dec (l ⊑ A) -> ( l , n ) ⊢ g₁ ↪ g₁' -> g₁ ≈ᴳ g₂ -> g₂ ↪⋆-≈ᴳ g₁'
εᴳ-sim⋆ (yes L⊑A) step x = εᴳ-simᴸ⋆ _ L⊑A step (alignᴳ x)
εᴳ-sim⋆ {g₁ = g₁} {g₁' = g₁'} {g₂ = g₂} (no H⋤A) stepᴴ g₁≈g₂
  = Cᴳ g₂ ( trans-≈ᴳ (sym-≈ᴳ (⌜ εᴳ-simᴴ H⋤A stepᴴ ⌝ᴳ)) g₁≈g₂) []

psni : ∀ {l n ls} {g₁ g₁' g₂ : Global ls} {{v₁ : validᴳ g₁}} {{v₂ : validᴳ g₂}}
         -> g₁ ≅ᴳ g₂ -> (l , n)  ⊢ g₁ ↪ g₁' -> ∃ (λ g₂' → g₂ ↪⋆ g₂' × g₁' ≅ᴳ g₂')
psni {l} eq s with εᴳ-sim⋆ (l ⊑? A) s ⌜ eq ⌝ᴳ
psni eq s | Cᴳ g₂' g₁'≈ᴳg₂'  g₂↪⋆g₂' = g₂' , (g₂↪⋆g₂' , ⌞ g₁'≈ᴳg₂' ⌟ᴳ)

--------------------------------------------------------------------------------
