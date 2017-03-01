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

import Concurrent.Calculus as C
open C 𝓛 𝓢
-- open import Concurrent.Calculus 𝓛 𝓢

import Concurrent.Semantics as CS
open CS 𝓛 𝓢
-- open import Concurrent.Semantics 𝓛 𝓢 public

open import Sequential.Erasure 𝓛 A as SE hiding (εᵀ ; εᴾ ; εˢ)
open import Sequential.PINI 𝓛 A as P₂ using (stepᴸ ; stepᴴ-≅ᴴ ; stepᴴ-≅ᴹ ; stepᴴ)

open import Data.Nat as N
--------------------------------------------------------------------------------

open Scheduler.Security.NIˢ 𝓛 A 𝓝 renaming (State to Stateˢ)
open import Scheduler.Base 𝓛

open import Concurrent.Erasure A 𝓝
open import Concurrent.Lemmas A 𝓝

import Concurrent.LowEq
module L₁ = Concurrent.LowEq A 𝓝
open L₁

import Sequential.LowEq renaming (_≈ᵀˢ⟨_⟩_ to _≈ᵀᴴ⟨_⟩_ ; ⌞_⌟ᵀˢ to ⌞_⌟ᵀᴴ ; ⌜_⌝ᵀˢ to ⌜_⌝ᵀᴴ ; ⟨_,_,_⟩ to mk≈ᴾ) hiding (_≈ˢ_)
module L₂  = Sequential.LowEq  𝓛 A
open L₂

import Concurrent.Graph
module G₁ = Concurrent.Graph A 𝓝
open G₁

import Sequential.Graph
module G₂ = Sequential.Graph 𝓛 A

--------------------------------------------------------------------------------

data  _↪⋆-≈ᴳ_ {ls} (g₂ : Global ls) (g₁' : Global ls) : Set where
   Cᴳ : ∀ (g₂' : Global ls) -> g₁' ≈ᴳ g₂' -> g₂ ↪⋆ g₂' -> g₂ ↪⋆-≈ᴳ g₁'

open import Data.Nat
open import Function


-- This is consistent with the fact that our lists are truly mappings
-- they are not defined so becuase they are inconvinient to reason with
postulate _∈ᴸ_ : (l : Label) (ls : List Label) -> l ∈ ls  -- TODO probably can be added to the lattice

lookupᴾ : ∀ {l ls} -> l ∈ ls -> (P : Pools ls) -> ∃ (λ T → l ↦ T ∈ᴾ P)
lookupᴾ here (T C.◅ P) = T , here
lookupᴾ (there q) (T' C.◅ P) = P.map id there (lookupᴾ q P)

-- The scheduler gives me only valid thread id
postulate lookupᵀ : ∀ {l} -> (n : SC.ℕ) (T : Pool l) -> ∃ (λ t → n ↦ t ∈ᵀ T)

-- TODO move to Semantics
postulate stateᴾ : ∀ {l ls τ} (p : Program l ls τ) -> Stateᴾ p

secureStack : ∀ {π l l' τ} -> Stack l π (Mac l' τ) (Mac l τ) -> l' ≡ l
secureStack [] = refl
secureStack (# τ∈π ∷ S) = secureStack S
secureStack (Bind x ∷ S) = refl
secureStack ∙ = refl


open import Sequential.Graph 𝓛 A

aux-sch : ∀ {Σ₁ Σ₂ n₁ n₂ L n H} {l⊑H : L ⊑ H} -> n₁ ≡ n₂ -> Σ₁ ⟶ Σ₂ ↑ S.⟪ L , n ,  Fork H n₁ l⊑H ⟫ ->  Σ₁ ⟶ Σ₂ ↑ S.⟪ L , n ,  Fork H n₂ l⊑H ⟫
aux-sch refl x = x

-- εᴳ-simᴸ₀ : ∀ {L n ls T₂ Ts₂ Σ₂'} {g₁ g₁' g₂ : Global ls} -> (L⊑A : L ⊑ A) (step : (L , n)  ⊢ g₁ ↪ g₁') -> g₁ ≈ᴳ g₂ ->
--            let C.⟨ Σ₁ , Ms₁ , Γ₁ , P₁ ⟩ = g₁
--                C.⟨ Σ₁' , Ms₁' , Γ₁' , P₁' ⟩ = g₁'
--                C.⟨ Σ₂ , Ms₂ , Γ₂ , P₂ ⟩ = g₂ in
--            Σ₂ ⟶ Σ₂' ↑ S.⟪ L , n , getEvent step ⟫ -> Σ₁' ≈ˢ Σ₂' -> L ↦ T₂ ∈ᴾ P₂ -> n ↦ Ts₂ ∈ᵀ T₂  ->
--            (nextPool step) L₁.≈ᴾ⟨ yes L⊑A ⟩ T₂ -> (nextThread step) ≈ᵀᴴ⟨ yes L⊑A ⟩ Ts₂ -> g₂ ↪⋆-≈ᴳ g₁'

-- εᴳ-simᴸ₀ L⊑A (CS.step-∅ {Ts₁ = Ts₁} l∈P t∈T ¬fork step sch u₁ᵀ u₁ᴾ) g₁≈g₂ sch' Σ₁'≈Σ₂' L∈P₂ t∈T₂ T₁≈T₂ Ts₁≈Ts₂
--   with redex-≈ L⊑A (mk≈ᴾ (Ms₁≈Ms₂ g₁≈g₂) (Γ₁≈Γ₂ g₁≈g₂) Ts₁≈Ts₂) step
-- ... | _ , L₂.mk≈ᴾ Ms₁'≈Ms₂' Γ₁'≈Γ₂' Ts₁'≈Ts₂' , step₂ with updateᵀ-≈ L⊑A u₁ᵀ T₁≈T₂ Ts₁'≈Ts₂'
-- ... | T₂' , T₁'≈T₂' , u₂ᵀ with updateᴾ-≈ (yes L⊑A) u₁ᴾ (P₁≈P₂ g₁≈g₂) T₁'≈T₂'
-- ... | P₂' , P₁'≈P₂' , u₂ᴾ = Cᴳ _ L₁.⟨ Σ₁'≈Σ₂' , Ms₁'≈Ms₂' , Γ₁'≈Γ₂' , P₁'≈P₂' ⟩ (step-∅ L∈P₂ t∈T₂ (¬IsForkTS-≈ Ts₁≈Ts₂ ¬fork) step₂ sch' u₂ᵀ u₂ᴾ ∷ [])

-- εᴳ-simᴸ₀ L⊑A (CS.fork l∈P t∈T u₁ᵀ u₁ᴾ H∈P₁ sch u₁ᴾ') L₁.⟨ Σ₁≈Σ₂ , Ms₁≈Ms₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩ sch' Σ₁'≈Σ₂' L∈P₂ t∈T₂ T₁≈T₂
--   (L₂.Kᵀˢ G₂.⟨ G₂.fork l⊑H h⊑A x , x₁ ⟩ G₂.⟨ G₂.fork .l⊑H h⊑A₁ x₂ , x₃ ⟩) with updateᵀ-≈ L⊑A u₁ᵀ T₁≈T₂ (L₂.Kᵀˢ G₂.⟨ Return （） , x₁ ⟩ G₂.⟨ Return （） , x₃ ⟩)
-- ... | T₂' , T₁'≈T₂' , u₂ᵀ with updateᴾ-≈ (yes L⊑A) u₁ᴾ P₁≈P₂ T₁'≈T₂'
-- ... | P₂' , P₁'≈P₂' , u₂ᴾ with memberᴾ-≈ (yes h⊑A) H∈P₁ P₁'≈P₂'
-- ... | Tᴴ₂ , Tᴴ₂≈T₁ᴴ , H∈P₂ with updateᴾ-≈ (yes h⊑A) u₁ᴾ' P₁'≈P₂' (newᵀ-≈ Tᴴ₂≈T₁ᴴ (L₂.Kᵀˢ G₂.⟨ x , [] ⟩ G₂.⟨ x₂ , [] ⟩))
-- ... | P₂'' , P₂''≈P₁'' , uᴾ₂′
--   = Cᴳ _ L₁.⟨ Σ₁'≈Σ₂' , Ms₁≈Ms₂  , Γ₁≈Γ₂ , P₂''≈P₁'' ⟩ (fork L∈P₂ t∈T₂ u₂ᵀ u₂ᴾ H∈P₂ (aux-sch (lengthᵀ-≈ h⊑A Tᴴ₂≈T₁ᴴ) sch') uᴾ₂′ ∷ [])



-- εᴳ-simᴸ₀ L⊑A (CS.fork l∈P t∈T u₁ᵀ u₁ᴾ H∈P₁ sch u₁ᴾ') L₁.⟨ Σ₁≈Σ₂ , MS₁≈MS₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩ sch' Σ₁'≈Σ₂' L∈P₂ t∈T₂ T₁≈T₂ (L₂.Kᵀˢ G₂.⟨ G₂.fork' l⊑H h⋤A x , x₁ ⟩ G₂.⟨ G₂.fork' .l⊑H h⋤A₁ x₂ , x₃ ⟩) with updateᵀ-≈ L⊑A u₁ᵀ T₁≈T₂ (L₂.Kᵀˢ G₂.⟨ Return （） , x₁ ⟩ G₂.⟨ Return （） , x₃ ⟩)
-- ... | T₂' , T₁'≈T₂' , u₂ᵀ with updateᴾ-≈ (yes L⊑A) u₁ᴾ P₁≈P₂ T₁'≈T₂'
-- ... | P₂' , P₁'≈P₂' , u₂ᴾ with memberᴾ-≈ (no h⋤A) H∈P₁ P₁'≈P₂'
-- ... | Tᴴ₂ , Tᴴ₂≈T₁ᴴ , H∈P₂ with id-≈ˢ (lengthᵀ Tᴴ₂) l⊑H L⊑A h⋤A sch'
-- ... | Σ₂'' , sch'' , Σ₂'≈Σ₂'' with updateᴾ-≈ (no h⋤A) u₁ᴾ' P₁'≈P₂' (newᵀ-≈ Tᴴ₂≈T₁ᴴ (L₂.Kᵀˢ ∙ ∙))
-- ... | P₂'' , P₂''≈P₁'' , uᴾ₂′ = Cᴳ _ L₁.⟨ trans-≈ˢ Σ₁'≈Σ₂' Σ₂'≈Σ₂'' , MS₁≈MS₂ , Γ₁≈Γ₂ , P₂''≈P₁'' ⟩ (fork L∈P₂ t∈T₂ u₂ᵀ u₂ᴾ H∈P₂ sch'' uᴾ₂′ ∷ [])

-- εᴳ-simᴸ₀ L⊑A (CS.fork {Tᴴ = T₁ᴴ} l∈P t∈T u₁ᵀ u₁ᴾ H∈P₁ sch u₁ᴾ') L₁.⟨ Σ₁≈Σ₂ , MS₁≈MS₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩ sch' Σ₁'≈Σ₂' L∈P₂ t∈T₂ T₁≈T₂ (L₂.Kᵀˢ G₂.⟨ G₂.fork' l⊑H h⋤A x , x₁ ⟩ G₂.⟨ G₂.fork∙ .l⊑H x₂ , x₃ ⟩) with updateᵀ-≈ L⊑A u₁ᵀ T₁≈T₂ (L₂.Kᵀˢ G₂.⟨ Return （） , x₁ ⟩ G₂.⟨ Return （） , x₃ ⟩)
-- ... | T₂' , T₁'≈T₂' , u₂ᵀ with updateᴾ-≈ (yes L⊑A) u₁ᴾ P₁≈P₂ T₁'≈T₂'
-- ... | P₂' , P₁'≈P₂' , u₂ᴾ with memberᴾ-≈ (no h⋤A) H∈P₁ P₁'≈P₂'
-- ... | Tᴴ₂ , Tᴴ₂≈T₁ᴴ , H∈P₂ with step-≈ˢ l⊑H L⊑A h⋤A sch'
-- ... | Σ₂'' , sch'' , Σ₂'≈Σ₂'' with updateᴾ-≈ {T₂ = T₁ᴴ} (no h⋤A) u₁ᴾ' P₁'≈P₂' (Kᴾ ∙ ∙)
-- ... | P₂'' , P₁''≈P₂'' , uᴾ₂′
--   = Cᴳ _ L₁.⟨ (trans-≈ˢ Σ₁'≈Σ₂' Σ₂'≈Σ₂'') , MS₁≈MS₂ , Γ₁≈Γ₂ , trans-≈ᴾ P₁''≈P₂'' L₁.map-⌜ sym (updateᴾ∙ h⋤A uᴾ₂′) ⌝ᴾ ⟩ (fork∙ L∈P₂ t∈T₂  u₂ᵀ u₂ᴾ sch'' ∷ [])

-- εᴳ-simᴸ₀ {ls = ls} L⊑A (CS.fork∙ {H} {tᴴ = t₁ᴴ} {P₂ = P₁'} l∈P t∈T u₁ᵀ u₁ᴾ sch) L₁.⟨ Σ₁≈Σ₂ , MS₁≈MS₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩ sch' Σ₁'≈Σ₂' L∈P₂ t∈T₂ T₁≈T₂ (L₂.Kᵀˢ G₂.⟨ G₂.fork∙ l⊑H x , x₁ ⟩ G₂.⟨ G₂.fork' .l⊑H h⋤A x₂ , x₃ ⟩) with updateᵀ-≈ L⊑A u₁ᵀ T₁≈T₂ (L₂.Kᵀˢ G₂.⟨  Return （） , x₁ ⟩ G₂.⟨ Return （） , x₃ ⟩)
-- ... | T₂' , T₁'≈T₂' , u₂ᵀ with updateᴾ-≈ (yes L⊑A) u₁ᴾ P₁≈P₂ T₁'≈T₂'
-- ... | P₂' , P₁'≈P₂' , u₂ᴾ with lookupᴾ (H ∈ᴸ ls) P₁'
-- ... | T₁ᴴ , H∈P₁ with memberᴾ-≈ (no h⋤A) H∈P₁ P₁'≈P₂'  -- TODO Won't need this if we add H∈P₁ to fork∙
-- ... | T₂ᴴ , T₂ᴴ≈T₁ᴴ , H∈P₂ with fork-≈ˢ (lengthᵀ T₂ᴴ) l⊑H L⊑A h⋤A sch'
-- ... | Σ₂'' , sch'' , Σ₂'≈Σ₂'' with updateᴾ H∈P₁ (T₁ᴴ ▻ mkᵀᴴ t₁ᴴ [])
-- ... | P₁'' , u₁ᴾ′ with updateᴾ-≈ {T₂ = T₂ᴴ ▻ mkᵀᴴ _ []} (no h⋤A) u₁ᴾ′ P₁'≈P₂' (Kᴾ ∙ ∙)
-- ... | P₂'' , P₁''≈P₂'' , u₂ᴾ′
--   = Cᴳ _ L₁.⟨ trans-≈ˢ Σ₁'≈Σ₂' Σ₂'≈Σ₂'' , MS₁≈MS₂ , Γ₁≈Γ₂ , trans-≈ᴾ P₁'≈P₂' L₁.map-⌜ updateᴾ∙ h⋤A u₂ᴾ′ ⌝ᴾ ⟩ (fork L∈P₂ t∈T₂ u₂ᵀ u₂ᴾ H∈P₂ sch'' u₂ᴾ′ ∷ [])

-- εᴳ-simᴸ₀ L⊑A (CS.fork∙ l∈P t∈T u₁ᵀ u₁ᴾ sch) L₁.⟨ Σ₁≈Σ₂ , MS₁≈MS₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩ sch' Σ₁'≈Σ₂' L∈P₂ t∈T₂ T₁≈T₂ (L₂.Kᵀˢ G₂.⟨ G₂.fork∙ l⊑H x , x₁ ⟩ G₂.⟨ G₂.fork∙ .l⊑H x₂ , x₃ ⟩) with updateᵀ-≈ L⊑A u₁ᵀ T₁≈T₂ (L₂.Kᵀˢ G₂.⟨ (Return （）) , x₁ ⟩ G₂.⟨ (Return （）) , x₃ ⟩)
-- ... | T₂' , T₁'≈T₂' , u₂ᵀ with updateᴾ-≈ (yes L⊑A) u₁ᴾ P₁≈P₂ T₁'≈T₂'
-- ... | P₂' , P₁'≈P₂' , u₂ᴾ
--   = Cᴳ _ L₁.⟨ Σ₁'≈Σ₂' , MS₁≈MS₂ , Γ₁≈Γ₂ , P₁'≈P₂' ⟩ (fork∙ L∈P₂ t∈T₂ u₂ᵀ u₂ᴾ sch' ∷ [])

-- εᴳ-simᴸ₀ L⊑A (skip l∈P t∈T stuck sch) L₁.⟨ Σ₁≈Σ₂ , MS₁≈MS₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩ sch' Σ₁'≈Σ₂' L∈P₂ t∈T₂ T₁≈T₂ Ts₁≈Ts₂
--   =  Cᴳ _ L₁.⟨ Σ₁'≈Σ₂' , MS₁≈MS₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩ (skip L∈P₂ t∈T₂ (stuck-≈ L⊑A (L₂.mk≈ᴾ MS₁≈MS₂ Γ₁≈Γ₂ Ts₁≈Ts₂) stuck) sch' ∷ [])

-- εᴳ-simᴸ₀ L⊑A (CS.done l∈P t∈T don sch) L₁.⟨ Σ₁≈Σ₂ , Ms₁≈Ms₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩ sch' Σ₁'≈Σ₂' L∈P₂ t∈T₂ T₁≈T₂ Ts₁≈Ts₂
--   = Cᴳ _ L₁.⟨ Σ₁'≈Σ₂' , Ms₁≈Ms₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩ (done L∈P₂ t∈T₂ (done-≈ L⊑A Ts₁≈Ts₂ don) sch' ∷ [])

εᴳ-simᴸ▵ : ∀ {L H n m n₁ n₂ ls T₂ Ts₂} {g₁ g₁' g₂ : Global ls} -> L ⊑ A -> (L , n)  ⊢ g₁ ↪ g₁' -> g₁ ≈ᴳ-⟨ n₁ , N.suc n₂ ⟩ g₂ ->
              H ⋤ A -> H ↦ T₂ ∈ᴾ (C.P g₂) -> m ↦ Ts₂ ∈ᵀ T₂ -> Stateᴾ (mkᴾ (C.Ms g₂) (C.Γ g₂) Ts₂) ->
             ((e : Event H) → ∃ (λ Σ₂' →  C.Σ g₁ ≈ˢ-⟨ n₁ , n₂ ⟩ Σ₂' × (C.Σ g₂) ⟶ Σ₂' ↑ S.⟪ H , m , e ⟫)) ->
             g₂ ↪⋆-≈ᴳ g₁'

εᴳ-simᴸ⋆ : ∀ {L n n₁ ls} {g₁ g₁' g₂ : Global ls} (n₂ : SC.ℕ) -> L ⊑ A -> (L , n)  ⊢ g₁ ↪ g₁' -> g₁ ≈ᴳ-⟨ n₁ , n₂ ⟩ g₂ -> g₂ ↪⋆-≈ᴳ g₁'


εᴳ-simᴸ▵ {n₂ = n₂} L⊑A step L₁.⟨ Σ₁≈Σ₂ , MS₁≈MS₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩ H⋤A H∈P₂ Ts∈T₂ (isD don) nextˢ with nextˢ Done
... | Σ₂' , Σ₂≈Σ₂' , sch' with εᴳ-simᴸ⋆ n₂ L⊑A step L₁.⟨ Σ₂≈Σ₂' , MS₁≈MS₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩
... | Cᴳ g₂' L₁.⟨ Σ₂'≈Σ₂'' , Ms₁'≈Ms₂'' , Γ₂'≈Γ₂'' , P₂'≈P₂'' ⟩ ss
  = Cᴳ _ L₁.⟨ Σ₂'≈Σ₂'' , Ms₁'≈Ms₂'' , Γ₂'≈Γ₂'' , P₂'≈P₂'' ⟩ ((done H∈P₂ Ts∈T₂ don sch') ∷ ss)
εᴳ-simᴸ▵ {n₂ = n₂} L⊑A step L₁.⟨ Σ₁≈Σ₂ , MS₁≈MS₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩ H⋤A H∈P₂ Ts∈T₂ (SS.isR (SS.Step {p' = p'} step₂)) nextˢ
  with updateᵀ Ts∈T₂ (TS p')
... | T₂' , uᵀ with updateᴾ H∈P₂ T₂'
... | P₂' , uᴾ with nextˢ Step
... | Σ₂' , Σ₂≈Σ₂' , sch'  with εᴳ-simᴸ⋆ n₂ L⊑A step L₁.⟨ Σ₂≈Σ₂' , trans-≈ᴹ MS₁≈MS₂ L₂.map-⌜ stepᴴ-≅ᴹ H⋤A step₂ ⌝ᴹ , trans-≈ᴴ Γ₁≈Γ₂ L₂.map-⌜ stepᴴ-≅ᴴ H⋤A step₂ ⌝ᴴ , trans-≈ᴾ P₁≈P₂ L₁.map-⌜ updateᴾ∙ H⋤A uᴾ ⌝ᴾ ⟩
... | Cᴳ g₂'' g₂'≈g₂'' ss  = Cᴳ _ g₂'≈g₂'' (step-∅ H∈P₂ Ts∈T₂ (Redex-¬IsForkTS (SS.Step step₂)) step₂ sch' uᵀ uᴾ ∷ ss)

εᴳ-simᴸ▵ {n₂ = n₂} L⊑A step L₁.⟨ Σ₁≈Σ₂ , MS₁≈MS₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩ H⋤A H∈P₂ Ts∈T₂ (SS.isS isStuck) nextˢ with nextˢ Skip
... | Σ₂' , Σ₂≈Σ₂' , sch' with εᴳ-simᴸ⋆ n₂ L⊑A step L₁.⟨ Σ₂≈Σ₂' , MS₁≈MS₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩
... | Cᴳ g₂' g₂'≈g₂'' ss = Cᴳ _ g₂'≈g₂'' (skip H∈P₂ Ts∈T₂ isStuck sch' ∷ ss)

εᴳ-simᴸ▵ {n₂ = n₂} {ls = ls} {Ts₂ = mkᵀᴴ (fork {h = h} .p .t₂ᴴ) S₂} L⊑A step L₁.⟨ Σ₁≈Σ₂ , MS₁≈MS₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩ H⋤A H∈P₂ Ts∈T₂ (SS.isF (SS.isForkTS (SC.Fork p t₂ᴴ))) nextˢ  rewrite secureStack S₂ with updateᵀ Ts∈T₂ (mkᵀᴴ (Return _ SC.（）) S₂)
... | T₂' , uᵀ with updateᴾ H∈P₂ T₂'
... | P₂' , uᴾ with lookupᴾ (h ∈ᴸ ls) P₂'
... | T₂ᴴ , H∈P₂' with updateᴾ H∈P₂' (T₂ᴴ ▻ (mkᵀᴴ t₂ᴴ []))
... | P₂'' , u₂ᴾ with nextˢ (Fork h (lengthᵀ T₂ᴴ) p)
... | Σ₂' , Σ₂'≈Σ₂'' , sch' with εᴳ-simᴸ⋆ n₂ L⊑A step L₁.⟨ Σ₂'≈Σ₂'' ,  MS₁≈MS₂ , Γ₁≈Γ₂ , trans-≈ᴾ (trans-≈ᴾ P₁≈P₂ L₁.map-⌜ updateᴾ∙ H⋤A uᴾ ⌝ᴾ) L₁.map-⌜ updateᴾ∙ (trans-⋤ p H⋤A) u₂ᴾ ⌝ᴾ  ⟩
... | Cᴳ g₂'' g₂≈g₂'' ss = Cᴳ _ g₂≈g₂'' (fork H∈P₂ Ts∈T₂ uᵀ uᴾ H∈P₂' sch' u₂ᴾ ∷ ss)

εᴳ-simᴸ▵ L⊑A step g₁≈g₂ H⋤A H∈P₂ Ts∈T₂ (SS.isF (SS.isForkTS (SC.Fork∙ p t))) nextˢ = {!!}

--   -- fork∙
-- εᴳ-simᴸ⋆ (suc n₂) Σ₁≈Σ₂ L⊑A step ⟨ Σ₁≈Σ₃ , P₁≈P₂ , Γ₁≈Γ₂ ⟩
--   | Σ₂' , H , m , H⋤A , Σ₂≈Σ₂' , nextˢ | T₂ , T∈P₂
--   | C.⟨ ._ , S₂ ⟩ , t∈T₂ | isR (Step {p' = ⟨ Γ₂' , t₂' , S₂' ⟩} step₂) | yes (Fork∙ l⊑H t₂ᴴ)
--     rewrite secureStack S₂ with updateᵀ t∈T₂ ⟨ t₂' , S₂' ⟩
-- ... | T₂' , uᵀ with updateᴾ T∈P₂ T₂'
-- ... | P₂' , uᴾ with ⟨ forget Σ₂≈Σ₂' , trans-≈ᴾ P₁≈P₂ L₁.⌜ updateᴾ∙ H⋤A uᴾ ⌝ᴾ , trans-≈ᴴ Γ₁≈Γ₂ ⌜ stepᴴ-Γ H⋤A step₂ ⌝ᴴ ⟩
-- ... | g₂≈g₂' with εᴳ-simᴸ⋆ n₂ Σ₂≈Σ₂' L⊑A step g₂≈g₂'
-- ... | Cᴳ g₂'' g₂'≈g₂'' ss = Cᴳ _ g₂'≈g₂'' (fork∙ T∈P₂ t∈T₂ step₂ uᵀ uᴾ (nextˢ Step) ∷ ss)


-- εᴳ-simᴸ⋆ N.zero L⊑A step L₁.⟨ Σ₁≈Σ₂ , Ms₁≈Ms₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩ with squareˢ L⊑A Σ₁≈Σ₂ (getSchStep step)
-- εᴳ-simᴸ⋆ N.zero L⊑A step L₁.⟨ Σ₁≈Σ₂ , Ms₁≈Ms₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩ | Σ₂' , sch' , Σ₁'≈Σ₂' with memberᴾ-≈ (yes L⊑A) (next-∈ᵀ step) P₁≈P₂
-- ... | T₂ , T₁≈T₂ , l∈P₂ with memberᵀ-≈ L⊑A (next-∈ᴾ step) T₁≈T₂
-- ... | _ , Ts₁≈Ts₂ , t∈T₂ = εᴳ-simᴸ₀ L⊑A step (forgetᴳ L₁.⟨ Σ₁≈Σ₂ , Ms₁≈Ms₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩) sch' Σ₁'≈Σ₂' l∈P₂ t∈T₂ T₁≈T₂ Ts₁≈Ts₂

εᴳ-simᴸ⋆ N.zero L⊑A step L₁.⟨ Σ₁≈Σ₂ , Ms₁≈Ms₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩ = {!!}

εᴳ-simᴸ⋆ {ls = ls} {g₂ = g₂} (N.suc n₂) L⊑A step g₁≈g₂ with triangleˢ L⊑A (get≈ˢ g₁≈g₂) (getSchStep step)
... | H , m , H⋤A , nextˢ  with lookupᴾ (H ∈ᴸ ls) (P g₂)
... | T₂ , T∈P₂ with lookupᵀ m T₂
... | Ts₂ , t∈T₂ = εᴳ-simᴸ▵ L⊑A step g₁≈g₂ H⋤A T∈P₂ t∈T₂ (stateᴾ (mkᴾ (C.Ms g₂) (C.Γ g₂) Ts₂)) nextˢ

εᴳ-sim⋆ : ∀ {l n ls} {g₁ g₁' g₂ : Global ls} -> Dec (l ⊑ A) -> ( l , n ) ⊢ g₁ ↪ g₁' -> g₁ ≈ᴳ g₂ -> g₂ ↪⋆-≈ᴳ g₁'
εᴳ-sim⋆ (yes L⊑A) step x = εᴳ-simᴸ⋆ _ L⊑A step (alignᴳ x)
εᴳ-sim⋆ {g₁ = g₁} {g₁' = g₁'} {g₂ = g₂} (no H⋤A) stepᴴ g₁≈g₂ = Cᴳ g₂ ( trans-≈ᴳ (sym-≈ᴳ (⌜ εᴳ-simᴴ H⋤A stepᴴ ⌝ᴳ)) g₁≈g₂) []
