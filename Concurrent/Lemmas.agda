import Lattice as L₁
import Scheduler as S
open import Scheduler.Security

module Concurrent.Lemmas {𝓛 : L₁.Lattice} {𝓢 : S.Scheduler 𝓛} (A : L₁.Label 𝓛) (𝓝 : NIˢ 𝓛 A 𝓢) where

open import Data.Nat as N
open import Relation.Nullary
open import Types 𝓛

open import Sequential.Calculus 𝓛 renaming (⟨_,_,_⟩ to mkᴾ ; ⟨_,_⟩ to mkᵀ) hiding (Ms ; Γ)
open import Sequential.Semantics 𝓛
open import Sequential.Security.Graph 𝓛 A renaming (⟨_,_⟩ to Eᵗ)
open import Sequential.Security.LowEq 𝓛 A renaming (⟨_,_,_⟩ to is≈ᴾ ; ⟨_,_⟩ to is≈ᵗ)
open _≈ᴾ⟨_⟩_
open import Sequential.Security.PINI 𝓛 A

import Concurrent.LowEq as L hiding (⌜_⌝ᴾ ; ⌞_⌟ᴾ) renaming ( ⟨_,_,_,_⟩ to is≈ᴳ) --  ; Σ₁≈Σ₂′ to Σ₁≈Σ₂ ; Ms₁≈Ms₂′ to Ms₁≈Ms₂ ; Γ₁≈Γ₂′ to Γ₁≈Γ₂ ; P₁≈P₂′ to P₁≈P₂)
open L A 𝓝
open import Concurrent.Calculus 𝓛 𝓢 renaming (⟨_,_,_,_⟩ to mkᴳ)

import Concurrent.Semantics as CS
open CS 𝓛 𝓢

open import Concurrent.Valid 𝓛 𝓢 as V hiding (memberᴾ)

open Scheduler.Security.NIˢ 𝓛 A 𝓝 renaming (State to Stateˢ)

open import Data.Product
open import Data.Empty

postulate redexᴳ-≈ : ∀ {l i n ls} {g₁ g₂ g₁' : Global ls} {{v₁ : validᴳ g₁}} {{v₂ : validᴳ g₂}} -> l ⊑ A -> g₁ ≈ᴳ-⟨ i , 0 ⟩ g₂ -> ( l , n ) ⊢ g₁ ↪ g₁' -> Redexᴳ ( l , n ) g₂
-- redexᴳ-≈ {{ v₂ = Ms₂ⱽ , Γ₂ⱽ , Ps₂ⱽ }} l⊑A (L.is≈ᴳ Σ₁≈Σ₂ Ms₁≈Ms₂ Γ₁≈Γ₂ Ps₁≈Ps₂) (CS.step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ)
--   with memberᴾ-≈  (yes l⊑A) l∈P Ps₁≈Ps₂
-- ... | _ , P₁≈P₂' , l∈P₂  with memberᵀ-≈ t∈T P₁≈P₂'
-- ... | _ , T₁≈T₂ , t∈T₂ with is≈ᴾ Ms₁≈Ms₂ Γ₁≈Γ₂ T₁≈T₂
-- ... | p₁≈p₂ with redex-≈ {l⊑A = l⊑A} {{ Ms₂ⱽ , Γ₂ⱽ , V.memberᴾ (memberᴾˢ Ps₂ⱽ l∈P₂) t∈T₂ }} p₁≈p₂ (Step step)
-- ... | Step {p' = p₂'} step' with redex-≈ˢ l⊑A sch Σ₁≈Σ₂
-- ... | _ , sch' with updateᵀ-≈ P₁≈P₂' (Ts₁≈Ts₂ ⌜ pini' (yes l⊑A) ⌞ p₁≈p₂ ⌟ᴾ step step' ⌝ᴾ) uᵀ
-- ... | _ , p₁≈p₂' , uᵀ'  with updateᴾ-≈ Ps₁≈Ps₂ p₁≈p₂' uᴾ
-- ... | _ , _ , uᴾ'
--   = CS.Step (step-∅ l∈P₂ t∈T₂ (¬IsForkTS-≈ T₁≈T₂ ¬fork) step' sch' uᵀ' uᴾ')
-- redexᴳ-≈ {{Ms₁ⱽ , Γ₁ⱽ , Ps₁ⱽ}} {{Ms₂ⱽ , Γ₂ⱽ , Ps₂ⱽ }} l⊑A (L.is≈ᴳ Σ₁≈Σ₂ Ms₁≈Ms₂ Γ₁≈Γ₂ Ps₁≈Ps₂) (CS.fork {tᴴ = tᴴ} l∈P t∈T uᵀ u₁ᴾ H∈P sch u₂ᴾ)
--   with memberᴾ-≈  (yes l⊑A) l∈P Ps₁≈Ps₂
-- ... | _ , T₁≈T₂' , l∈P₂  with memberᵀ-≈ t∈T T₁≈T₂'
-- ... | _ , (Kᵀˢ (Eᵗ e₁ S₁ᴱ) (Eᵗ e₂ S₂ᴱ)) , t∈T₂
--   with fork-≈' {{proj₁ (V.memberᴾ (memberᴾˢ Ps₁ⱽ l∈P) t∈T )}} {{proj₁ (V.memberᴾ (memberᴾˢ Ps₂ⱽ l∈P₂) t∈T₂ )}} (is≈ᵗ e₁ e₂) (Fork _ _)
-- ... | isFork-≈ {t₂ = tᴴ'} t₁ᴴ≈t₂ᴴ with updateᵀ-≈ T₁≈T₂' (Kᵀˢ (Eᵗ (Return _) S₁ᴱ) (Eᵗ (Return _) S₂ᴱ)) uᵀ
-- ... | _ , P₁≈P₂ , uᵀ'  with updateᴾ-≈ Ps₁≈Ps₂ P₁≈P₂ u₁ᴾ
-- ... | _ , Ps₁≈Ps₂' , u₁ᴾ' with memberᴾ-≈ (_ ⊑? A) H∈P Ps₁≈Ps₂'
-- ... | _ , T₁≈T₂ , H∈P₂  with redex-≈ˢ l⊑A sch Σ₁≈Σ₂
-- ... | _ , sch' with updateᴾ-≈ Ps₁≈Ps₂' (newᵀ-≈ T₁≈T₂ (newᵀˢ-≈ t₁ᴴ≈t₂ᴴ)) u₂ᴾ
-- ... | _ , Ps₁≈Ps₂'' , u₂ᴾ'
--   = Step (fork l∈P₂ t∈T₂ uᵀ' u₁ᴾ' H∈P₂ {!sch'!} u₂ᴾ') -- we need to account for high thread-pools with different number of threads.
-- redexᴳ-≈ {{_ , _ , Psⱽ}} l⊑A g₁≈g₂ (CS.fork∙ l∈P t∈T uᵀ uᴾ sch) = ⊥-elim (proj₁ (V.memberᴾ (memberᴾˢ Psⱽ l∈P) t∈T))
-- redexᴳ-≈ {{Ms₁ⱽ , Γ₁ⱽ , Ps₁ⱽ}} l⊑A (L.is≈ᴳ Σ₁≈Σ₂ Ms₁≈Ms₂ Γ₁≈Γ₂ Ps₁≈Ps₂) (CS.skip l∈P t∈T stuck sch)
--   with memberᴾ-≈  (yes l⊑A) l∈P Ps₁≈Ps₂
-- ... | _ , P₁≈P₂' , l∈P₂  with memberᵀ-≈ t∈T P₁≈P₂'
-- ... | _ , T₁≈T₂ , t∈T₂ with redex-≈ˢ l⊑A sch Σ₁≈Σ₂
-- ... | _ , sch' = CS.Step (skip l∈P₂ t∈T₂ (stuck-≈ {{Ms₁ⱽ , Γ₁ⱽ , V.memberᴾ (memberᴾˢ Ps₁ⱽ l∈P) t∈T }} (is≈ᴾ Ms₁≈Ms₂ Γ₁≈Γ₂ T₁≈T₂) stuck) sch')
-- redexᴳ-≈ l⊑A (L.is≈ᴳ Σ₁≈Σ₂ Ms₁≈Ms₂ Γ₁≈Γ₂ Ps₁≈Ps₂) (CS.done l∈P t∈T don sch)
--   with memberᴾ-≈  (yes l⊑A) l∈P Ps₁≈Ps₂
-- ... | _ , P₁≈P₂' , l∈P₂  with memberᵀ-≈ t∈T P₁≈P₂'
-- ... | _ , T₁≈T₂ , t∈T₂ with redex-≈ˢ l⊑A sch Σ₁≈Σ₂
-- ... | _ , sch' = CS.Step (done l∈P₂ t∈T₂ (done-≈ T₁≈T₂ don) sch')
