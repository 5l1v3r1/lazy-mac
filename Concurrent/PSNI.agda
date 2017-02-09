import Lattice as L
import Scheduler as S
open import Scheduler.Security


module Concurrent.PSNI {𝓛 : L.Lattice} {𝓢 : S.Scheduler 𝓛} (A : L.Label 𝓛) (𝓝 : NIˢ 𝓛 A 𝓢) where

open import Types 𝓛

open import Data.Product using (∃ ; _×_ ; proj₁ ; proj₂ )
import Data.Product as P

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
--------------------------------------------------------------------------------
-- Temporarily side-step bug #2245

import Sequential.Calculus as SC
open SC 𝓛

open import Sequential.Semantics 𝓛

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
open import Concurrent.Lemmas A 𝓝

import Concurrent.LowEq as L₁
open L₁ A 𝓝

import Sequential.LowEq  𝓛 A as L₂
open L₂

import Sequential.Graph  as G
open G 𝓛 A

--------------------------------------------------------------------------------

data  _↪⋆-≈ᴳ_ {ls} (g₂ : Global ls) (g₁' : Global ls) : Set where
   Cᴳ : ∀ (g₂' : Global ls) -> g₁' ≈ᴳ g₂' -> g₂ ↪⋆ g₂' -> g₂ ↪⋆-≈ᴳ g₁'

open import Data.Nat

-- data PSNI {ls} {g₁ g₁' : Global ls} (s : g₁ ↪ g₁') (g₂ : Global) : Set where
--   Pᴳ : ∀ {g₂'} -> g₂ ↪⋆ g₂' -> g₁' ≈ g₂ -> PSNI s g₂

memberᴾ-≈ : ∀ {ls L} {T₁ : Pool L} {P₁ P₂ : Pools ls} -> (L⊑A : L ⊑ A) -> L ↦ T₁ ∈ᴾ P₁ -> P₁ ≈ᴾ P₂ -> ∃ (λ T₂ -> T₁ ≈ᵀ⟨ yes L⊑A ⟩ T₂ × L ↦ T₂ ∈ᴾ P₂)
memberᴾ-≈ = {!!}

memberᵀ-≈ : ∀ {n L} {T₁ T₂ : Pool L} {t₁ : Thread L} -> (L⊑A : L ⊑ A) -> n ↦ t₁ ∈ᵀ T₁ -> T₁ ≈ᵀ⟨ yes L⊑A ⟩ T₂ -> ∃ (λ t₂ → (t₁ ≈ᵗ t₂) × n ↦ t₂ ∈ᵀ T₂)
memberᵀ-≈ = {!!}

updateᵀ-≈ : ∀ {n L} {T₁ T₁' T₂ : Pool L} {t₁ t₂ : Thread L} -> (L⊑A : L ⊑ A) -> T₁' ≔ T₁ [ n ↦ t₁ ]ᵀ ->
            T₁ ≈ᵀ⟨ yes L⊑A ⟩ T₂ -> t₁ ≈ᵗ t₂ -> ∃ (λ T₂' → T₁' ≈ᵀ⟨ yes L⊑A ⟩ T₂'  × T₂' ≔ T₂ [ n ↦ t₂ ]ᵀ)
updateᵀ-≈ = {!!}

updateᴾ-≈ : ∀ {L ls} {P₁ P₂ P₁' : Pools ls} {T₁ T₂ : Pool L}  (L⊑A : L ⊑ A) -> P₁' ≔ P₁ [ L ↦ T₁ ]ᴾ ->
            P₁ ≈ᴾ P₂ -> T₁ ≈ᵀ⟨ yes L⊑A ⟩ T₂ -> ∃ (λ P₂' → P₁' ≈ᴾ P₂'  × P₂' ≔ P₂ [ L ↦ T₂ ]ᴾ)
updateᴾ-≈ = {!!}


val-≈ : ∀ {π τ} {t₁ t₂ : Term π τ} -> t₁ L₂.≈ᵀ t₂ -> Value t₁ -> Value t₂
val-≈ = {!!}

stuck-≈ : ∀ {l ls τ} {p₁ p₂ : Program l ls τ} (l⊑A : l ⊑ A) -> p₁ L₂.≈ᴾ⟨ (yes l⊑A) ⟩ p₂ -> Stuckᴾ p₁ -> Stuckᴾ p₂
stuck-≈ = {!!}

¬fork-≈ : ∀ {π τ} {t₁ t₂ : Term π τ} -> t₁ L₂.≈ᵀ t₂ -> ¬ (IsFork t₁) -> ¬ (IsFork t₂)
¬fork-≈ = {!!}

redex-≈ : ∀ {l ls τ} {p₁ p₁' p₂ : Program l ls τ} -> (l⊑A : l ⊑ A) -> p₁ L₂.≈ᴾ⟨ (yes l⊑A) ⟩ p₂ -> p₁ ⟼ p₁' ->
            ∃ (λ p₂' -> (p₁' L₂.≈ᴾ⟨ yes l⊑A ⟩ p₂') × (p₂ ⟼ p₂'))
redex-≈ = {!!}

lengthᵀ-≈ : ∀ {l} {T₁ T₂ : Pool l} -> (l⊑A : l ⊑ A) -> T₁ ≈ᵀ⟨ yes l⊑A ⟩ T₂ -> lengthᵀ T₁ ≡ lengthᵀ T₂
lengthᵀ-≈ = {!!}

newᵀ-≈ : ∀ {l} {T₁ T₂ : Pool l} {t₁ t₂ : Thread l} -> (l⊑A : l ⊑ A) -> T₁ ≈ᵀ⟨ yes l⊑A ⟩ T₂ -> t₁ ≈ᵗ t₂ -> (T₁ ▻ t₁) ≈ᵀ⟨ yes l⊑A ⟩ (T₂ ▻ t₂)
newᵀ-≈ = {!!}

open import Sequential.Graph 𝓛 A

εᴳ-simᴸ⋆ : ∀ {L n n₁ ls} {Σ₁ Σ₁' Σ₂ : Stateˢ} {Γ₁ Γ₁' Γ₂ : Heaps ls} {P₁ P₁' P₂ : Pools ls} ->
               (n₂ : SC.ℕ) ->
               Σ₁ ≈ˢ-⟨ n₁ , n₂ ⟩ Σ₂ ->
               let g₁ = ⟨ Σ₁ , Γ₁ , P₁ ⟩
                   g₁' = ⟨ Σ₁' , Γ₁' , P₁' ⟩
                   g₂ = ⟨ Σ₂ , Γ₂ , P₂ ⟩ in
               L ⊑ A -> (L P., n)  ⊢ g₁ ↪ g₁' -> g₁ ≈ᴳ g₂ -> g₂ ↪⋆-≈ᴳ g₁'

εᴳ-simᴸ⋆ SC.zero Σ₁≈Σ₂ L⊑A step g₁'≈g₂' with squareˢ L⊑A Σ₁≈Σ₂ (getSchStep step)

εᴳ-simᴸ⋆ zero _ L⊑A (CS.step-∅ l∈P₁ t∈T₁ ¬fork₁ step₁ sch₁ u₁ᵀ u₁ᴾ) L₁.⟨ Σ₁≈Σ₂ , P₁≈P₂ , Γ₁≈Γ₂ ⟩
    | Σ₂' P., sch' P., Σ₁'≈Σ₂' with memberᴾ-≈ L⊑A l∈P₁ P₁≈P₂
... | T₂ P., T₁≈T₂ P., l∈P₂ with memberᵀ-≈ L⊑A t∈T₁ T₁≈T₂
... | _ P., ⟨ t₁≈t₂ , S₁≈S₂ ⟩ P., t∈T₂ with redex-≈ L⊑A L₂.⟨ Γ₁≈Γ₂ , t₁≈t₂ , S₁≈S₂ ⟩ step₁
... | _ P., L₂.⟨ Γ₁'≈Γ₂' , t₁'≈t₂' , S₁'≈S₂' ⟩  P., step₂ with updateᵀ-≈ L⊑A u₁ᵀ T₁≈T₂ L₁.⟨ t₁'≈t₂' , S₁'≈S₂' ⟩
... | T₂' P., T₁'≈T₂' P., u₂ᵀ with updateᴾ-≈ L⊑A u₁ᴾ P₁≈P₂ T₁'≈T₂'
... | P₂' P., P₁'≈P₂' P., u₂ᴾ
  = Cᴳ _ L₁.⟨ Σ₁'≈Σ₂' , P₁'≈P₂' , Γ₁'≈Γ₂' ⟩ (step-∅ l∈P₂ t∈T₂ (¬fork-≈ t₁≈t₂ ¬fork₁) step₂ sch' u₂ᵀ u₂ᴾ ∷ [])

εᴳ-simᴸ⋆ zero _ L⊑A (CS.fork l∈P₁ t∈T₁ step₁ u₁ᵀ u₁ᴾ H∈P₁ sch u₁ᴾ') L₁.⟨ Σ₁≈Σ₂ , P₁≈P₂ , Γ₁≈Γ₂ ⟩
    | Σ₂' P., sch' P., Σ₁'≈Σ₂' with memberᴾ-≈ L⊑A l∈P₁ P₁≈P₂
... | T₂ P., T₁≈T₂ P., l∈P₂ with memberᵀ-≈ L⊑A t∈T₁ T₁≈T₂
εᴳ-simᴸ⋆ zero _ L⊑A (CS.fork l∈P₁ t∈T₁ step₁ u₁ᵀ u₁ᴾ H∈P₁ sch u₁ᴾ') L₁.⟨ Σ₁≈Σ₂ , P₁≈P₂ , Γ₁≈Γ₂ ⟩

    -- Fork
    | Σ₂' P., sch' P., Σ₁'≈Σ₂' | T₂ P., T₁≈T₂ P., l∈P₂
    | ._ P., L₁.⟨ ⟨ G.fork l⊑H h⊑A e₁ , G.fork .l⊑H h⊑A₁ e₂ ⟩ , S₁≈S₂ ⟩ P., t∈T₂
         with redex-≈ L⊑A L₂.⟨ Γ₁≈Γ₂ , ⟨ ( G.fork l⊑H h⊑A e₁) , (G.fork l⊑H h⊑A₁ e₂) ⟩ , S₁≈S₂ ⟩ step₁
... | _ P., L₂.⟨ Γ₁'≈Γ₂' , t₁'≈t₂' , S₁'≈S₂' ⟩  P., step₂ with updateᵀ-≈ L⊑A u₁ᵀ T₁≈T₂ L₁.⟨ t₁'≈t₂' , S₁'≈S₂' ⟩
... | T₂' P., T₁'≈T₂' P., u₂ᵀ with updateᴾ-≈ L⊑A u₁ᴾ P₁≈P₂ T₁'≈T₂'
... | P₂' P., P₁'≈P₂' P., u₂ᴾ with memberᴾ-≈ h⊑A H∈P₁ P₁'≈P₂'
... | Tᴴ₂ P., Tᴴ₂≈T₁ᴴ P., H∈P₂
  rewrite lengthᵀ-≈ h⊑A Tᴴ₂≈T₁ᴴ with updateᴾ-≈ h⊑A u₁ᴾ' P₁'≈P₂' (newᵀ-≈ h⊑A Tᴴ₂≈T₁ᴴ L₁.⟨ ⟨ e₁ , e₂ ⟩ , [] ⟩)
... | P₂'' P., P₂''≈P₁'' P., uᴾ₂′ = Cᴳ _ L₁.⟨ Σ₁'≈Σ₂' , P₂''≈P₁'' , Γ₁'≈Γ₂' ⟩ (fork l∈P₂ t∈T₂ step₂ u₂ᵀ u₂ᴾ H∈P₂ sch' uᴾ₂′ ∷ [])

εᴳ-simᴸ⋆ zero Σ₁≈Σ₂ L⊑A (CS.fork l∈P₁ t∈T₁ step₁ u₁ᵀ u₁ᴾ H∈P₂ sch u₁ᴾ') L₁.⟨ Σ₁≈Σ₃ , P₁≈P₂ , Γ₁≈Γ₂ ⟩
  -- Fork∙
  | Σ₂' P., sch' P., Σ₁'≈Σ₂' | T₂ P., T₁≈T₂ P., l∈P₂
  | ._ P., L₁.⟨ ⟨ G.fork' l⊑H h⋤A e₁ , G.fork' .l⊑H h⋤A₁ e₂ ⟩ , S₁'≈S₂' ⟩ P., t∈T₂ = {!!}

εᴳ-simᴸ⋆ zero Σ₁≈Σ₂ L⊑A (CS.fork l∈P₁ t∈T₁ step₁ u₁ᵀ u₁ᴾ H∈P₂ sch u₁ᴾ') L₁.⟨ Σ₁≈Σ₃ , P₁≈P₂ , Γ₁≈Γ₂ ⟩
  -- Fork∙ (?)
  | Σ₂' P., sch' P., Σ₁'≈Σ₂' | T₂ P., T₁≈T₂ P., l∈P₂
  | ._ P., L₁.⟨ ⟨ G.fork' l⊑H h⋤A e₁ , G.fork∙ .l⊑H e₂ ⟩ , S₁'≈S₂' ⟩ P., t∈T₂ = {!!}

εᴳ-simᴸ⋆ zero Σ₁≈Σ₂ L⊑A (CS.fork∙ l∈P t∈T step uᵀ uᴾ sch) g₁'≈g₂' | sch' = {!!}

εᴳ-simᴸ⋆ zero Σ₁≈Σ₂ L⊑A (CS.skip l∈P₁ t∈T₁ stuck₁ sch) L₁.⟨ Σ₁≈Σ₂' , P₁≈P₂ , Γ₁≈Γ₂ ⟩ | Σ₂' P., sch' P., Σ₁'≈Σ₂' with memberᴾ-≈ L⊑A l∈P₁ P₁≈P₂
... | T₂ P., T₁≈T₂ P., l∈P₂ with memberᵀ-≈ L⊑A t∈T₁ T₁≈T₂
... | ._ P., ⟨ t₁≈t₂ , S₁≈S₂ ⟩ P., t∈T₂
  = Cᴳ C.⟨ Σ₂' , _ , _ ⟩ L₁.⟨ Σ₁'≈Σ₂' , P₁≈P₂ , Γ₁≈Γ₂ ⟩ (skip l∈P₂ t∈T₂ (stuck-≈ L⊑A L₂.⟨ Γ₁≈Γ₂ , t₁≈t₂ , S₁≈S₂ ⟩ stuck₁) sch' ∷ [])

εᴳ-simᴸ⋆ zero Σ₁≈Σ₂ L⊑A (CS.done l∈P₁ t∈T₁ (Done isVal) sch) L₁.⟨ Σ₁≈Σ₂' , P₁≈P₂ , Γ₁≈Γ₂ ⟩ | Σ₂' P., sch' P., Σ₁'≈Σ₂' with memberᴾ-≈ L⊑A l∈P₁ P₁≈P₂
... | T₂ P., T₁≈T₂ P., l∈P₂ with memberᵀ-≈ L⊑A t∈T₁ T₁≈T₂
... | ._ P., ⟨ t₁≈t₂ , L₂.[] ⟩ P., t∈T₂ = Cᴳ ⟨ Σ₂' , _ , _ ⟩ L₁.⟨ Σ₁'≈Σ₂' , P₁≈P₂ , Γ₁≈Γ₂ ⟩ (done l∈P₂ t∈T₂ (Done (val-≈ t₁≈t₂ isVal)) sch' ∷ [])

εᴳ-simᴸ⋆ (SC.suc n₂) Σ₁≈Σ₂ L⊑A step g₁'≈g₂' = {!!}

εᴳ-sim⋆ : ∀ {l n ls} {g₁ g₁' g₂ : Global ls} -> Dec (l ⊑ A) -> ( l P., n ) ⊢ g₁ ↪ g₁' -> g₁ ≈ᴳ g₂ -> g₂ ↪⋆-≈ᴳ g₁'
εᴳ-sim⋆ (yes L⊑A) step x = εᴳ-simᴸ⋆ _ (align (Σ₁≈Σ₂ x)) L⊑A step x
εᴳ-sim⋆ {g₁ = g₁} {g₁' = g₁'} {g₂ = g₂} (no H⋤A) stepᴴ g₁≈g₂ = Cᴳ g₂ ( trans-≈ᴳ (sym-≈ᴳ (⌜ εᴳ-simᴴ H⋤A stepᴴ ⌝ᴳ)) g₁≈g₂) []
