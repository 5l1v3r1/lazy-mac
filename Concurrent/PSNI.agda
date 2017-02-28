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
open import Sequential.PINI 𝓛 A using (stepᴸ ; stepᴴ-≅ᴴ ; stepᴴ-≅ᴹ ; stepᴴ)


--------------------------------------------------------------------------------

open Scheduler.Security.NIˢ 𝓛 A 𝓝 renaming (State to Stateˢ)
open import Scheduler.Base 𝓛

open import Concurrent.Erasure A 𝓝 hiding (updateᵀ ; updateᴾ)
open import Concurrent.Lemmas A 𝓝

import Concurrent.LowEq  A 𝓝 as L₁
open L₁

import Sequential.LowEq  𝓛 A as L₂ renaming (_≈ᵀˢ⟨_⟩_ to _≈ᵀᴴ⟨_⟩_ ; ⌞_⌟ᵀˢ to ⌞_⌟ᵀᴴ ; ⌜_⌝ᵀˢ to ⌜_⌝ᵀᴴ)
open L₂

import Sequential.Graph  as G
open G 𝓛 A

--------------------------------------------------------------------------------

data  _↪⋆-≈ᴳ_ {ls} (g₂ : Global ls) (g₁' : Global ls) : Set where
   Cᴳ : ∀ (g₂' : Global ls) -> g₁' ≈ᴳ g₂' -> g₂ ↪⋆ g₂' -> g₂ ↪⋆-≈ᴳ g₁'

open import Data.Nat
open import Function


-- This is consistent with the fact that our lists are truly mappings
-- they are not defined so becuase they are inconvinient to reason with
postulate _∈ᴸ_ : (l : Label) (ls : List Label) -> l ∈ ls  -- TODO probably can be added to the lattice

lookupᴾ : ∀ {l ls} -> l ∈ ls -> (P : Pools ls) -> ∃ (λ T → l ↦ T ∈ᴾ P)
lookupᴾ here (T C.◅ P) = T P., here
lookupᴾ (there q) (T' C.◅ P) = P.map id there (lookupᴾ q P)

-- The scheduler gives me only val-≈id thread id
postulate lookupᵀ : ∀ {l} -> (n : SC.ℕ) (T : Pool l) -> ∃ (λ t → n ↦ t ∈ᵀ T)

updateᵀ : ∀ {l n} {t : Thread l} {T : Pool l} -> n ↦ t ∈ᵀ T -> (t' : Thread l) -> ∃ (λ T' → T' ≔ T [ n ↦ t' ]ᵀ)
updateᵀ C.here t' = _ P., here
updateᵀ (C.there x) t' = P.map (_◅_ _) there (updateᵀ x t')

updateᴾ : ∀ {l ls} {T : Pool l} {P : Pools ls} -> l ↦ T ∈ᴾ P -> (T' : Pool l) -> ∃ (λ P' → P' ≔ P [ l ↦ T' ]ᴾ)
updateᴾ = {!!}

-- TODO move to Semantics
postulate stateᴾ : ∀ {l ls τ} (p : Program l ls τ) -> Stateᴾ p

isFork? : ∀ {π τ} (t : Term π τ) -> Dec (IsFork t)
isFork? t = {!!}

secureStack : ∀ {l l' τ} -> Stack l (Mac l' τ) (Mac l τ) -> l' ≡ l
secureStack [] = refl
secureStack (# τ∈π ∷ S) = secureStack S
secureStack (Bind x ∷ S) = refl
secureStack ∙ = refl

open import Sequential.Graph 𝓛 A

εᴳ-simᴸ⋆ : ∀ {L n n₁ ls} {Σ₁ Σ₁' Σ₂ : Stateˢ} {Γ₁ Γ₁' Γ₂ : Heaps ls} {P₁ P₁' P₂ : Pools ls} ->
               (n₂ : SC.ℕ) ->
               Σ₁ ≈ˢ-⟨ n₁ , n₂ ⟩ Σ₂ ->
               let g₁ = ⟨ Σ₁ , Γ₁ , P₁ ⟩
                   g₁' = ⟨ Σ₁' , Γ₁' , P₁' ⟩
                   g₂ = ⟨ Σ₂ , Γ₂ , P₂ ⟩ in
               L ⊑ A -> (L P., n)  ⊢ g₁ ↪ g₁' -> g₁ ≈ᴳ g₂ -> g₂ ↪⋆-≈ᴳ g₁'

εᴳ-simᴸ⋆ SC.zero Σ₁≈Σ₂ L⊑A step g₁'≈g₂' with squareˢ L⊑A Σ₁≈Σ₂ (getSchStep step)

εᴳ-simᴸ⋆ zero _ L⊑A (CS.step-∅ l∈P₁ t∈T₁ ¬fork₁ step₁ sch₁ u₁ᵀ u₁ᴾ) L₁.⟨ Σ₁≈Σ₂ , MS₁≈MS₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩
    | Σ₂' P., sch' P., Σ₁'≈Σ₂' with memberᴾ-≈ (yes L⊑A) l∈P₁ P₁≈P₂
... | T₂ P., T₁≈T₂ P., l∈P₂ with memberᵀ-≈ L⊑A t∈T₁ T₁≈T₂
... | _ P., ⟨ t₁≈t₂ , S₁≈S₂ ⟩ P., t∈T₂ with redex-≈ L⊑A L₁.⟨ Ms₁≈Ms₂ , Γ₁≈Γ₂ , t₁≈t₂ , S₁≈S₂ ⟩ step₁
... | _ P., L₂.⟨ Ms₁'≈Ms₂' , Γ₁'≈Γ₂' , Ts₁'≈Ts₂' ⟩  P., step₂ with updateᵀ-≈ L⊑A u₁ᵀ T₁≈T₂ Ts₁'≈Ts₂'
... | T₂' P., T₁'≈T₂' P., u₂ᵀ with updateᴾ-≈ (yes L⊑A) u₁ᴾ P₁≈P₂ T₁'≈T₂'
... | P₂' P., P₁'≈P₂' P., u₂ᴾ
  = Cᴳ _ L₁.⟨ Σ₁'≈Σ₂' , ? , Γ₁'≈Γ₂' , P₁'≈P₂' ⟩ (step-∅ l∈P₂ t∈T₂ (¬fork-≈ t₁≈t₂ ¬fork₁) step₂ sch' u₂ᵀ u₂ᴾ ∷ [])

εᴳ-simᴸ⋆ zero _ L⊑A (CS.fork l∈P₁ t∈T₁ step₁ u₁ᵀ u₁ᴾ H∈P₁ sch u₁ᴾ') L₁.⟨ Σ₁≈Σ₂ , MS₁≈MS₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩ = ?
--     | Σ₂' P., sch' P., Σ₁'≈Σ₂' with memberᴾ-≈ (yes L⊑A) l∈P₁ P₁≈P₂
-- ... | T₂ P., T₁≈T₂ P., l∈P₂ with memberᵀ-≈ L⊑A t∈T₁ T₁≈T₂
-- εᴳ-simᴸ⋆ zero _ L⊑A (CS.fork l∈P₁ t∈T₁ step₁ u₁ᵀ u₁ᴾ H∈P₁ sch u₁ᴾ') L₁.⟨ Σ₁≈Σ₂ , MS₁≈MS₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩

--     -- Fork
--     | Σ₂' P., sch' P., Σ₁'≈Σ₂' | T₂ P., T₁≈T₂ P., l∈P₂
--     | ._ P., L₁.⟨ ⟨ G.fork l⊑H h⊑A e₁ , G.fork .l⊑H h⊑A₁ e₂ ⟩ , S₁≈S₂ ⟩ P., t∈T₂
--          with redex-≈ L⊑A L₂.⟨ Γ₁≈Γ₂ , ⟨ ( G.fork l⊑H h⊑A e₁) , (G.fork l⊑H h⊑A₁ e₂) ⟩ , S₁≈S₂ ⟩ step₁
-- ... | _ P., L₂.⟨ Γ₁'≈Γ₂' , t₁'≈t₂' , S₁'≈S₂' ⟩  P., step₂ with updateᵀ-≈ L⊑A u₁ᵀ T₁≈T₂ L₁.⟨ t₁'≈t₂' , S₁'≈S₂' ⟩
-- ... | T₂' P., T₁'≈T₂' P., u₂ᵀ with updateᴾ-≈ (yes L⊑A) u₁ᴾ P₁≈P₂ T₁'≈T₂'
-- ... | P₂' P., P₁'≈P₂' P., u₂ᴾ with memberᴾ-≈ (yes h⊑A) H∈P₁ P₁'≈P₂'
-- ... | Tᴴ₂ P., Tᴴ₂≈T₁ᴴ P., H∈P₂
--   rewrite lengthᵀ-≈ h⊑A Tᴴ₂≈T₁ᴴ with updateᴾ-≈ (yes h⊑A) u₁ᴾ' P₁'≈P₂' (newᵀ-≈ Tᴴ₂≈T₁ᴴ L₁.⟨ ⟨ e₁ , e₂ ⟩ , [] ⟩)
-- ... | P₂'' P., P₂''≈P₁'' P., uᴾ₂′ = Cᴳ _ L₁.⟨ Σ₁'≈Σ₂' , P₂''≈P₁'' , Γ₁'≈Γ₂' ⟩ (fork l∈P₂ t∈T₂ step₂ u₂ᵀ u₂ᴾ H∈P₂ sch' uᴾ₂′ ∷ [])

-- εᴳ-simᴸ⋆ zero Σ₁≈Σ₂ L⊑A (CS.fork l∈P₁ t∈T₁ step₁ u₁ᵀ u₁ᴾ H∈P₁ sch u₁ᴾ') L₁.⟨ Σ₁≈Σ₃ , P₁≈P₂ , Γ₁≈Γ₂ ⟩
--   -- Fork∙
--   | Σ₂' P., sch' P., Σ₁'≈Σ₂' | T₂ P., T₁≈T₂ P., l∈P₂
--   | ._ P., L₁.⟨ ⟨ G.fork' l⊑H h⋤A e₁ , G.fork' .l⊑H h⋤A₁ e₂ ⟩ , S₁≈S₂ ⟩ P., t∈T₂
--     with redex-≈ L⊑A L₂.⟨ Γ₁≈Γ₂ , ⟨ ( G.fork' l⊑H h⋤A e₁) , G.fork' l⊑H h⋤A₁ e₂ ⟩ , S₁≈S₂ ⟩ step₁
-- ... | _ P., L₂.⟨ Γ₁'≈Γ₂' , t₁'≈t₂' , S₁'≈S₂' ⟩  P., step₂ with updateᵀ-≈ L⊑A u₁ᵀ T₁≈T₂ L₁.⟨ t₁'≈t₂' , S₁'≈S₂' ⟩
-- ... | T₂' P., T₁'≈T₂' P., u₂ᵀ with updateᴾ-≈ (yes L⊑A) u₁ᴾ P₁≈P₂ T₁'≈T₂'
-- ... | P₂' P., P₁'≈P₂' P., u₂ᴾ with memberᴾ-≈ (no h⋤A) H∈P₁ P₁'≈P₂'
-- ... | Tᴴ₂ P., Tᴴ₂≈T₁ᴴ P., H∈P₂ with id-≈ˢ (lengthᵀ Tᴴ₂) l⊑H L⊑A h⋤A sch'
-- ... | Σ₂'' P., sch'' P., Σ₂'≈Σ₂'' with updateᴾ-≈ (no h⋤A) u₁ᴾ' P₁'≈P₂' (newᵀ-≈ Tᴴ₂≈T₁ᴴ L₁.⟨ ⟨ e₁ , e₂ ⟩ , [] ⟩)
-- ... | P₂'' P., P₂''≈P₁'' P., uᴾ₂′ = Cᴳ _ L₁.⟨ trans-≈ˢ Σ₁'≈Σ₂' Σ₂'≈Σ₂'' , P₂''≈P₁'' , Γ₁'≈Γ₂' ⟩ (fork l∈P₂ t∈T₂ step₂ u₂ᵀ u₂ᴾ H∈P₂ sch'' uᴾ₂′ ∷ [])

εᴳ-simᴸ⋆ zero Σ₁≈Σ₂ L⊑A (CS.fork {Tᴴ = T₁ᴴ} l∈P₁ t∈T₁ step₁ u₁ᵀ u₁ᴾ H∈P₁ sch u₁ᴾ') L₁.⟨ Σ₁≈Σ₃ , Ms₁≈Ms₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩ = ?
--   -- Fork∙
--   | Σ₂' P., sch' P., Σ₁'≈Σ₂' | T₂ P., T₁≈T₂ P., l∈P₂
--   | ._ P., L₁.⟨ ⟨ G.fork' l⊑H h⋤A e₁ , G.fork∙ .l⊑H e₂ ⟩ , S₁≈S₂ ⟩ P., t∈T₂
--        with redex-≈ L⊑A L₂.⟨ Γ₁≈Γ₂ , ⟨ ( G.fork' l⊑H h⋤A e₁) , G.fork∙ l⊑H e₂ ⟩ , S₁≈S₂ ⟩ step₁
-- ... | _ P., L₂.⟨ Γ₁'≈Γ₂' , t₁'≈t₂' , S₁'≈S₂' ⟩  P., step₂ with updateᵀ-≈ L⊑A u₁ᵀ T₁≈T₂ L₁.⟨ t₁'≈t₂' , S₁'≈S₂' ⟩
-- ... | T₂' P., T₁'≈T₂' P., u₂ᵀ with updateᴾ-≈ (yes L⊑A) u₁ᴾ P₁≈P₂ T₁'≈T₂'
-- ... | P₂' P., P₁'≈P₂' P., u₂ᴾ with step-≈ˢ l⊑H L⊑A h⋤A sch'
-- ... | Σ₂'' P., sch'' P., Σ₂'≈Σ₂'' with updateᴾ-≈ {T₂ = T₁ᴴ} (no h⋤A) u₁ᴾ' P₁'≈P₂' L₁.∙
-- ... | P₂'' P., P₁''≈P₂'' P., uᴾ₂′
--   = Cᴳ _ L₁.⟨ (trans-≈ˢ Σ₁'≈Σ₂' Σ₂'≈Σ₂'') , trans-≈ᴾ P₁''≈P₂'' L₁.⌜ sym (updateᴾ∙ h⋤A uᴾ₂′) ⌝ᴾ , Γ₁'≈Γ₂' ⟩ (fork∙ l∈P₂ t∈T₂ step₂ u₂ᵀ u₂ᴾ sch'' ∷ [])

εᴳ-simᴸ⋆ zero _ L⊑A (CS.fork∙ {P₂ = P₁'} l∈P₁ t∈T₁ step₁ u₁ᵀ u₁ᴾ sch) L₁.⟨ Σ₁≈Σ₂ , MS₁≈MS₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩
    | Σ₂' P., sch' P., Σ₁'≈Σ₂' with memberᴾ-≈ (yes L⊑A) l∈P₁ P₁≈P₂
... | T₂ P., T₁≈T₂ P., l∈P₂ with memberᵀ-≈ L⊑A t∈T₁ T₁≈T₂

εᴳ-simᴸ⋆ {ls = ls} zero Σ₁≈Σ₂ L⊑A (CS.fork∙ {H} {tᴴ = t₁ᴴ} {P₂ = P₁'} l∈P₁ t∈T₁ step₁ u₁ᵀ u₁ᴾ sch) ⟨ _ , P₁≈P₂ , Γ₁≈Γ₂ ⟩
  | Σ₂' P., sch' P., Σ₁'≈Σ₂' | T₂ P., T₁≈T₂ P., l∈P₂
  | ._ P., ⟨ ⟨ G.fork∙ l⊑H e₁ , G.fork' .l⊑H h⋤A e₂ ⟩ , S₁≈S₂ ⟩ P., t∈T₂
    with redex-≈ L⊑A L₂.⟨ Γ₁≈Γ₂ , ⟨ ( G.fork∙ l⊑H e₁) , G.fork' l⊑H h⋤A e₂ ⟩ , S₁≈S₂ ⟩ step₁
... | _ P., L₂.⟨ Γ₁'≈Γ₂' , Ts₁'≈Ts₂' ⟩  P., step₂ with updateᵀ-≈ L⊑A u₁ᵀ T₁≈T₂ Ts₁'≈Ts₂'
... | T₂' P., T₁'≈T₂' P., u₂ᵀ with updateᴾ-≈ (yes L⊑A) u₁ᴾ P₁≈P₂ T₁'≈T₂'
... | P₂' P., P₁'≈P₂' P., u₂ᴾ with lookupᴾ (H ∈ᴸ ls) P₁'
... | T₁ᴴ P., H∈P₁ with memberᴾ-≈ (no h⋤A) H∈P₁ P₁'≈P₂'  -- TODO Won't need this if we add H∈P₁ to fork∙
... | T₂ᴴ P., T₂ᴴ≈T₁ᴴ P., H∈P₂ with fork-≈ˢ (lengthᵀ T₂ᴴ) l⊑H L⊑A h⋤A sch'
... | Σ₂'' P., sch'' P., Σ₂'≈Σ₂'' with updateᴾ H∈P₁ (T₁ᴴ ▻ ⟨ t₁ᴴ , [] ⟩)
... | P₁'' P., u₁ᴾ′ with updateᴾ-≈ {T₂ = T₂ᴴ ▻ ⟨ _ , [] ⟩} (no h⋤A) u₁ᴾ′ P₁'≈P₂' ?  -- P₁''≈P₂''
... | P₂'' P., P₁''≈P₂'' P., u₂ᴾ′
  = Cᴳ _ ⟨ trans-≈ˢ Σ₁'≈Σ₂' Σ₂'≈Σ₂'' , trans-≈ᴾ P₁'≈P₂' L₁.⌜ updateᴾ∙ h⋤A u₂ᴾ′ ⌝ᴾ , Γ₁'≈Γ₂' ⟩ (fork l∈P₂ t∈T₂ step₂ u₂ᵀ u₂ᴾ H∈P₂ sch'' u₂ᴾ′ ∷ [])

εᴳ-simᴸ⋆ zero _ L⊑A (CS.fork∙ l∈P₁ t∈T₁ step₁ u₁ᵀ u₁ᴾ sch) ⟨ Σ₁≈Σ₂ , P₁≈P₂ , Γ₁≈Γ₂ ⟩
  | Σ₂' P., sch' P., Σ₁'≈Σ₂' | T₂ P., T₁≈T₂ P., l∈P₂
  | ._ P., ⟨ ⟨ G.fork∙ l⊑H e₁ , G.fork∙ .l⊑H e₂ ⟩ , S₁≈S₂ ⟩ P., t∈T₂
    with redex-≈ L⊑A L₂.⟨ Γ₁≈Γ₂ , ⟨ ( G.fork∙ l⊑H e₁) , G.fork∙ l⊑H e₂ ⟩ , S₁≈S₂ ⟩ step₁
... | _ P., L₂.⟨ Γ₁'≈Γ₂' , Ts₁'≈Ts₂' ⟩  P., step₂ with updateᵀ-≈ L⊑A u₁ᵀ T₁≈T₂ Ts₁'≈Ts₂'
... | T₂' P., T₁'≈T₂' P., u₂ᵀ with updateᴾ-≈ (yes L⊑A) u₁ᴾ P₁≈P₂ T₁'≈T₂'
... | P₂' P., P₁'≈P₂' P., u₂ᴾ
  = Cᴳ _ ⟨ Σ₁'≈Σ₂' , P₁'≈P₂' , Γ₁'≈Γ₂' ⟩ (fork∙ l∈P₂ t∈T₂ step₂ u₂ᵀ u₂ᴾ sch' ∷ [])

εᴳ-simᴸ⋆ zero Σ₁≈Σ₂ L⊑A (CS.skip l∈P₁ t∈T₁ stuck₁ sch) L₁.⟨ Σ₁≈Σ₂' , Ms₁≈Ms₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩ | Σ₂' P., sch' P., Σ₁'≈Σ₂' with memberᴾ-≈ (yes L⊑A) l∈P₁ P₁≈P₂
... | T₂ P., T₁≈T₂ P., l∈P₂ with memberᵀ-≈ L⊑A t∈T₁ T₁≈T₂
... | ._ P., ⟨ t₁≈t₂ , S₁≈S₂ ⟩ P., t∈T₂
  = Cᴳ C.⟨ Σ₂' , _ , _ , _ ⟩ L₁.⟨ Σ₁'≈Σ₂' , Ms₁≈Ms₂ , P₁≈P₂ , Γ₁≈Γ₂ ⟩ (skip l∈P₂ t∈T₂ (stuck-≈ L⊑A L₂.⟨ Γ₁≈Γ₂ , t₁≈t₂ , S₁≈S₂ ⟩ stuck₁) sch' ∷ [])

εᴳ-simᴸ⋆ zero Σ₁≈Σ₂ L⊑A (CS.done l∈P₁ t∈T₁ (Done isVal) sch) L₁.⟨ Σ₁≈Σ₂' , Ms₁≈Ms₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩ | Σ₂' P., sch' P., Σ₁'≈Σ₂' with memberᴾ-≈ (yes L⊑A) l∈P₁ P₁≈P₂
... | T₂ P., T₁≈T₂ P., l∈P₂ with memberᵀ-≈ L⊑A t∈T₁ T₁≈T₂
... | ._ P., ⟨ t₁≈t₂ , S₁≈S₂ ⟩ P., t∈T₂ = Cᴳ ⟨ Σ₂' , _ , _ , _ ⟩ L₁.⟨ Σ₁'≈Σ₂' , Ms₁≈Ms₂ , P₁≈P₂ , Γ₁≈Γ₂ ⟩ (done l∈P₂ t∈T₂ (Done (val-≈ t₁≈t₂ isVal)) sch' ∷ [])

εᴳ-simᴸ⋆ {ls = ls} {Γ₂ = Γ₂} {P₂ = P₂} (SC.suc n₂) Σ₁≈Σ₂ L⊑A step L₁.⟨ _ , Ms₁≈Ms₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩ = ?
-- with triangleˢ L⊑A Σ₁≈Σ₂ (getSchStep step)
-- ... | Σ₂' P., H P., m P., H⋤A P., Σ₂≈Σ₂' P., nextˢ  with lookupᴾ (H ∈ᴸ ls) P₂
-- ... | T₂ P., T∈P₂ with lookupᵀ m T₂
-- ... | ⟨ t₂ , S₂ ⟩ P., t∈T₂ with stateᴾ ⟨ Γ₂ , t₂ , S₂ ⟩

-- εᴳ-simᴸ⋆ (suc n₂) Σ₁≈Σ₂ L⊑A step ⟨ Σ₁≈Σ₃ , Ms₁≈Ms₂ , Γ₁≈Γ₂ , P₁≈P₂ ⟩
--   -- Done
--   |  Σ₂' P., H P., m P., H⋤A P., Σ₂≈Σ₂' P., nextˢ | T₂ P., T∈P₂
--   | C.⟨ t₂ , S₂ ⟩ P., t∈T₂ | isD don with εᴳ-simᴸ⋆ n₂ Σ₂≈Σ₂' L⊑A step ⟨ forget Σ₂≈Σ₂' , P₁≈P₂ , Γ₁≈Γ₂ ⟩
-- ... | Cᴳ g₂' ⟨ Σ₂'≈Σ₂'' , t₂'≈t₂'' , Γ₂'≈Γ₂'' ⟩ ss = Cᴳ _ ⟨ Σ₂'≈Σ₂'' , ? , t₂'≈t₂'' , Γ₂'≈Γ₂'' ⟩ (done T∈P₂ t∈T₂ don (nextˢ Done) ∷ ss)

--   -- Redex
-- εᴳ-simᴸ⋆ (suc n₂) Σ₁≈Σ₂ L⊑A step ⟨ Σ₁≈Σ₃ , P₁≈P₂ , Γ₁≈Γ₂ ⟩
--   | Σ₂' P., H P., m P., H⋤A P., Σ₂≈Σ₂' P., nextˢ | T₂ P., T∈P₂
--   | C.⟨ t₂ , S₂ ⟩ P., t∈T₂ | isR (Step {p' = ∙} ())

-- εᴳ-simᴸ⋆ (suc n₂) Σ₁≈Σ₂ L⊑A step ⟨ Σ₁≈Σ₃ , P₁≈P₂ , Γ₁≈Γ₂ ⟩
--   | Σ₂' P., H P., m P., H⋤A P., Σ₂≈Σ₂' P., nextˢ | T₂ P., T∈P₂
--   | C.⟨ t₂ , S₂ ⟩ P., t∈T₂ | isR (Step {p' = ⟨ a , b , c ⟩} step') with isFork? t₂

--   -- step-∅
-- εᴳ-simᴸ⋆ (suc n₂) Σ₁≈Σ₂ L⊑A step ⟨ Σ₁≈Σ₃ , P₁≈P₂ , Γ₁≈Γ₂ ⟩
--   | Σ₂' P., H P., m P., H⋤A P., Σ₂≈Σ₂' P., nextˢ | T₂ P., T∈P₂
--   | C.⟨ t₂ , S₂ ⟩ P., t∈T₂ | isR (Step {p' = ⟨ Γ₂' , t₂' , S₂' ⟩} step₂) | no ¬fork with updateᵀ t∈T₂ ⟨ t₂' , S₂' ⟩
-- ... | T₂' P., uᵀ with updateᴾ T∈P₂ T₂'
-- ... | P₂' P., uᴾ with ⟨ forget Σ₂≈Σ₂' , trans-≈ᴾ P₁≈P₂ L₁.⌜ updateᴾ∙ H⋤A uᴾ ⌝ᴾ , trans-≈ᴴ Γ₁≈Γ₂ ⌜ stepᴴ-Γ H⋤A step₂ ⌝ᴴ ⟩
-- ... | g₂≈g₂' with εᴳ-simᴸ⋆ n₂ Σ₂≈Σ₂' L⊑A step g₂≈g₂'
-- ... | Cᴳ g₂'' g₂'≈g₂'' ss  = Cᴳ _ g₂'≈g₂'' (step-∅ T∈P₂ t∈T₂ ¬fork step₂ (nextˢ Step) uᵀ uᴾ ∷ ss)

--   -- fork
-- εᴳ-simᴸ⋆ {ls = ls} (suc n₂) Σ₁≈Σ₂ L⊑A step ⟨ Σ₁≈Σ₃ , P₁≈P₂ , Γ₁≈Γ₂ ⟩
--   | Σ₂' P., H P., m P., H⋤A P., Σ₂≈Σ₂' P., nextˢ | T₂ P., T∈P₂
--   | C.⟨ _ , S₂ ⟩ P., t∈T₂ | isR (Step {p' = ⟨ Γ₂' , t₂' , S₂' ⟩} step₂) | yes (Fork {h = H₂} H⊑H₂ t₂ᴴ)
--     rewrite secureStack S₂ with updateᵀ t∈T₂ ⟨ t₂' , S₂' ⟩
-- ... | T₂' P., uᵀ with updateᴾ T∈P₂ T₂'
-- ... | P₂' P., uᴾ with lookupᴾ (H₂ ∈ᴸ ls) P₂'
-- ... | T₂ᴴ P., H∈P₂' with updateᴾ H∈P₂' (T₂ᴴ ▻ ⟨ t₂ᴴ , [] ⟩)
-- ... | P₂'' P., u₂ᴾ with trans-≈ᴾ (trans-≈ᴾ P₁≈P₂ L₁.⌜ updateᴾ∙ H⋤A uᴾ ⌝ᴾ) L₁.⌜ updateᴾ∙ (trans-⋢ H⊑H₂ H⋤A) u₂ᴾ ⌝ᴾ | trans-≈ᴴ Γ₁≈Γ₂ ⌜ stepᴴ-Γ H⋤A step₂ ⌝ᴴ
-- ... | P₂≈P₂' | Γ₂≈Γ₂' with εᴳ-simᴸ⋆ n₂ Σ₂≈Σ₂' L⊑A step ⟨ forget Σ₂≈Σ₂' , P₂≈P₂'  , Γ₂≈Γ₂' ⟩
-- ... | Cᴳ g₂'' g₂≈g₂'' ss = Cᴳ _ g₂≈g₂'' (fork T∈P₂ t∈T₂ step₂ uᵀ uᴾ H∈P₂' (nextˢ (Fork H₂ (lengthᵀ T₂ᴴ) H⊑H₂)) u₂ᴾ ∷ ss)

--   -- fork∙
-- εᴳ-simᴸ⋆ (suc n₂) Σ₁≈Σ₂ L⊑A step ⟨ Σ₁≈Σ₃ , P₁≈P₂ , Γ₁≈Γ₂ ⟩
--   | Σ₂' P., H P., m P., H⋤A P., Σ₂≈Σ₂' P., nextˢ | T₂ P., T∈P₂
--   | C.⟨ ._ , S₂ ⟩ P., t∈T₂ | isR (Step {p' = ⟨ Γ₂' , t₂' , S₂' ⟩} step₂) | yes (Fork∙ l⊑H t₂ᴴ)
--     rewrite secureStack S₂ with updateᵀ t∈T₂ ⟨ t₂' , S₂' ⟩
-- ... | T₂' P., uᵀ with updateᴾ T∈P₂ T₂'
-- ... | P₂' P., uᴾ with ⟨ forget Σ₂≈Σ₂' , trans-≈ᴾ P₁≈P₂ L₁.⌜ updateᴾ∙ H⋤A uᴾ ⌝ᴾ , trans-≈ᴴ Γ₁≈Γ₂ ⌜ stepᴴ-Γ H⋤A step₂ ⌝ᴴ ⟩
-- ... | g₂≈g₂' with εᴳ-simᴸ⋆ n₂ Σ₂≈Σ₂' L⊑A step g₂≈g₂'
-- ... | Cᴳ g₂'' g₂'≈g₂'' ss = Cᴳ _ g₂'≈g₂'' (fork∙ T∈P₂ t∈T₂ step₂ uᵀ uᴾ (nextˢ Step) ∷ ss)

--   -- Stuck
-- εᴳ-simᴸ⋆ (suc n₂) Σ₁≈Σ₂ L⊑A step ⟨ Σ₁≈Σ₃ , P₁≈P₂ , Γ₁≈Γ₂ ⟩
--   | Σ₂' P., H P., m P., H⋤A P., Σ₂≈Σ₂' P., nextˢ | T₂ P., T∈P₂
--   | C.⟨ t₂ , S₂ ⟩ P., t∈T₂ | isS stuck with εᴳ-simᴸ⋆ n₂ Σ₂≈Σ₂' L⊑A step ⟨ forget Σ₂≈Σ₂' , P₁≈P₂ , Γ₁≈Γ₂ ⟩
-- ... | Cᴳ g₂' ⟨ Σ₂'≈Σ₂'' , t₂'≈t₂'' , Γ₂'≈Γ₂'' ⟩ ss = Cᴳ _ ⟨ Σ₂'≈Σ₂'' , t₂'≈t₂'' , Γ₂'≈Γ₂'' ⟩ (skip T∈P₂ t∈T₂ stuck (nextˢ Skip) ∷ ss)

εᴳ-sim⋆ : ∀ {l n ls} {g₁ g₁' g₂ : Global ls} -> Dec (l ⊑ A) -> ( l P., n ) ⊢ g₁ ↪ g₁' -> g₁ ≈ᴳ g₂ -> g₂ ↪⋆-≈ᴳ g₁'
εᴳ-sim⋆ (yes L⊑A) step x = εᴳ-simᴸ⋆ _ (align (Σ₁≈Σ₂ x)) L⊑A step x
εᴳ-sim⋆ {g₁ = g₁} {g₁' = g₁'} {g₂ = g₂} (no H⋤A) stepᴴ g₁≈g₂ = Cᴳ g₂ ( trans-≈ᴳ (sym-≈ᴳ (⌜ εᴳ-simᴴ H⋤A stepᴴ ⌝ᴳ)) g₁≈g₂) []
