import Lattice as L₁
import Scheduler as S₁
open import Scheduler.Security

module Concurrent.Lemmas {𝓛 : L₁.Lattice} {𝓢 : S₁.Scheduler 𝓛} (A : L₁.Label 𝓛) (𝓝 : NIˢ 𝓛 A 𝓢) where

open import Data.Nat as N
open import Relation.Nullary
open import Types 𝓛

open import Sequential.Calculus 𝓛 renaming (⟨_,_,_⟩ to mkᴾ ; ⟨_,_⟩ to mkᵀ) hiding (Ms ; Γ)
import Sequential.Semantics as S
open S 𝓛
open import Sequential.Security.Graph 𝓛 A renaming (⟨_,_⟩ to Eᵗ)
open import Sequential.Security.LowEq 𝓛 A renaming (⟨_,_,_⟩ to is≈ᴾ ; ⟨_,_⟩ to is≈ᵗ )
open _≈ᴾ⟨_⟩_
open import Sequential.Security.PINI 𝓛 A

import Concurrent.LowEq as L hiding (⌜_⌝ᴾ ; ⌞_⌟ᴾ) renaming ( ⟨_,_,_,_⟩ to is≈ᴳ)
open L A 𝓝
open import Concurrent.Calculus 𝓛 𝓢 as C renaming (⟨_,_,_,_⟩ to mkᴳ)

import Concurrent.Semantics as CS
open CS 𝓛 𝓢

open import Concurrent.Valid 𝓛 𝓢 as V hiding (memberᴾ)

open import Scheduler.Base 𝓛
open Scheduler.Security.NIˢ 𝓛 A 𝓝 renaming (State to Stateˢ)

open import Data.Product
open import Data.Empty

redexᴳ-≈ : ∀ {l i n ls} {g₁ g₂ g₁' : Global ls} {{v₁ : validᴳ g₁}} {{v₂ : validᴳ g₂}}
           -> l ⊑ A -> g₁ ≈ᴳ-⟨ i , 0 ⟩ g₂ -> ( l , n ) ⊢ g₁ ↪ g₁' -> Redexᴳ ( l , n ) g₂
redexᴳ-≈ {{ v₂ = Ms₂ⱽ , Γ₂ⱽ , Ps₂ⱽ }} l⊑A (L.is≈ᴳ Σ₁≈Σ₂ Ms₁≈Ms₂ Γ₁≈Γ₂ Ps₁≈Ps₂) (CS.step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ)
  with memberᴾ-≈  (yes l⊑A) l∈P Ps₁≈Ps₂
... | _ , P₁≈P₂' , l∈P₂  with memberᵀ-≈ t∈T P₁≈P₂'
... | _ , T₁≈T₂ , t∈T₂ with is≈ᴾ Ms₁≈Ms₂ Γ₁≈Γ₂ T₁≈T₂
... | p₁≈p₂ with redex-≈ {l⊑A = l⊑A} {{ Ms₂ⱽ , Γ₂ⱽ , V.memberᴾ (memberᴾˢ Ps₂ⱽ l∈P₂) t∈T₂ }} p₁≈p₂ (Step step)
... | Step {p' = p₂'} step' with redex-≈ˢ l⊑A sch Σ₁≈Σ₂ Step
... | _ , sch' with updateᵀ-≈ P₁≈P₂' (Ts₁≈Ts₂ ⌜ pini' (yes l⊑A) ⌞ p₁≈p₂ ⌟ᴾ step step' ⌝ᴾ) uᵀ
... | _ , p₁≈p₂' , uᵀ'  with updateᴾ-≈ Ps₁≈Ps₂ p₁≈p₂' uᴾ
... | _ , _ , uᴾ'
  = CS.Step (step-∅ l∈P₂ t∈T₂ (¬IsForkTS-≈ T₁≈T₂ ¬fork) step' sch' uᵀ' uᴾ')
redexᴳ-≈ {{Ms₁ⱽ , Γ₁ⱽ , Ps₁ⱽ}} {{Ms₂ⱽ , Γ₂ⱽ , Ps₂ⱽ }} l⊑A (L.is≈ᴳ Σ₁≈Σ₂ Ms₁≈Ms₂ Γ₁≈Γ₂ Ps₁≈Ps₂) (CS.fork {tᴴ = tᴴ} l∈P t∈T uᵀ u₁ᴾ H∈P sch u₂ᴾ)
  with memberᴾ-≈  (yes l⊑A) l∈P Ps₁≈Ps₂
... | _ , T₁≈T₂' , l∈P₂  with memberᵀ-≈ t∈T T₁≈T₂'
... | _ , (Kᵀˢ (Eᵗ e₁ S₁ᴱ) (Eᵗ e₂ S₂ᴱ)) , t∈T₂
  with fork-≈' {{proj₁ (V.memberᴾ (memberᴾˢ Ps₁ⱽ l∈P) t∈T )}} {{proj₁ (V.memberᴾ (memberᴾˢ Ps₂ⱽ l∈P₂) t∈T₂ )}} (is≈ᵗ e₁ e₂) (Fork _ _)
... | isFork-≈ {t₂ = tᴴ'} t₁ᴴ≈t₂ᴴ with updateᵀ-≈ T₁≈T₂' (Kᵀˢ (Eᵗ (Return （）) S₁ᴱ) (Eᵗ (Return （）) S₂ᴱ)) uᵀ
... | _ , P₁≈P₂ , uᵀ'  with updateᴾ-≈ Ps₁≈Ps₂ P₁≈P₂ u₁ᴾ
... | _ , Ps₁≈Ps₂' , u₁ᴾ' with memberᴾ-≈ (_ ⊑? A) H∈P Ps₁≈Ps₂'
... | _ , T₁≈T₂ , H∈P₂  with redex-≈ˢ l⊑A sch Σ₁≈Σ₂ (forkᴱ-≈ (_ ⊑? A) T₁≈T₂)
... | _ , sch' with updateᴾ-≈ Ps₁≈Ps₂' (newᵀ-≈ T₁≈T₂ (newᵀˢ-≈ (deepDupᵀ-≈ t₁ᴴ≈t₂ᴴ))) u₂ᴾ
... | _ , Ps₁≈Ps₂'' , u₂ᴾ'
  = Step (fork l∈P₂ t∈T₂ uᵀ' u₁ᴾ' H∈P₂ sch' u₂ᴾ')
redexᴳ-≈ {{_ , _ , Psⱽ}} l⊑A g₁≈g₂ (CS.fork∙ l∈P t∈T uᵀ uᴾ sch) = ⊥-elim (proj₁ (V.memberᴾ (memberᴾˢ Psⱽ l∈P) t∈T))
redexᴳ-≈ {{Ms₁ⱽ , Γ₁ⱽ , Ps₁ⱽ}} l⊑A (L.is≈ᴳ Σ₁≈Σ₂ Ms₁≈Ms₂ Γ₁≈Γ₂ Ps₁≈Ps₂) (CS.skip l∈P t∈T stuck sch)
  with memberᴾ-≈  (yes l⊑A) l∈P Ps₁≈Ps₂
... | _ , P₁≈P₂' , l∈P₂  with memberᵀ-≈ t∈T P₁≈P₂'
... | _ , T₁≈T₂ , t∈T₂ with redex-≈ˢ l⊑A sch Σ₁≈Σ₂ Skip
... | _ , sch' = CS.Step (skip l∈P₂ t∈T₂ (stuck-≈ {{Ms₁ⱽ , Γ₁ⱽ , V.memberᴾ (memberᴾˢ Ps₁ⱽ l∈P) t∈T }} (is≈ᴾ Ms₁≈Ms₂ Γ₁≈Γ₂ T₁≈T₂) stuck) sch')
redexᴳ-≈ l⊑A (L.is≈ᴳ Σ₁≈Σ₂ Ms₁≈Ms₂ Γ₁≈Γ₂ Ps₁≈Ps₂) (CS.done l∈P t∈T don sch)
  with memberᴾ-≈  (yes l⊑A) l∈P Ps₁≈Ps₂
... | _ , P₁≈P₂' , l∈P₂  with memberᵀ-≈ t∈T P₁≈P₂'
... | _ , T₁≈T₂ , t∈T₂ with redex-≈ˢ l⊑A sch Σ₁≈Σ₂ Done
... | _ , sch' = CS.Step (done l∈P₂ t∈T₂ (done-≈ T₁≈T₂ don) sch')

open import Relation.Binary.PropositionalEquality

secureStack : ∀ {π l l' τ} -> Stack l π (Mac l' τ) (Mac l τ) -> l' ≡ l
secureStack [] = refl
secureStack (# τ∈π ∷ S) = secureStack S
secureStack (Bind x ∷ S) = refl
secureStack ∙ = refl

εᴳ-simᴸ▵ : ∀ {l n ls T Ts} {g : Global ls} {{v : validᴳ g}} ->
              l ↦ T ∈ᴾ (P g) -> n ↦ Ts ∈ᵀ T -> Stateᴾ (mkᴾ (Ms g) (Γ g) Ts) ->
              (∀ (e : Event _) → ∃ (λ Σ' →  (C.Σ g) ⟶ Σ' ↑ S₁.⟪ l  , n , e ⟫ )) ->
                Redexᴳ (l , n) g
εᴳ-simᴸ▵ l∈Ps t∈T (S.isD x) nextˢ = CS.Step (done l∈Ps t∈T x (proj₂ (nextˢ Done)))
εᴳ-simᴸ▵ l∈Ps t∈T (S.isR (S.Step {p' = p'} x)) nextˢ with C.updateᵀ t∈T (TS p')
... | T' , uᵀ  with C.updateᴾ l∈Ps T'
... | Ps' , uᴾ = Step (step-∅ l∈Ps t∈T (Redex-¬IsForkTS (Step x)) x (proj₂ (nextˢ Step)) uᵀ uᴾ)
εᴳ-simᴸ▵ l∈Ps t∈T (S.isS x) nextˢ = Step (skip l∈Ps t∈T x (proj₂ (nextˢ Skip)))
εᴳ-simᴸ▵ {{_ , _ , Psⱽ}} l∈Ps t∈T (S.isF (S.isForkTS {S = S} (Fork {h = H} l⊑h t))) nextˢ
  rewrite secureStack S with C.updateᵀ t∈T (mkᵀ (Return _ _) S)
... | T' , uᵀ with C.updateᴾ l∈Ps T'
... | Ps' , u₁ᴾ with proj₁ (V.memberᴾ (memberᴾˢ Psⱽ l∈Ps) t∈T)
... | H∈ls , _ with lookupᴾ H∈ls Ps' | lookup-∈ᴾ H∈ls Ps'
... | Tᴴ | H∈Ps  with  C.updateᴾ H∈Ps (Tᴴ ▻ mkᵀ (deepDupᵀ t) [])
... | Ps'' , u₂ᴾ with nextˢ (Fork H (lengthᵀ Tᴴ) l⊑h)
... | _ , sch' =  CS.Step (fork l∈Ps t∈T uᵀ u₁ᴾ H∈Ps sch' u₂ᴾ)
εᴳ-simᴸ▵ {{v}} l∈Ps t∈T (S.isF (S.isForkTS {S = S} (Fork∙ p t))) nextˢ
  rewrite secureStack S = ⊥-elim (proj₁ (V.memberᴾ (memberᴾˢ (proj₂ (proj₂ v)) l∈Ps) t∈T))

-- open import Coinduction
-- open import Data.Product as P

-- Valid-Id : ∀ {ls} Label -> ℕ -> Global ls -> Set
-- Valid-Id {ls} l n g = P.Σ (l ∈ ls) (λ l∈ls → ∃ (λ T → l ↦ T ∈ᴾ (P g) × (∃ (λ Ts → n ↦ Ts ∈ᵀ T))))

-- Only existing threads are scheduled
-- data Correct {ls} (g₁ : Global ls) : Set where
--   isC : ∀ {l n e Σ₂} -> (C.Σ g₁ ⟶ Σ₂ ↑ S₁.⟪ l , n , e ⟫ ->
--     Valid-Id l n g₁ × (∀ {Ms₂ Γ₂ Ps₂} -> (l , n) ⊢ g₁ ↪ (mkᴳ Σ₂ Ms₂ Γ₂ Ps₂) -> ∞ (Correct (mkᴳ Σ₂ Ms₂ Γ₂ Ps₂)) )) -> Correct g₁


-- Ideally in Agda our data-structures would be mapped by labels.
-- However since functions complicate reasoning we are using a
-- surrogate list representation.  With a proper represenetation we
-- would not need this postulate.
postulate _∈ᴸ_ : (l : Label) (ls : List Label) -> l ∈ ls

-- We assume that only existing threads are scheduled.
postulate lookupᵀ : ∀ {l} -> (n : ℕ) (T : Pool l) -> ∃ (λ t → n ↦ t ∈ᵀ T)

redexᴳ-≈ᴴ : ∀ {ls L i j n} {g₁ g₂ g₁' : Global ls} {{v₁ : validᴳ g₁}} {{v₂ : validᴳ g₂}} ->
                      L ⊑ A -> g₁ ≈ᴳ-⟨ i , suc j ⟩ g₂ -> ( L , n ) ⊢ g₁ ↪ g₁' -> ∃ (λ x → Redexᴳ x g₂)
redexᴳ-≈ᴴ {ls} {g₂ = g₂} L⊑A g₁≈g₂ step with redex-≈▵ˢ L⊑A (Σ₁≈Σ₂′ g₁≈g₂) (getSchStep step)
... | (H , m) , nextˢ with lookupᵀ m (lookupᴾ (H ∈ᴸ ls) (P g₂))
... | Ts₂ , t∈T₂ = (H , m) , (εᴳ-simᴸ▵ (lookup-∈ᴾ (H ∈ᴸ ls) (P g₂)) t∈T₂ (stateᴾ (mkᴾ (Ms g₂) (Γ g₂) Ts₂)) nextˢ)
