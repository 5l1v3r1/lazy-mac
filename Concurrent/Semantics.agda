import Lattice as L
import Scheduler as S

module Concurrent.Semantics (𝓛 : L.Lattice) (𝓢 : S.Scheduler 𝓛) where

open import Types 𝓛
open S.Scheduler 𝓛 𝓢

open S.Message
open S.Event 𝓛

open import Sequential.Calculus 𝓛
open import Sequential.Semantics 𝓛
open import Concurrent.Calculus 𝓛 𝓢
open import Relation.Nullary

-- Concurrent semantics
data Stepᶜ (l : Label) (n : ℕ) {ls} : Global ls -> Global ls -> Set where
  step-∅ : ∀ {π₁ π₂ τ₁ τ₂ S₁ S₂ Σ₁ Σ₂ Ms₁ Ms₂} {t₁ : Term π₁ τ₁} {t₂ : Term π₂ τ₂} {Γ₁ Γ₂ : Heaps ls} {P₁ P₂ : Pools ls} {T₁ T₂ : Pool l}
           (l∈P : l ↦ T₁ ∈ᴾ P₁)
           (t∈T : n ↦ ⟨ t₁ , S₁ ⟩ ∈ᵀ T₁)
           (¬fork : ¬ (IsFork t₁))
           (step : ⟨ Ms₁ , Γ₁ , t₁ , S₁ ⟩ ⟼ ⟨ Ms₂ , Γ₂ , t₂ , S₂ ⟩)
           (sch : Σ₁ ⟶ Σ₂ ↑ ⟪ l , n , Step ⟫ )
           (uᵀ : T₂ ≔ T₁ [ n ↦ ⟨ t₂ , S₂ ⟩ ]ᵀ )
           (uᴾ : P₂ ≔ P₁ [ l ↦ T₂ ]ᴾ ) ->
           Stepᶜ l n ⟨ Σ₁ , Ms₁ , Γ₁ , P₁ ⟩ ⟨ Σ₂ , Ms₂ , Γ₂ , P₂ ⟩

  fork :  ∀ {H π S Ms Σ₁ Σ₂} {tᴴ : Term π (Mac H _)} {Γ₁ Γ₂ : Heaps ls}
            {P₁ P₂ P₃ : Pools ls} {T₁ T₂ : Pool l} {Tᴴ : Pool H} {l⊑H : l ⊑ H}
           (l∈P : l ↦ T₁ ∈ᴾ P₁)
           (t∈T : n ↦ ⟨ fork l⊑H tᴴ , S ⟩ ∈ᵀ T₁)
           (uᵀ : T₂ ≔ T₁ [ n ↦ ⟨ Return _ （） , S ⟩ ]ᵀ )
           (u₁ᴾ : P₂ ≔ P₁ [ l ↦ T₂ ]ᴾ )
           (H∈P₂ : H ↦ Tᴴ ∈ᴾ P₂)
           (sch : Σ₁ ⟶ Σ₂ ↑ ⟪ l , n , Fork H (lengthᵀ Tᴴ) l⊑H ⟫ )
           (u₂ᴾ : P₃ ≔ P₂ [ H ↦ Tᴴ ▻ ⟨ tᴴ , [] ⟩ ]ᴾ ) ->  -- TODO must add deepDup!
           Stepᶜ l n ⟨ Σ₁ , Ms , Γ₁ , P₁ ⟩ ⟨ Σ₂ , Ms , Γ₂ , P₃ ⟩

  fork∙ :  ∀ {H π₁ π₂ τ₂ S₁ S₂ Ms Σ₁ Σ₂} {tᴴ : Term π₁ (Mac H _)} {t₂ : Term π₂ τ₂} {Γ₁ Γ₂ : Heaps ls}
             {P₁ P₂ : Pools ls} {T₁ T₂ : Pool l} {l⊑H : l ⊑ H}
           (l∈P : l ↦ T₁ ∈ᴾ P₁)
           (t∈T : n ↦ ⟨ fork∙ l⊑H tᴴ , S₁ ⟩ ∈ᵀ T₁)
           (uᵀ : T₂ ≔ T₁ [ n ↦ ⟨ t₂ , S₂ ⟩ ]ᵀ )
           (uᴾ : P₂ ≔ P₁ [ l ↦ T₂ ]ᴾ )
           (sch : Σ₁ ⟶ Σ₂ ↑ ⟪ l , n , Step ⟫) ->
           Stepᶜ l n ⟨ Σ₁ , Ms , Γ₁ , P₁ ⟩ ⟨ Σ₂ , Ms , Γ₂ , P₂ ⟩

  skip : ∀ {Σ₁ Σ₂ τ π Ms S} {t : Term π τ} {Γ : Heaps ls} {P : Pools ls} {T : Pool l}
            (l∈P : l ↦ T ∈ᴾ P)
            (t∈T : n ↦ ⟨ t , S ⟩ ∈ᵀ T)
            (stuck : Stuckᴾ ⟨ Ms , Γ , t , S ⟩)
            (sch : Σ₁ ⟶ Σ₂ ↑ ⟪ l , n , Skip ⟫ ) ->
            Stepᶜ l n ⟨ Σ₁ , Ms , Γ , P ⟩ ⟨ Σ₂ , Ms , Γ , P ⟩

  done : ∀ {Σ₁ Σ₂ τ π Ms S} {t : Term π τ} {Γ : Heaps ls} {P : Pools ls} {T : Pool l}
            (l∈P : l ↦ T ∈ᴾ P)
            (t∈T : n ↦ ⟨ t , S ⟩ ∈ᵀ T)
            (don : Doneᴾ ⟨ Ms , Γ , t , S ⟩)
            (sch : Σ₁ ⟶ Σ₂ ↑ ⟪ l , n , Done ⟫ ) ->
            Stepᶜ l n ⟨ Σ₁ , Ms , Γ , P ⟩ ⟨ Σ₂ , Ms , Γ , P ⟩

open import Data.Product hiding (Σ ; _,_)

_⊢_↪_ : ∀ {ls} -> Label × ℕ -> Global ls -> Global ls -> Set
x ⊢ g₁ ↪ g₂ = Stepᶜ (proj₁ x) (proj₂ x) g₁ g₂

open import Scheduler 𝓛 using (Event)

getEvent : ∀ {ls x} {g₁ g₂ : Global ls} -> x ⊢ g₁ ↪ g₂ -> Event (proj₁ x)
getEvent (step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ) = Step
getEvent (fork {H = H} {Tᴴ = Tᴴ} {l⊑H = l⊑H} l∈P t∈T uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ) = Fork H (lengthᵀ Tᴴ) l⊑H
getEvent (fork∙ l∈P t∈T uᵀ uᴾ sch) = Step
getEvent (skip l∈P t∈T stuck sch) = Skip
getEvent (done l∈P t∈T don sch) = Done

getSchStep : ∀ {ls x} {g₁ g₂ : Global ls} -> (s : x ⊢ g₁ ↪ g₂) -> Σ g₁ ⟶ Σ g₂ ↑ ⟪ proj₁ x , proj₂ x , getEvent s ⟫
getSchStep (step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ) = sch
getSchStep (fork l∈P t∈T uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ) = sch
getSchStep (fork∙ l∈P t∈T uᵀ uᴾ sch) = sch
getSchStep (skip l∈P t∈T stuck sch) = sch
getSchStep (done l∈P t∈T don sch) = sch

-- -- An auxiliary data type that externalizes a global-step event.
-- data _⊢ᴹ_↪_ {ls} : ∀ {l} -> Message l -> Global ls -> Global ls -> Set where
--   withMsg : ∀ {l n g₁ g₂} -> (s : l , n ⊢ g₁ ↪ g₂) -> (l , n , (getEvent s)) ⊢ᴹ g₁ ↪ g₂

-- Transitive closure of the concurrent small step
data _↪⋆_ {ls : List Label} : Global ls -> Global ls -> Set where

  -- Zero steps
  [] : ∀ {g} -> g ↪⋆ g

  -- More steps
  _∷_ : ∀ {g₁ g₂ g₃ x} -> x ⊢ g₁ ↪ g₂ -> g₂ ↪⋆ g₃ -> g₁ ↪⋆ g₃


-- -- Concatenates two multiple steps reductions
-- _++ˢ_ : ∀ {ls} {g₁ g₂ g₃ : Global ls} -> g₁ ↪⋆ g₂ -> g₂ ↪⋆ g₃ -> g₁ ↪⋆ g₃
-- [] ++ˢ ss₂ = ss₂
-- (s ∷ ss₁) ++ˢ ss₂ = s ∷ (ss₁ ++ˢ ss₂)
