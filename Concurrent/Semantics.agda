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

-- TODO I think that we can remove l n from the plain step and define
-- a wrapper data-type that extracts it.
data Stepᶜ (l : Label) (n : ℕ) {ls} : Global ls -> Global ls -> Set where
  step-∅ : ∀ {Σ₁ Σ₂ Ms₁ Ms₂} {Ts₁ Ts₂ : Thread l} {Γ₁ Γ₂ : Heaps ls} {P₁ P₂ : Pools ls} {T₁ T₂ : Pool l}
           (l∈P : l ↦ T₁ ∈ᴾ P₁)
           (t∈T : n ↦ Ts₁ ∈ᵀ T₁)
           (¬fork : ¬ (IsForkTS Ts₁))
           (step : ⟨ Ms₁ , Γ₁ , Ts₁ ⟩ ⟼ ⟨ Ms₂ , Γ₂ , Ts₂ ⟩)
           (sch : Σ₁ ⟶ Σ₂ ↑ ⟪ l , n , Step ⟫ )
           (uᵀ : T₂ ≔ T₁ [ n ↦  Ts₂  ]ᵀ )
           (uᴾ : P₂ ≔ P₁ [ l ↦ T₂ ]ᴾ ) ->
           Stepᶜ l n ⟨ Σ₁ , Ms₁ , Γ₁ , P₁ ⟩ ⟨ Σ₂ , Ms₂ , Γ₂ , P₂ ⟩

  fork :  ∀ {H π S Ms Σ₁ Σ₂} {tᴴ : Term π (Mac H _)} {Γ : Heaps ls}
            {P₁ P₂ P₃ : Pools ls} {T₁ T₂ : Pool l} {Tᴴ : Pool H} {l⊑H : l ⊑ H}
           (l∈P : l ↦ T₁ ∈ᴾ P₁)
           (t∈T : n ↦ ⟨ fork l⊑H tᴴ , S ⟩ ∈ᵀ T₁)
           (uᵀ : T₂ ≔ T₁ [ n ↦ ⟨ Return _ （） , S ⟩ ]ᵀ )
           (u₁ᴾ : P₂ ≔ P₁ [ l ↦ T₂ ]ᴾ )
           (H∈P₂ : H ↦ Tᴴ ∈ᴾ P₂)
           (sch : Σ₁ ⟶ Σ₂ ↑ ⟪ l , n , Fork H (lengthᵀ Tᴴ) l⊑H ⟫ )
           (u₂ᴾ : P₃ ≔ P₂ [ H ↦ Tᴴ ▻ ⟨ tᴴ , [] ⟩ ]ᴾ ) ->  -- TODO must add deepDup!
           Stepᶜ l n ⟨ Σ₁ , Ms , Γ , P₁ ⟩ ⟨ Σ₂ , Ms , Γ , P₃ ⟩

  fork∙ :  ∀ {H π S Ms Σ₁ Σ₂} {tᴴ : Term π (Mac H _)} {Γ : Heaps ls}
             {P₁ P₂ : Pools ls} {T₁ T₂ : Pool l} {l⊑H : l ⊑ H}
           (l∈P : l ↦ T₁ ∈ᴾ P₁)
           (t∈T : n ↦ ⟨ fork∙ l⊑H tᴴ , S ⟩ ∈ᵀ T₁)
           (uᵀ : T₂ ≔ T₁ [ n ↦ ⟨ Return _ （） , S ⟩ ]ᵀ )
           (uᴾ : P₂ ≔ P₁ [ l ↦ T₂ ]ᴾ )
           (sch : Σ₁ ⟶ Σ₂ ↑ ⟪ l , n , Step ⟫) ->
           Stepᶜ l n ⟨ Σ₁ , Ms , Γ , P₁ ⟩ ⟨ Σ₂ , Ms , Γ , P₂ ⟩

  skip : ∀ {Σ₁ Σ₂ Ms} {Ts : Thread _} {Γ : Heaps ls} {P : Pools ls} {T : Pool l}
            (l∈P : l ↦ T ∈ᴾ P)
            (t∈T : n ↦ Ts ∈ᵀ T)
            (stuck : Stuckᴾ ⟨ Ms , Γ , Ts ⟩)
            (sch : Σ₁ ⟶ Σ₂ ↑ ⟪ l , n , Skip ⟫ ) ->
            Stepᶜ l n ⟨ Σ₁ , Ms , Γ , P ⟩ ⟨ Σ₂ , Ms , Γ , P ⟩

  done : ∀ {Σ₁ Σ₂ Ms} {Ts : Thread _} {Γ : Heaps ls} {P : Pools ls} {T : Pool l}
            (l∈P : l ↦ T ∈ᴾ P)
            (t∈T : n ↦ Ts ∈ᵀ T)
            (don : Doneᴾ ⟨ Ms , Γ , Ts ⟩)
            (sch : Σ₁ ⟶ Σ₂ ↑ ⟪ l , n , Done ⟫ ) ->
            Stepᶜ l n ⟨ Σ₁ , Ms , Γ , P ⟩ ⟨ Σ₂ , Ms , Γ , P ⟩

open import Data.Product hiding (Σ ; _,_)

data NextThread {ls} (l : Label) (n : ℕ) (g : Global ls) : Set where
  next : {T : Pool l} (Ts : Thread _) -> (l∈P : l ↦ T ∈ᴾ (P g)) (t∈T : n ↦ Ts ∈ᵀ T) -> NextThread l n g

_⊢_↪_ : ∀ {ls} -> Label × ℕ -> Global ls -> Global ls -> Set
x ⊢ g₁ ↪ g₂ = Stepᶜ (proj₁ x) (proj₂ x) g₁ g₂

nextThread : ∀ {ls} {x : Label × ℕ} {g₁ g₂ : Global ls} -> x ⊢ g₁ ↪ g₂ -> Thread (proj₁ x)
nextThread (step-∅ {Ts₁ = Ts₁} l∈P t∈T ¬fork step sch uᵀ uᴾ) = Ts₁
nextThread (fork {S = S} {tᴴ = tᴴ} {l⊑H = l⊑H} l∈P t∈T uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ) = ⟨ fork l⊑H tᴴ , S ⟩
nextThread (fork∙ {S = S} {tᴴ = tᴴ} {l⊑H = l⊑H} l∈P t∈T uᵀ uᴾ sch) =  ⟨ fork∙ l⊑H tᴴ , S ⟩
nextThread (skip {Ts = Ts} l∈P t∈T stuck sch) = Ts
nextThread (done {Ts = Ts} l∈P t∈T don sch) = Ts

nextPool : ∀ {ls} {x : Label × ℕ} {g₁ g₂ : Global ls} -> x ⊢ g₁ ↪ g₂ -> Pool (proj₁ x)
nextPool (step-∅ {T₁ = T₁} l∈T t∈T ¬fork step sch uᵀ uᴾ) = T₁
nextPool (fork {T₁ = T₁} l∈P t∈T uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ) = T₁
nextPool (fork∙ {T₁ = T₁} l∈P t∈T uᵀ uᴾ sch) = T₁
nextPool (skip {T = T} l∈P t∈T stuck sch) = T
nextPool (done {T = T} l∈P t∈T don sch) = T

next-∈ᴾ  : ∀ {ls} {x : Label × ℕ} {g₁ g₂ : Global ls} -> (step : x ⊢ g₁ ↪ g₂) -> (proj₂ x) ↦ (nextThread step) ∈ᵀ (nextPool step)
next-∈ᴾ (step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ) = t∈T
next-∈ᴾ (fork l∈P t∈T uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ) = t∈T
next-∈ᴾ (fork∙ l∈P t∈T uᵀ uᴾ sch) = t∈T
next-∈ᴾ (skip l∈P t∈T stuck sch) = t∈T
next-∈ᴾ (done l∈P t∈T don sch) = t∈T

next-∈ᵀ :  ∀ {ls} {x : Label × ℕ} {g₁ g₂ : Global ls} -> (step : x ⊢ g₁ ↪ g₂) -> (proj₁ x) ↦ (nextPool step) ∈ᴾ (P g₁)
next-∈ᵀ (step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ) = l∈P
next-∈ᵀ (fork l∈P t∈T uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ) = l∈P
next-∈ᵀ (fork∙ l∈P t∈T uᵀ uᴾ sch) = l∈P
next-∈ᵀ (skip l∈P t∈T stuck sch) = l∈P
next-∈ᵀ (done l∈P t∈T don sch) = l∈P

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
