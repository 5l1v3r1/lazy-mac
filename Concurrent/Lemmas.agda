import Lattice as L
import Scheduler as S
open import Scheduler.Security

module Concurrent.Lemmas {𝓛 : L.Lattice} {𝓢 : S.Scheduler 𝓛} (A : L.Label 𝓛) (𝓝 : NIˢ 𝓛 A 𝓢) where

open import Types 𝓛
open import Data.Product using (∃ ; _×_ ; proj₁ ; proj₂ )
import Data.Product as P

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
--------------------------------------------------------------------------------
-- Temporarily side-step bug #2245

import Sequential.Calculus as SC
open SC 𝓛


import Concurrent.Calculus as C
open C 𝓛 𝓢
-- open import Concurrent.Calculus 𝓛 𝓢

import Concurrent.Semantics as CS
open CS 𝓛 𝓢
-- open import Concurrent.Semantics 𝓛 𝓢 public

open import Sequential.Erasure 𝓛 A as SE hiding (εᵀ ; εᴾ ; εˢ)
open import Sequential.PINI 𝓛 A using (stepᴸ ; stepᴴ-≅ᴹ ; stepᴴ-≅ᴴ)

--------------------------------------------------------------------------------

open Scheduler.Security.NIˢ 𝓛 A 𝓝 renaming (State to Stateˢ)
open import Concurrent.Erasure A 𝓝

open import Concurrent.LowEq A 𝓝 as L₁

open import Data.Product renaming (_,_ to ⟨_,_⟩)

-- Square
εᴳ-simᴸ : ∀ {l n ls} {g₁ g₂ : Global ls} -> l ⊑ A ->  ⟨ l , n ⟩ ⊢ g₁ ↪ g₂ -> ⟨ l , n ⟩ ⊢ (εᴳ g₁) ↪ (εᴳ g₂)
εᴳ-simᴸ l⊑A (CS.step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ)
  = step-∅ (memberᴾ l⊑A l∈P) (memberᵀ l⊑A t∈T) (εᵀˢ¬IsForkTS l⊑A ¬fork) (stepᴸ l⊑A step) (εˢ-simᴸ l⊑A sch) (updateᵀ l⊑A uᵀ) (updateᴾ l⊑A uᴾ)
εᴳ-simᴸ l⊑A (CS.fork {H = H} {tᴴ = tᴴ} {Tᴴ = Tᴴ} l∈P t∈T uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ) with memberᵀ l⊑A t∈T | εˢ-simᴸ l⊑A sch
... | t∈T' | sch' with H ⊑? A
... | yes H⊑A rewrite lengthᵀ-ε-≡ H⊑A Tᴴ
    = fork (memberᴾ l⊑A l∈P) t∈T' (updateᵀ l⊑A uᵀ) (updateᴾ l⊑A u₁ᴾ) (memberᴾ H⊑A H∈P₂) sch' (updateᴾ-▻ Tᴴ (⟨ tᴴ , [] ⟩) H⊑A u₂ᴾ)
εᴳ-simᴸ l⊑A (CS.fork {tᴴ = tᴴ} {P₂ = P₂} {Tᴴ = Tᴴ} l∈P t∈T uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ) | t∈T' | sch' | no H⋤A
  rewrite newᴾ∙ Tᴴ ⟨ tᴴ , [] ⟩ H⋤A u₂ᴾ = fork∙ {P₂ = map-εᴾ P₂} (memberᴾ l⊑A l∈P) t∈T' (updateᵀ l⊑A uᵀ) (updateᴾ l⊑A u₁ᴾ) sch'
εᴳ-simᴸ l⊑A (CS.fork∙ l∈P t∈T uᵀ u₁ᴾ sch)
  = fork∙ (memberᴾ l⊑A l∈P) (memberᵀ l⊑A t∈T) (updateᵀ l⊑A uᵀ) (updateᴾ l⊑A u₁ᴾ) (εˢ-simᴸ l⊑A sch)
εᴳ-simᴸ l⊑A (CS.skip l∈P t∈T stuck sch) = skip (memberᴾ l⊑A l∈P) (memberᵀ l⊑A t∈T) (stuck-ε l⊑A stuck) (εˢ-simᴸ l⊑A sch)
εᴳ-simᴸ l⊑A (CS.done l∈P t∈T don sch) = done (memberᴾ l⊑A l∈P) (memberᵀ l⊑A t∈T) (done-ε l⊑A don) (εˢ-simᴸ l⊑A sch)


-- Triangle
εᴳ-simᴴ : ∀ {H n ls} {g₁ g₂ : Global ls} -> H ⋤ A -> ⟨ H , n ⟩ ⊢ g₁ ↪ g₂ -> g₁ ≅ᴳ g₂
εᴳ-simᴴ H⋤A (CS.step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ)
  = lift-εᴳ (⌞ εˢ-simᴴ H⋤A sch ⌟) (stepᴴ-≅ᴹ H⋤A step) (stepᴴ-≅ᴴ H⋤A step) (updateᴾ∙ H⋤A uᴾ)
εᴳ-simᴴ H⋤A (CS.fork {l⊑H = L⊑H} l∈P t∈T uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ)
  = lift-εᴳ (⌞ εˢ-simᴴ H⋤A sch ⌟) refl refl (trans (updateᴾ∙ H⋤A u₁ᴾ) (updateᴾ∙ (trans-⋤ L⊑H H⋤A) u₂ᴾ))
εᴳ-simᴴ H⋤A (CS.fork∙ l∈P t∈T uᵀ u₁ᴾ sch) = lift-εᴳ (⌞ εˢ-simᴴ H⋤A sch ⌟) refl refl (updateᴾ∙ H⋤A u₁ᴾ)
εᴳ-simᴴ H⋤A (CS.skip l∈P t∈T stuck sch) = lift-εᴳ (⌞ εˢ-simᴴ H⋤A sch ⌟) refl refl refl
εᴳ-simᴴ H⋤A (CS.done l∈P t∈T don sch) = lift-εᴳ (⌞ εˢ-simᴴ H⋤A sch ⌟) refl refl refl


--------------------------------------------------------------------------------

-- TODO move to Concurrent.LowEq ?

open import Function

import Sequential.LowEq  𝓛 A as L₂ renaming (_≈ᵀˢ⟨_⟩_ to _≈ᵀᴴ⟨_⟩_ ; ⌞_⌟ᵀˢ to ⌞_⌟ᵀᴴ ; ⌜_⌝ᵀˢ to ⌜_⌝ᵀᴴ)
open L₂

open import Concurrent.Graph A 𝓝

memberᴾ-≈ : ∀ {ls L} {T₁ : Pool L} {P₁ P₂ : Pools ls} -> (x : Dec (L ⊑ A)) -> L ↦ T₁ ∈ᴾ P₁ -> P₁ L₁.map-≈ᴾ P₂ -> ∃ (λ T₂ -> T₁ L₁.≈ᴾ⟨ x ⟩ T₂ × L ↦ T₂ ∈ᴾ P₂)
memberᴾ-≈ x C.here (K-mapᴾ (e₁ ◅ e₂) (e₃ ◅ e₄)) = ⟨ _ , ⟨ ext-≈ᴾ (Kᴾ e₁ e₃) x , here ⟩ ⟩
memberᴾ-≈ x (C.there L∈P) (K-mapᴾ (x₁ ◅ x₂) (x₃ ◅ x₄)) = P.map id (P.map id there) (memberᴾ-≈ x L∈P (K-mapᴾ x₂ x₄))

memberᵀ-≈ : ∀ {n L} {T₁ T₂ : Pool L} {t₁ : Thread L} -> (L⊑A : L ⊑ A) -> n ↦ t₁ ∈ᵀ T₁ -> T₁ L₁.≈ᴾ⟨ yes L⊑A ⟩ T₂
              -> ∃ (λ t₂ → (t₁ ≈ᵀᴴ⟨ yes L⊑A ⟩ t₂) × n ↦ t₂ ∈ᵀ T₂)
memberᵀ-≈ L⊑A C.here (Kᴾ (Mapᵀ (e ◅ e₁)) (Mapᵀ (e' ◅ e₁'))) = ⟨ _ , ⟨ (Kᵀˢ e e') , here ⟩ ⟩
memberᵀ-≈ L⊑A (C.there n∈T) (Kᴾ (Mapᵀ (e ◅ e₁)) (Mapᵀ (e' ◅ e₁'))) = P.map id (P.map id there) (memberᵀ-≈ L⊑A n∈T (Kᴾ (Mapᵀ e₁) (Mapᵀ e₁')))

updateᵀ-≈ : ∀ {n L} {T₁ T₁' T₂ : Pool L} {t₁ t₂ : Thread L} -> (L⊑A : L ⊑ A) -> T₁' ≔ T₁ [ n ↦ t₁ ]ᵀ ->
            T₁ L₁.≈ᴾ⟨ yes L⊑A ⟩ T₂ -> t₁ ≈ᵀᴴ⟨ yes L⊑A ⟩ t₂ -> ∃ (λ T₂' → T₁' L₁.≈ᴾ⟨ yes L⊑A ⟩ T₂'  × T₂' ≔ T₂ [ n ↦ t₂ ]ᵀ)
updateᵀ-≈ L⊑A C.here (Kᴾ (Mapᵀ (_ ◅ e₁)) (Mapᵀ (_ ◅ e₁'))) (Kᵀˢ e e') = ⟨ _ , ⟨ (Kᴾ (Mapᵀ (e ◅ e₁)) (Mapᵀ (e' ◅ e₁'))) , here ⟩ ⟩
updateᵀ-≈ L⊑A (C.there u) (Kᴾ (Mapᵀ (e ◅ e₁)) (Mapᵀ (e' ◅ e₁'))) eq₂
  = P.map (_◅_ _) (P.map (cons≈ᴾ (Kᵀˢ e e')) there) (updateᵀ-≈ L⊑A u (Kᴾ (Mapᵀ e₁) (Mapᵀ e₁')) eq₂)

updateᴾ-≈ : ∀ {l ls} {P₁ P₂ P₁' : Pools ls} {T₁ T₂ : Pool l}  (x : Dec (l ⊑ A)) -> P₁' ≔ P₁ [ l ↦ T₁ ]ᴾ ->
             P₁ map-≈ᴾ P₂ -> T₁ L₁.≈ᴾ⟨ x ⟩ T₂ -> ∃ (λ P₂' → P₁' map-≈ᴾ P₂' × P₂' ≔ P₂ [ l ↦ T₂ ]ᴾ)
updateᴾ-≈ {l} x C.here (K-mapᴾ (_ ◅ e₁) (_ ◅ e₁')) (Kᴾ e e') = ⟨ _ , ⟨ K-mapᴾ (ext-εᴾ e (l ⊑? A) ◅ e₁) (ext-εᴾ e' (l ⊑? A) ◅ e₁') , here ⟩ ⟩
updateᴾ-≈ x (C.there u₁) (K-mapᴾ (e ◅ e₁) (e' ◅ e₁')) eq₂ = P.map (_◅_ _) (P.map (cons-map-≈ᵀ (Kᴾ e e')) there) (updateᴾ-≈ x u₁ (K-mapᴾ e₁ e₁') eq₂)

-- lengthᵀ-≈ : ∀ {l} {T₁ T₂ : Pool l} -> (l⊑A : l ⊑ A) -> T₁ L₁.≈ᴾ⟨ yes l⊑A ⟩ T₂ -> lengthᵀ T₁ ≡ lengthᵀ T₂
-- lengthᵀ-≈ {_} {T₁} {T₂} l⊑A T₁≈T₂ rewrite lengthᵀ-ε-≡ l⊑A T₁ | lengthᵀ-ε-≡ l⊑A T₂ = {!!} -- | ⌞ T₁≈T₂ ⌟ᵀ = refl

-- newᵀ-≈ : ∀ {l} {T₁ T₂ : Pool l} {t₁ t₂ : Thread l} {x : Dec _} -> T₁ L₁.≈ᴾ⟨ x ⟩ T₂ -> t₁ ≈ᵀᴴ⟨ x ⟩ t₂ -> (T₁ ▻ t₁) L₁.≈ᴾ⟨ x ⟩ (T₂ ▻ t₂)
-- newᵀ-≈ T₁≈T₂ t₁≈t₂ = {!!}


-- TODO move to Sequential LowEq?

-- import Sequential.Graph 𝓛 A as G
-- open import Sequential.Semantics 𝓛

-- val-≈ : ∀ {π τ} {t₁ t₂ : Term π τ} -> t₁ L₂.≈ᵀ t₂ -> Value t₁ -> Value t₂
-- val-≈ ⟨ e₁ , e₂ ⟩ val = {!!} -- valᴱ e₂ (val₁ᴱ e₁ val)

-- stuck-≈ : ∀ {l ls τ} {p₁ p₂ : Program l ls τ} (l⊑A : l ⊑ A) -> p₁ L₂.≈ᴾ⟨ (yes l⊑A) ⟩ p₂ -> Stuckᴾ p₁ -> Stuckᴾ p₂
-- stuck-≈ l⊑A eq stuck₁ = {!!}

-- ¬fork-≈ : ∀ {π τ} {t₁ t₂ : Term π τ} -> t₁ L₂.≈ᵀ t₂ -> ¬ (IsFork t₁) -> ¬ (IsFork t₂)
-- ¬fork-≈ ⟨ G.unId e₁ , () ⟩ ¬fork₁ (SC.Fork p t₁)
-- ¬fork-≈ ⟨ G.Var τ∈π , () ⟩ ¬fork₁ (SC.Fork p t)
-- ¬fork-≈ ⟨ G.App e₂ e₁ , () ⟩ ¬fork₁ (SC.Fork p t)
-- ¬fork-≈ ⟨ G.If e₁ Then e₂ Else e₃ , () ⟩ ¬fork₁ (SC.Fork p t)
-- ¬fork-≈ ⟨ G.Return e₁ , () ⟩ ¬fork₁ (SC.Fork p t₁)
-- ¬fork-≈ ⟨ e₁ G.>>= e₂ , () ⟩ ¬fork₁ (SC.Fork p t)
-- ¬fork-≈ ⟨ G.Mac e₁ , () ⟩ ¬fork₁ (SC.Fork p t₁)
-- ¬fork-≈ ⟨ G.unlabel l⊑h e₁ , () ⟩ ¬fork₁ (SC.Fork p t₁)
-- ¬fork-≈ ⟨ G.read l⊑h e₁ , () ⟩ ¬fork₁ (SC.Fork p t₁)
-- ¬fork-≈ ⟨ G.write l⊑h h⊑A e₁ e₂ , () ⟩ ¬fork₁ (SC.Fork p t)
-- ¬fork-≈ ⟨ G.write' l⊑h h⋤A e₁ e₂ , () ⟩ ¬fork₁ (SC.Fork p t)
-- ¬fork-≈ ⟨ G.write∙ l⊑h e₁ e₂ , () ⟩ ¬fork₁ (SC.Fork p t)
-- ¬fork-≈ ⟨ G.fork l⊑h h⊑A e₁ , G.fork .l⊑h h⊑A₁ e₂ ⟩ ¬fork₁ (SC.Fork .l⊑h t₁) = ¬fork₁ (SC.Fork l⊑h _)
-- ¬fork-≈ ⟨ G.fork' l⊑h h⋤A e₁ , G.fork' .l⊑h h⋤A₁ e₂ ⟩ ¬fork₁ (SC.Fork .l⊑h t₁) = ¬fork₁ (SC.Fork l⊑h _)
-- ¬fork-≈ ⟨ G.fork∙ l⊑h e₁ , G.fork' .l⊑h h⋤A e₂ ⟩ ¬fork₁ (SC.Fork .l⊑h t₁) = ¬fork₁ (SC.Fork∙ l⊑h _)
-- ¬fork-≈ ⟨ G.deepDup e₁ , () ⟩ ¬fork₁ (SC.Fork p t₁)
-- ¬fork-≈ ⟨ G.∙ , () ⟩ ¬fork₁ (SC.Fork p t)
-- ¬fork-≈ ⟨ G.fork' p h⋤A e₁ , G.fork∙ .p e₂ ⟩ ¬fork₁ (SC.Fork∙ .p t₁) = ¬fork₁ (SC.Fork p _)
-- ¬fork-≈ ⟨ G.fork∙ p e₁ , G.fork∙ .p e₂ ⟩ ¬fork₁ (SC.Fork∙ .p t₁) = ¬fork₁ (SC.Fork∙ p _)

-- redex-≈ : ∀ {l ls τ} {p₁ p₁' p₂ : Program l ls τ} -> (l⊑A : l ⊑ A) -> p₁ L₂.≈ᴾ⟨ (yes l⊑A) ⟩ p₂ -> p₁ ⟼ p₁' ->
--             ∃ (λ p₂' -> (p₁' L₂.≈ᴾ⟨ yes l⊑A ⟩ p₂') × (p₂ ⟼ p₂'))
-- redex-≈ = {!!}
