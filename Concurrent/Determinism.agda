import Lattice as L
import Scheduler as S

module Concurrent.Determinism (𝓛 : L.Lattice) (𝓢 : S.Scheduler 𝓛) where

open import Sequential.Calculus 𝓛
open import Sequential.Semantics 𝓛
open import Sequential.Determinism 𝓛
--------------------------------------------------------------------------------
-- Temporarily side-step bug #2245

import Concurrent.Calculus as C
open C 𝓛 𝓢
-- open import Concurrent.Calculus 𝓛 𝓢

import Concurrent.Semantics as CS
open CS 𝓛 𝓢
-- open import Concurrent.Semantics 𝓛 𝓢 public

open S.Scheduler 𝓛 𝓢

--------------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality


memberᴾ-≡ : ∀ {l ls} {P : Pools ls} {T₁ T₂ : Pool l} -> l ↦ T₁ ∈ᴾ P -> l ↦ T₂ ∈ᴾ P -> T₁ ≡ T₂
memberᴾ-≡ C.here C.here = refl
memberᴾ-≡ C.here (C.there {u = u} y) = ⊥-elim (∈-not-unique (memberᴾ-∈ y) u)
memberᴾ-≡ (C.there {u = u} x) C.here = ⊥-elim (∈-not-unique (memberᴾ-∈ x) u)
memberᴾ-≡ (C.there x) (C.there y) = memberᴾ-≡ x y

memberᵀ-≡ : ∀ {n l} {T : Pool l} {t₁ t₂ : Thread l} -> n ↦ t₁ ∈ᵀ T -> n ↦ t₂ ∈ᵀ T -> t₁ ≡ t₂
memberᵀ-≡ C.here C.here = refl
memberᵀ-≡ (C.there x) (C.there y) = memberᵀ-≡ x y

updateᵀ-≡ : ∀ {n l} {T₁ T₂ T₃ : Pool l} {t : Thread l} -> T₂ ≔ T₁ [ n ↦ t ]ᵀ -> T₃ ≔ T₁ [ n ↦ t ]ᵀ -> T₂ ≡ T₃
updateᵀ-≡ C.here C.here = refl
updateᵀ-≡ (C.there x) (C.there y) rewrite updateᵀ-≡ x y = refl

updateᴾ-≡ : ∀ {l ls} {P₁ P₂ P₃ : Pools ls} {T : Pool l} -> P₂ ≔ P₁ [ l ↦ T ]ᴾ -> P₃ ≔ P₁ [ l ↦ T ]ᴾ -> P₂ ≡ P₃
updateᴾ-≡ C.here C.here = refl
updateᴾ-≡ C.here (C.there {u = u} y) = ⊥-elim (∈-not-unique (updateᴾ-∈ y) u)
updateᴾ-≡ (C.there {u = u} x) C.here = ⊥-elim (∈-not-unique (updateᴾ-∈ x) u)
updateᴾ-≡ (C.there x) (C.there y) rewrite updateᴾ-≡ x y = refl

determinismᶜ : ∀ {ls l n} {g₁ g₂ g₃ : Global ls} -> (l , n) ⊢ g₁ ↪ g₂ -> (l , n) ⊢ g₁ ↪ g₃ -> g₂ ≡ g₃
determinismᶜ (CS.step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ) (CS.step-∅ l∈P₁ t∈T₁ ¬fork₁ step₁ sch₁ uᵀ₁ uᴾ₁)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | refl with determinismᴾ step step₁
... | refl rewrite determinismˢ sch sch₁ | updateᵀ-≡ uᵀ uᵀ₁ | updateᴾ-≡ uᴾ uᴾ₁ = refl
determinismᶜ (CS.step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ) (CS.fork l∈P₁ t∈T₁ step₁ uᵀ₁ u₁ᴾ H∈P₂ sch₁ u₂ᴾ)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | refl = ⊥-elim (¬fork (Fork _ _))
determinismᶜ (CS.step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ) (CS.fork∙ l∈P₁ t∈T₁ step₁ uᵀ₁ u₁ᴾ sch₁)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | refl = ⊥-elim (¬fork (Fork∙ _ _))
determinismᶜ (CS.step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ) (CS.skip l∈P₁ t∈T₁ stuck sch₁)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | refl = ⊥-elim (⊥-stuckSteps stuck (Step step))
determinismᶜ (CS.step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ) (CS.done l∈P₁ t∈T₁ don sch₁)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | refl = ⊥-elim (⊥-doneSteps don (Step step))
determinismᶜ (CS.fork l∈P t∈T step uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ) (CS.step-∅ l∈P₁ t∈T₁ ¬fork step₁ sch₁ uᵀ₁ uᴾ)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | refl = ⊥-elim (¬fork (Fork _ _))
determinismᶜ (CS.fork l∈P t∈T step uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ) (CS.fork l∈P₁ t∈T₁ step₁ uᵀ₁ u₁ᴾ₁ H∈P₃ sch₁ u₂ᴾ₁)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | refl with determinismᴾ step step₁
... | refl rewrite updateᵀ-≡ uᵀ uᵀ₁ | updateᴾ-≡ u₁ᴾ u₁ᴾ₁ | memberᴾ-≡ H∈P₂ H∈P₃ | updateᴾ-≡ u₂ᴾ u₂ᴾ₁ | determinismˢ sch sch₁ = refl
determinismᶜ (CS.fork l∈P t∈T step uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ) (CS.fork∙ l∈P₁ t∈T₁ step₁ uᵀ₁ u₁ᴾ₁ sch₁)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | ()
determinismᶜ (CS.fork l∈P t∈T step uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ) (CS.skip l∈P₁ t∈T₁ stuck sch₁)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | refl = ⊥-elim (⊥-stuckSteps stuck (Step step))
determinismᶜ (CS.fork l∈P t∈T step uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ) (CS.done l∈P₁ t∈T₁ don sch₁)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | refl = ⊥-elim (⊥-doneSteps don (Step step))
determinismᶜ (CS.fork∙ l∈P t∈T step uᵀ u₁ᴾ sch) (CS.step-∅ l∈P₁ t∈T₁ ¬fork step₁ sch₁ uᵀ₁ uᴾ)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | refl = ⊥-elim (¬fork (Fork∙ _ _))
determinismᶜ (CS.fork∙ l∈P t∈T step uᵀ u₁ᴾ sch) (CS.fork l∈P₁ t∈T₁ step₁ uᵀ₁ u₁ᴾ₁ H∈P₂ sch₁ u₂ᴾ)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | ()
determinismᶜ (CS.fork∙ l∈P t∈T step uᵀ uᴾ sch) (CS.fork∙ l∈P₁ t∈T₁ step₁ uᵀ₁ uᴾ₁ sch₁)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | refl with determinismᴾ step step₁
... | refl rewrite determinismˢ sch sch₁ | updateᵀ-≡ uᵀ uᵀ₁ | updateᴾ-≡ uᴾ uᴾ₁ = refl
determinismᶜ (CS.fork∙ l∈P t∈T step uᵀ u₁ᴾ sch) (CS.skip l∈P₁ t∈T₁ stuck sch₁)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | refl = ⊥-elim (⊥-stuckSteps stuck (Step step))
determinismᶜ (CS.fork∙ l∈P t∈T step uᵀ u₁ᴾ sch) (CS.done l∈P₁ t∈T₁ don sch₁)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | refl = ⊥-elim (⊥-doneSteps don (Step step))
determinismᶜ (CS.skip l∈P t∈T stuck sch) (CS.step-∅ l∈P₁ t∈T₁ ¬fork step sch₁ uᵀ uᴾ)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | refl = ⊥-elim (⊥-stuckSteps stuck (Step step))
determinismᶜ (CS.skip l∈P t∈T stuck sch) (CS.fork l∈P₁ t∈T₁ step uᵀ u₁ᴾ H∈P₂ sch₁ u₂ᴾ)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | refl = ⊥-elim (⊥-stuckSteps stuck (Step step))
determinismᶜ (CS.skip l∈P t∈T stuck sch) (CS.fork∙ l∈P₁ t∈T₁ step uᵀ u₁ᴾ sch₁)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | refl = ⊥-elim (⊥-stuckSteps stuck (Step step))
determinismᶜ (CS.skip l∈P t∈T stuck sch) (CS.skip l∈P₁ t∈T₁ stuck₁ sch₁)
  rewrite memberᴾ-≡ l∈P l∈P₁ | determinismˢ sch sch₁ = refl
determinismᶜ (CS.skip l∈P t∈T stuck sch) (CS.done l∈P₁ t∈T₁ don sch₁)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | refl = ⊥-elim (⊥-stuckDone stuck don)
determinismᶜ (CS.done l∈P t∈T don sch) (CS.step-∅ l∈P₁ t∈T₁ ¬fork step sch₁ uᵀ uᴾ)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | refl = ⊥-elim (⊥-doneSteps don (Step step))
determinismᶜ (CS.done l∈P t∈T don sch) (CS.fork l∈P₁ t∈T₁ step uᵀ u₁ᴾ H∈P₂ sch₁ u₂ᴾ)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | refl = ⊥-elim (⊥-doneSteps don (Step step))
determinismᶜ (CS.done l∈P t∈T don sch) (CS.fork∙ l∈P₁ t∈T₁ step uᵀ u₁ᴾ sch₁)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | refl = ⊥-elim (⊥-doneSteps don (Step step))
determinismᶜ (CS.done l∈P t∈T don sch) (CS.skip l∈P₁ t∈T₁ stuck sch₁)
  rewrite memberᴾ-≡ l∈P l∈P₁ with memberᵀ-≡ t∈T t∈T₁
... | refl = ⊥-elim (⊥-stuckDone stuck don)
determinismᶜ (CS.done l∈P t∈T don sch) (CS.done l∈P₁ t∈T₁ don₁ sch₁)
  rewrite determinismˢ sch sch₁ = refl
