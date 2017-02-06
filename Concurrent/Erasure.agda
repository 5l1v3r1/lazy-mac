import Lattice as L
import Scheduler as S
open import Scheduler.Security

module Concurrent.Erasure {𝓛 : L.Lattice} {𝓢 : S.Scheduler 𝓛} (A : L.Label 𝓛) (𝓝 : NIˢ 𝓛 A 𝓢) where

open import Relation.Nullary
open import Types 𝓛
open import Sequential.Calculus 𝓛
open import Sequential.Semantics 𝓛
open import Sequential.Erasure 𝓛 A as SE hiding (εᵀ ; εᴾ ; εˢ)

--------------------------------------------------------------------------------
-- Temporarily side-step bug #2245
import Concurrent.Calculus as C
open C 𝓛 𝓢
-- open import Concurrent.Calculus 𝓛 𝓢

import Concurrent.Semantics as CS
open CS 𝓛 𝓢
-- open import Concurrent.Semantics 𝓛 𝓢 public
--------------------------------------------------------------------------------

open Scheduler.Security.NIˢ 𝓛 A 𝓝

εᵗ : ∀ {l} ->  Thread l -> Thread l
εᵗ C.⟨ t , S ⟩ = ⟨ SE.εᵀ t , SE.εˢ S ⟩
εᵗ C.∙ = ∙

εᵀ : ∀ {l} -> Dec (l ⊑ A) -> Pool l -> Pool l
εᵀ (yes p) C.[] = []
εᵀ (yes p) (t C.◅ T) = εᵗ t ◅ (εᵀ (yes p) T)
εᵀ (yes p) C.∙ = ∙
εᵀ (no ¬p) T = ∙

open import Relation.Binary.PropositionalEquality
open import Data.Empty

εᵀ-ext-≡ : ∀ {l} -> (x y : Dec (l ⊑ A)) (T : Pool l) -> εᵀ x T ≡ εᵀ y T
εᵀ-ext-≡ (yes p) (yes p₁) C.[] = refl
εᵀ-ext-≡ (yes p) (yes p₁) (t C.◅ T) rewrite εᵀ-ext-≡ (yes p) (yes p₁) T = refl
εᵀ-ext-≡ (yes p) (yes p₁) C.∙ = refl
εᵀ-ext-≡ (yes p) (no ¬p) T = ⊥-elim (¬p p)
εᵀ-ext-≡ (no ¬p) (yes p) T = ⊥-elim (¬p p)
εᵀ-ext-≡ (no ¬p) (no ¬p₁) T = refl

-- Pointwise erasure function for pools
εᴾ : ∀ {ls} -> Pools ls -> Pools ls
εᴾ C.[] = []
εᴾ (T C.◅ P) = (εᵀ (_ ⊑? A) T) ◅ (εᴾ P)

εᴳ : ∀ {ls} -> Global ls -> Global ls
εᴳ C.⟨ Σ , Γ , P ⟩ = C.⟨ εˢ Σ , εᴴ Γ , εᴾ P ⟩

import Data.Product as P

memberᴾ : ∀ {l ls} {T : Pool l} {P : Pools ls} -> (l⊑A : l ⊑ A) -> l ↦ T ∈ᴾ P -> l ↦ (εᵀ (yes l⊑A) T) ∈ᴾ (εᴾ P)
memberᴾ {l} l⊑A C.here with l ⊑? A
memberᴾ {T = T} l⊑A C.here | yes p rewrite εᵀ-ext-≡ (yes l⊑A) (yes p) T = here
memberᴾ l⊑A C.here | no ¬p = ⊥-elim (¬p l⊑A)
memberᴾ l⊑A (C.there x) = there (memberᴾ l⊑A x)

memberᵀ : ∀ {l n τ₁ π} {T : Pool l} {t : Term π τ₁} {S : Stack l _ _} -> (l⊑A : l ⊑ A)
          -> n ↦ ⟨ t , S ⟩ ∈ᵀ T -> n ↦ ⟨ SE.εᵀ t , SE.εˢ S ⟩ ∈ᵀ (εᵀ (yes l⊑A) T)
memberᵀ l⊑A C.here = C.here
memberᵀ l⊑A (C.there x) = C.there (memberᵀ l⊑A x)

updateᵀ : ∀ {l π τ n} {t : Term π τ} {S : Stack l _ _} {T₁ T₂ : Pool l} -> (l⊑A : l ⊑ A) -> T₂ ≔ T₁ [ n ↦ ⟨ t , S ⟩ ]ᵀ ->
          (εᵀ (yes l⊑A) T₂) ≔ (εᵀ (yes l⊑A) T₁) [ n ↦ ⟨ (SE.εᵀ t) , SE.εˢ S ⟩ ]ᵀ
updateᵀ l⊑A C.here = C.here
updateᵀ l⊑A (C.there x) = C.there (updateᵀ l⊑A x)

updateᴾ : ∀ {l ls} {T : Pool l} {P₁ P₂ : Pools ls} -> (l⊑A : l ⊑ A) -> P₂ ≔ P₁ [ l ↦ T ]ᴾ -> (εᴾ P₂) ≔ (εᴾ P₁) [ l ↦ (εᵀ (yes l⊑A) T) ]ᴾ
updateᴾ {l} l⊑A C.here with l ⊑? A
updateᴾ {T = T} l⊑A C.here | yes p rewrite εᵀ-ext-≡ (yes l⊑A) (yes p) T = here
updateᴾ l⊑A C.here | no ¬p = ⊥-elim (¬p l⊑A)
updateᴾ l⊑A (C.there x) = C.there (updateᴾ l⊑A x)


done-ε : ∀ {l ls τ} {p : Program l ls τ} -> (l⊑A : l ⊑ A) -> Doneᴾ p -> Doneᴾ (SE.ε₁ᴾ (yes l⊑A) p)
done-ε l⊑A (Done isVal) = Done (εᵀ-Val isVal)

-- Will probably need the graph of the function
stuck-ε : ∀ {l ls τ} {p : Program l ls τ} -> (l⊑A : l ⊑ A) -> Stuckᴾ p -> Stuckᴾ (SE.ε₁ᴾ (yes l⊑A) p)
stuck-ε {l} {ls} {τ} l⊑A (¬done P., ¬redex) = ε¬done ¬done P., ε¬redex ¬redex
  where ε¬done : {p : Program l ls τ} -> ¬ (Doneᴾ p) -> ¬ (Doneᴾ (ε₁ᴾ (yes l⊑A) p))
        ε¬done {⟨ Γ , t , [] ⟩} ¬done₁ (Done isVal) = εᵀ¬Val (¬Done⇒¬Val ¬done₁) isVal
        ε¬done {⟨ Γ , t , x ∷ S ⟩} ¬done₁ ()
        ε¬done {⟨ Γ , t , ∙ ⟩} ¬done₁ ()
        ε¬done {∙} ¬done₁ ()

        -- Lengthy boring proof, I will probably need the graph of the function εᴾ
        postulate ε¬redex : ∀ {p : Program l ls τ} -> ¬ (Redexᴾ p) -> ¬ (Redexᴾ (SE.ε₁ᴾ (yes l⊑A) p))


εᴳ-sim : ∀ {l n ls} {g₁ g₂ : Global ls} -> l ⊑ A -> (l P., n) ⊢ g₁ ↪ g₂ -> (l P., n) ⊢ (εᴳ g₁) ↪ (εᴳ g₂)
εᴳ-sim l⊑A (CS.step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ)
  = step-∅ (memberᴾ l⊑A l∈P) (memberᵀ l⊑A t∈T) (εᵀ¬Fork ¬fork) (εᴾ-simᴸ l⊑A step) (εˢ-simᴸ l⊑A sch) (updateᵀ l⊑A uᵀ) (updateᴾ l⊑A uᴾ)
εᴳ-sim l⊑A (CS.fork l∈P t∈T step uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ)
  = fork (memberᴾ l⊑A l∈P) (memberᵀ l⊑A t∈T) (εᴾ-simᴸ l⊑A step) (updateᵀ l⊑A uᵀ) (updateᴾ l⊑A u₁ᴾ) {!memberᴾ!} {!εˢ-simᴸ l⊑A sch!} {!!}
εᴳ-sim l⊑A (CS.skip l∈P t∈T stuck sch) = skip (memberᴾ l⊑A l∈P) (memberᵀ l⊑A t∈T) (stuck-ε l⊑A stuck) (εˢ-simᴸ l⊑A sch)
εᴳ-sim l⊑A (CS.done l∈P t∈T don sch) = done (memberᴾ l⊑A l∈P) (memberᵀ l⊑A t∈T) (done-ε l⊑A don) (εˢ-simᴸ l⊑A sch)
εᴳ-sim l⊑A (CS.hole l∈P t∈T sch) = hole (memberᴾ l⊑A l∈P) {!!} (εˢ-simᴸ l⊑A sch)
