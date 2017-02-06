import Lattice as L
import Scheduler as S
open import Scheduler.Security

module Concurrent.Erasure {𝓛 : L.Lattice} {𝓢 : S.Scheduler 𝓛} (A : L.Label 𝓛) (𝓝 : NIˢ 𝓛 A 𝓢) where

open import Relation.Nullary
open import Types 𝓛
open import Sequential.Erasure 𝓛 A as SE hiding (εᵀ ; εᴾ ; εˢ)


-- Temporarily side-step bug #2245
import Concurrent.Calculus as C
open C 𝓛 𝓢
-- open import Concurrent.Calculus 𝓛 𝓢
open import Concurrent.Semantics 𝓛 𝓢 public

open Scheduler.Security.NIˢ 𝓛 A 𝓝

εᵗ : ∀ {l} ->  Thread l -> Thread l
εᵗ C.⟨ t , S ⟩ = ⟨ SE.εᵀ t , SE.εˢ S ⟩
εᵗ C.∙ = ∙

εᵀ : ∀ {l} -> Dec (l ⊑ A) -> Pool l -> Pool l
εᵀ (yes p) C.[] = []
εᵀ (yes p) (t C.◅ T) = εᵗ t ◅ (εᵀ (yes p) T)
εᵀ (yes p) C.∙ = ∙
εᵀ (no ¬p) T = ∙

-- Pointwise erasure function for pools
εᴾ : ∀ {ls} -> Pools ls -> Pools ls
εᴾ C.[] = []
εᴾ (T C.◅ P) = (εᵀ (_ ⊑? A) T) ◅ (εᴾ P)

εᴳ : ∀ {ls} -> Global ls -> Global ls
εᴳ C.⟨ Σ , Γ , P ⟩ = C.⟨ εˢ Σ , εᴴ Γ , εᴾ P ⟩

open import Relation.Binary.PropositionalEquality hiding (subst ; [_])
