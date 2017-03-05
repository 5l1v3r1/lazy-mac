import Lattice as L

module Sequential.Security (𝓛 : L.Lattice) (A : L.Label 𝓛) where

open import Sequential.Security.Erasure 𝓛 A
open import Sequential.Security.Graph 𝓛 A
open import Sequential.Security.Simulation 𝓛 A
open import Sequential.Security.Lemmas 𝓛 A
open import Sequential.Security.LowEq 𝓛 A

--------------------------------------------------------------------------------
-- Lemmas used in the proofs of the concurrent calculus.

open import Types 𝓛
open import Sequential.Calculus 𝓛
open import Relation.Nullary
open import Sequential.Valid 𝓛
open import Sequential.Semantics 𝓛
open import Data.Product

done-ε : ∀ {l τ} {Ts : TS∙ l τ} -> (l⊑A : l ⊑ A) -> IsDoneTS Ts -> IsDoneTS (εᵀˢ (yes l⊑A) Ts)
done-ε l⊑A (isDoneTS isVal) = isDoneTS (εᵀ-Val isVal)

ε¬done : ∀ {l τ} {Ts : TS∙ l τ} -> (l⊑A : l ⊑ A) -> ¬ (IsDoneTS Ts) -> ¬ (IsDoneTS (εᵀˢ (yes l⊑A) Ts))
ε¬done l⊑A ¬done = contrapositive (doneᴱ (lift-εᵀˢ (yes l⊑A) _)) ¬done

ε¬redex : ∀ {l ls τ} {p : Program l ls τ} {{pᵛ : validᴾ p}} (l⊑A : l ⊑ A) -> ¬ (Redexᴾ p) -> ¬ (Redexᴾ (ε₁ᴾ (yes l⊑A) p))
ε¬redex {l} {ls} {τ} {p = p} l⊑A ¬redex redex = simᴾ (lift-εᴾ (yes l⊑A) p) ¬redex redex

stuck-ε : ∀ {l ls τ} {p : Program l ls τ} {{pⱽ : validᴾ p}} -> (l⊑A : l ⊑ A) -> Stuckᴾ p -> Stuckᴾ (ε₁ᴾ (yes l⊑A) p)
stuck-ε {l} {_} {τ} {{pⱽ}}  l⊑A (¬done , ¬redex , ¬fork) = (ε¬done l⊑A ¬done) , ε¬redex l⊑A ¬redex , εᵀˢ¬IsForkTS l⊑A ¬fork
