import Lattice as L

module Sequential.Security (𝓛 : L.Lattice) (A : L.Label 𝓛) where

open import Sequential.Security.Erasure 𝓛 A
open import Sequential.Security.Graph 𝓛 A
open import Sequential.Security.Simulation 𝓛 A
open import Sequential.Security.LowEq 𝓛 A public
open import Sequential.Security.PINI 𝓛 A public

--------------------------------------------------------------------------------
-- Lemmas used in the proofs of the concurrent calculus.

open import Types 𝓛
open import Sequential.Calculus 𝓛
open import Relation.Nullary
open import Sequential.Valid 𝓛
open import Sequential.Semantics 𝓛
open import Data.Product

done-ε : ∀ {l τ} {Ts : TS∙ l τ} -> (l⊑A : l ⊑ A) -> IsDoneTS Ts -> IsDoneTS (εᵀˢ (yes l⊑A) Ts)
done-ε l⊑A = doneᴱ (lift-εᵀˢ (yes l⊑A) _)

¬done-ε : ∀ {l τ} {Ts : TS∙ l τ} -> (l⊑A : l ⊑ A) -> ¬ (IsDoneTS Ts) -> ¬ (IsDoneTS (εᵀˢ (yes l⊑A) Ts))
¬done-ε l⊑A = ¬doneᴱ (lift-εᵀˢ (yes l⊑A) _)

¬redex-ε : ∀ {l ls τ} {p : Program l ls τ} {{pᵛ : validᴾ p}} (l⊑A : l ⊑ A) -> ¬ (Redexᴾ p) -> ¬ (Redexᴾ (ε₁ᴾ (yes l⊑A) p))
¬redex-ε l⊑A = ¬redexᴱ (lift-εᴾ (yes l⊑A) _)

stuck-ε : ∀ {l ls τ} {p : Program l ls τ} {{pⱽ : validᴾ p}} -> (l⊑A : l ⊑ A) -> Stuckᴾ p -> Stuckᴾ (ε₁ᴾ (yes l⊑A) p)
stuck-ε l⊑A = stuckᴱ (lift-εᴾ (yes l⊑A) _)
