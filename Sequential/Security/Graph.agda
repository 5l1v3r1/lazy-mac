import Lattice as L

module Sequential.Security.Graph (𝓛 : L.Lattice) (A : L.Label 𝓛) where

open import Sequential.Security.Graph.Base 𝓛 A public
open import Sequential.Security.Graph.Lemmas 𝓛 A

open import Types 𝓛
open import Sequential.Calculus 𝓛
open import Sequential.Semantics 𝓛
open import Sequential.Valid 𝓛
open import Sequential.Security.Simulation 𝓛 A

open import Data.Product as P
open import Relation.Nullary

redex⁻ᴱ : ∀ {l ls τ} {p p' : Program l ls τ} {{pⱽ : validᴾ p}} {l⊑A : l ⊑ A}  -> Eraseᴾ (yes l⊑A) p p' -> Redexᴾ p' -> Redexᴾ p
redex⁻ᴱ {{pⱽ}} {l⊑A} e (Step step) = sim⟼ l⊑A pⱽ e step

redexᴱ : ∀ {l ls τ} {p p' : Program l ls τ} {l⊑A : l ⊑ A} -> Eraseᴾ (yes l⊑A) p p' -> Redexᴾ p -> Redexᴾ p'
redexᴱ {l⊑A = l⊑A} e (Step step) rewrite unlift-εᴾ e = Step (ε₁ᴾ-sim (yes l⊑A) step)

¬redexᴱ : ∀ {l ls τ} {p p' : Program l ls τ} {l⊑A : l ⊑ A} {{pⱽ : validᴾ p}} -> Eraseᴾ (yes l⊑A) p p' -> ¬ (Redexᴾ p) -> ¬ (Redexᴾ p')
¬redexᴱ {{pⱽ}} e = contrapositive (redex⁻ᴱ e)

¬redex⁻ᴱ : ∀ {l ls τ} {p p' : Program l ls τ} {l⊑A : l ⊑ A} -> Eraseᴾ (yes l⊑A) p p' -> ¬ (Redexᴾ p') -> ¬ (Redexᴾ p)
¬redex⁻ᴱ e = contrapositive (redexᴱ e)

open Eraseᴾ public

stuckᴱ : ∀ {l ls τ} {p p' : Program l ls τ} {l⊑A : l ⊑ A} {{pⱽ : validᴾ p}} -> Eraseᴾ (yes l⊑A) p p' -> Stuckᴾ p -> Stuckᴾ p'
stuckᴱ e (¬done , ¬redex , ¬fork) = ¬doneᴱ (eᵀˢ e) ¬done , ¬redexᴱ e ¬redex , ¬forkTSᴱ (eᵀˢ e) ¬fork
