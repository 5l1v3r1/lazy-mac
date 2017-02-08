import Lattice as L

module Scheduler.RoundRobin.Base (𝓛 : L.Lattice) where

open L.Lattice 𝓛

open import Scheduler.Base 𝓛 renaming (_,_,_ to ⟪_,_,_⟫)

open import Data.Product
open import Data.List
open import Data.Nat

State : Set
State = List (Label × ℕ)

data _⟶_↑_ : ∀ {l} -> State -> State -> Message l -> Set where
  step : ∀ {s} -> (l : Label) (n : ℕ) -> ((l , n) ∷ s) ⟶ s ++ [ (l , n) ] ↑ ⟪ l , n , Step ⟫
  fork : ∀ {s h m} -> (l : Label) (n : ℕ) (p : l ⊑ h) -> ((l , n) ∷ s) ⟶ s ++ ((h , m) ∷ (l , n) ∷ []) ↑ ⟪ l , n , Fork h m p ⟫
  done : ∀ {s} -> (l : Label) (n : ℕ) -> ((l , n) ∷ s) ⟶ s ↑ ⟪ l , n , Done ⟫
  skip : ∀ {s} -> (l : Label) (n : ℕ) -> ((l , n) ∷ s) ⟶ s ++ [ (l , n) ] ↑ ⟪ l , n , Skip ⟫

open import Relation.Binary.PropositionalEquality hiding ([_])

-- Determinism
determinism : ∀ {s₁ s₂ s₃ l n e} ->
                                   s₁ ⟶ s₂ ↑ ⟪ l , n , e ⟫ ->
                                   s₁ ⟶ s₃ ↑ ⟪ l , n , e ⟫ ->
                                   s₂ ≡ s₃
determinism (step l n) (step .l .n) = refl
determinism (fork l n p) (fork .l .n .p) = refl
determinism (done l n) (done .l .n) = refl
determinism (skip l n) (skip .l .n) = refl

RR : Scheduler
RR = record { State = State ; _⟶_↑_ = _⟶_↑_ ; determinismˢ = determinism }
