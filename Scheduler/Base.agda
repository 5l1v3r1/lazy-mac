import Lattice as L

module Scheduler.Base (𝓛 : L.Lattice) where

open L.Lattice 𝓛

open import Data.Nat

data Event (l : Label) : Set where
  Skip : Event l
  Step : Event l
  Done : Event l
  Fork : (h : Label) (n : ℕ) -> l ⊑ h -> Event l
  ∙ : Event l

open Event public

data Message : Label -> Set where
   _,_,_ : (l : Label) (n : ℕ) (e : Event l) -> Message l

record Scheduler : Set₁ where
  constructor Sch
  field
    State : Set
    _⟶_↑_ : ∀ {l} -> State -> State -> Message l -> Set
