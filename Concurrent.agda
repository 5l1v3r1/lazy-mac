open import Lattice
open import Scheduler

module Concurrent (𝓛 : Lattice) (𝓢 : Scheduler 𝓛)  where

open import Concurrent.Calculus 𝓛 𝓢 public
open import Concurrent.Semantics 𝓛 𝓢 public
