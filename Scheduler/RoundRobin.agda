import Lattice as L

module Scheduler.RoundRobin (𝓛 : L.Lattice) where

open import Scheduler.RoundRobin.Base 𝓛 public
open import Scheduler.RoundRobin.Security 𝓛 public
