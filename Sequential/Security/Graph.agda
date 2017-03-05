import Lattice as L

module Sequential.Security.Graph (𝓛 : L.Lattice) (A : L.Label 𝓛) where

open import Sequential.Security.Graph.Base 𝓛 A public
open import Sequential.Security.Graph.Lemmas 𝓛 A using (redex⁻ᴱ ; redexᴱ ; ¬redexᴱ ; ¬redex⁻ᴱ) public
