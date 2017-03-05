-- TODO remove

import Lattice as L₁

module Sequential.Security.Lemmas2 (𝓛 : L₁.Lattice) (A : L₁.Label 𝓛) where

import Types as T
open T 𝓛

open import Sequential.Security.Erasure 𝓛 A as SE hiding (updateᴹ)
import Sequential.Security.Graph as G
open G 𝓛 A

--------------------------------------------------------------------------------
-- Temporarily side-step bug #2245

import Sequential.Calculus as SC
open SC 𝓛

--------------------------------------------------------------------------------

import Sequential.Semantics as SS
open SS 𝓛

import Sequential.Security.LowEq as L renaming (⟨_,_,_⟩ to is≈ᴾ)
open L 𝓛 A



open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Relation.Nullary
open import Data.Product
open import Data.Maybe

import Sequential.Calculus renaming (⟨_,_,_⟩ to mkᴾ ; ⟨_,_⟩ to mkᵀ)

--------------------------------------------------------------------------------
