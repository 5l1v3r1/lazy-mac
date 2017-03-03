import Lattice as L
import Scheduler as S₁

module Concurrent.Valid (𝓛 : L.Lattice) (𝓢 : S₁.Scheduler 𝓛) where

import Types as T
open T 𝓛


open S₁.Scheduler 𝓛 𝓢 renaming (State to Stateˢ)
open import Scheduler.Base 𝓛 renaming (⟪_,_,_⟫ to mkᴹ)

import Sequential.Calculus as S
open S 𝓛

import Sequential.Valid as V hiding (validᴾ ; validˢ )
open V 𝓛

import  Concurrent.Calculus as C renaming (⟨_,_,_,_⟩ to mkᴳ)
open C 𝓛 𝓢

import Concurrent.Semantics
module CS = Concurrent.Semantics 𝓛 𝓢
open CS

open import Data.Product as P
open import Data.Empty

validᴾ : ∀ {l ls} -> Memories ls -> Pool l -> Set
validᴾ Ms C.[] = ⊤
validᴾ Ms (t C.◅ P) = validTS∙ Ms t × validᴾ Ms P
validᴾ Ms C.∙ = ⊥

map-validᴾ : ∀ {ls ls'} -> Memories ls -> Pools ls' -> Set
map-validᴾ Ms C.[] = ⊤
map-validᴾ Ms (T C.◅ Ps) = validᴾ Ms T × map-validᴾ Ms Ps

data Validᵀ {l} : (n : ℕ) (P : Pool l) -> Set where
  -- TODO fill in ...

validˢ : ∀ {ls} -> Pools ls -> Stateˢ -> Set
validˢ {ls} Ps Σ = ∀ {Σ' l n e} -> Σ ⟶ Σ' ↑ (mkᴹ l n e) -> P.Σ (l ∈ ls) (λ l∈ls -> Validᵀ n (lookupᴾ l∈ls Ps))

validᴳ : ∀ {ls} -> Global ls -> Set
validᴳ (mkᴳ Σ Ms Γ Ps) = validˢ Ps Σ × map-validᴹ Ms × map-validᴴ Ms Γ × map-validᴾ Ms Ps
