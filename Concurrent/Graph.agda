import Lattice as L
import Scheduler as S
open import Scheduler.Security

module Concurrent.Graph {𝓛 : L.Lattice} {𝓢 : S.Scheduler 𝓛} (A : L.Label 𝓛) (𝓝 : NIˢ 𝓛 A 𝓢) where

import Types as T
open T 𝓛

open import Sequential.Calculus 𝓛
import Sequential.Security.Graph 𝓛 A as G

import Concurrent.Calculus as C
open C 𝓛 𝓢
open import Concurrent.Erasure A 𝓝

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

data EraseMapᵀ {l} (l⊑A : l ⊑ A) : Pool l -> Pool l -> Set where
  [] : EraseMapᵀ l⊑A [] []
  _◅_ : ∀ {T₁ T₂ P₁ P₂} -> G.Eraseᵀˢ (yes l⊑A) T₁ T₂ -> EraseMapᵀ l⊑A P₁ P₂ -> EraseMapᵀ l⊑A (T₁ ◅ P₁) (T₂ ◅ P₂)
  ∙ : EraseMapᵀ l⊑A ∙ ∙

lift-map-εᵀ : ∀ {l} (l⊑A : l ⊑ A) (P : Pool l) -> EraseMapᵀ l⊑A P (map-εᵀ l⊑A P)
lift-map-εᵀ l⊑A C.[] = []
lift-map-εᵀ l⊑A (t C.◅ P) = (G.lift-εᵀˢ (yes l⊑A) t) ◅ (lift-map-εᵀ l⊑A P)
lift-map-εᵀ l⊑A C.∙ = ∙


unlift-map-εᵀ : ∀ {l} {P P' : Pool l } {l⊑A : l ⊑ A} -> EraseMapᵀ l⊑A P P' -> P' ≡ map-εᵀ l⊑A P
unlift-map-εᵀ [] = refl
unlift-map-εᵀ (e₁ ◅ e₂) with G.unlift-εᵀˢ e₁ | unlift-map-εᵀ e₂
... | eq₁ | eq₂ rewrite eq₁ | eq₂ = refl
unlift-map-εᵀ ∙ = refl

ext-ε-mapᵀ : ∀ {l} {P P' : Pool l } {l⊑A l⊑A' : l ⊑ A} -> EraseMapᵀ l⊑A P P' -> EraseMapᵀ l⊑A' P P'
ext-ε-mapᵀ [] = []
ext-ε-mapᵀ (x ◅ x₁) = G.ext-εᵀˢ x ◅ (ext-ε-mapᵀ x₁)
ext-ε-mapᵀ ∙ = ∙

--------------------------------------------------------------------------------

data Eraseᴾ {l : Label} : Dec (l ⊑ A) -> Pool l -> Pool l -> Set where
  Mapᵀ : ∀ {P₁ P₂ : Pool l} {l⊑A : l ⊑ A} -> EraseMapᵀ l⊑A P₁ P₂ -> Eraseᴾ (yes l⊑A) P₁ P₂
  ∙ : ∀ {P} {l⋤A : l ⋤ A} -> Eraseᴾ (no l⋤A) P ∙

lift-εᴾ : ∀ {l} (x : Dec (l ⊑ A)) (P : Pool l) -> Eraseᴾ x P (εᴾ x P)
lift-εᴾ (yes l⊑A) P = Mapᵀ (lift-map-εᵀ l⊑A P)
lift-εᴾ (no ¬p) P = ∙

unlift-εᴾ : ∀ {l} {x : Dec (l ⊑ A)} {P P' : Pool l} -> Eraseᴾ x P P' -> P' ≡ εᴾ x P
unlift-εᴾ (Mapᵀ x) = unlift-map-εᵀ x
unlift-εᴾ ∙ = refl

open import Data.Empty

ext-εᴾ : ∀ {l} {x : Dec (l ⊑ A)} {T T' : Pool l} -> Eraseᴾ x T T' -> (y : Dec (l ⊑ A)) -> Eraseᴾ y T T'
ext-εᴾ (Mapᵀ x) (yes p) = Mapᵀ (ext-ε-mapᵀ x)
ext-εᴾ (Mapᵀ {l⊑A = l⊑A} x) (no ¬p) = ⊥-elim (¬p l⊑A)
ext-εᴾ {x = no l⋤A} ∙ (yes p) = ⊥-elim (l⋤A p)
ext-εᴾ ∙ (no ¬p) = ∙

--------------------------------------------------------------------------------

data EraseMapᴾ : ∀ {ls} -> Pools ls -> Pools ls -> Set where
  [] : EraseMapᴾ [] []
  _◅_ : ∀ {l ls} {{u : Unique l ls}} {Ps₁ Ps₂ : Pools ls} {P₁ P₂ : Pool l} ->
        Eraseᴾ (l ⊑? A) P₁ P₂ -> EraseMapᴾ Ps₁ Ps₂ -> EraseMapᴾ (P₁ ◅ Ps₁ ) (P₂ ◅ Ps₂)

lift-map-εᴾ : ∀ {ls} -> (Ps : Pools ls) -> EraseMapᴾ Ps (map-εᴾ Ps)
lift-map-εᴾ C.[] = []
lift-map-εᴾ (T C.◅ Ps) = (lift-εᴾ (_ ⊑? A) T) ◅ lift-map-εᴾ Ps

unlift-map-εᴾ : ∀ {ls} {Ps Ps' : Pools ls} -> EraseMapᴾ Ps Ps' -> Ps' ≡ map-εᴾ Ps
unlift-map-εᴾ [] = refl
unlift-map-εᴾ (e₁ ◅ e₂) rewrite unlift-εᴾ {x = _ ⊑? A} e₁ | unlift-map-εᴾ e₂ = refl

--------------------------------------------------------------------------------
