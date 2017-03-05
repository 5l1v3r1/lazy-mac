import Lattice as L
import Scheduler as S
open import Scheduler.Security

module Concurrent.Erasure {𝓛 : L.Lattice} {𝓢 : S.Scheduler 𝓛} (A : L.Label 𝓛) (𝓝 : NIˢ 𝓛 A 𝓢) where

open import Relation.Nullary
open import Types 𝓛

import Sequential.Semantics as S₁
open S₁ 𝓛

open import Sequential.Security.Erasure 𝓛 A using (εᵀˢ ; εᵀˢ-ext-≡ ; map-εᴹ ; map-εᴴ)

--------------------------------------------------------------------------------
-- Temporarily side-step bug #2245
import Concurrent.Calculus as C
open C 𝓛 𝓢
-- open import Concurrent.Calculus 𝓛 𝓢

import Concurrent.Semantics as CS
open CS 𝓛 𝓢
-- open import Concurrent.Semantics 𝓛 𝓢 public

import Sequential.Calculus as SC
open SC 𝓛

--------------------------------------------------------------------------------

open Scheduler.Security.NIˢ 𝓛 A 𝓝 renaming (State to Stateˢ)

map-εᵀ : ∀ {l} -> l ⊑ A -> Pool l -> Pool l
map-εᵀ l⊑A  C.[] = []
map-εᵀ l⊑A (t C.◅ P) = εᵀˢ (yes l⊑A) t ◅ map-εᵀ l⊑A P
map-εᵀ l⊑A C.∙ = ∙

εᴾ : ∀ {l} -> Dec (l ⊑ A) -> Pool l -> Pool l
εᴾ (yes l⊑A) P = map-εᵀ l⊑A P
εᴾ (no _) P = ∙

open import Relation.Binary.PropositionalEquality
open import Data.Empty

εᴾ-ext-≡ : ∀ {l} -> (x y : Dec (l ⊑ A)) (T : Pool l) -> εᴾ x T ≡ εᴾ y T
εᴾ-ext-≡ (yes p) (yes p₁) C.[] = refl
εᴾ-ext-≡ (yes p) (yes p₁) (t C.◅ T) with εᵀˢ-ext-≡ (yes p) (yes p₁) t | εᴾ-ext-≡ (yes p) (yes p₁) T
... | eq₁ | eq₂ rewrite eq₁ | eq₂ = refl
εᴾ-ext-≡ (yes p) (yes p₁) C.∙ = refl
εᴾ-ext-≡ (yes p) (no ¬p) T = ⊥-elim (¬p p)
εᴾ-ext-≡ (no ¬p) (yes p) T = ⊥-elim (¬p p)
εᴾ-ext-≡ (no ¬p) (no ¬p₁) T = refl

-- Pointwise erasure function for pools
map-εᴾ : ∀ {ls} -> Pools ls -> Pools ls
map-εᴾ C.[] = []
map-εᴾ (T C.◅ P) = (εᴾ (_ ⊑? A) T) ◅ (map-εᴾ P)

εᴳ : ∀ {ls} -> Global ls -> Global ls
εᴳ C.⟨ Σ , Ms , Γ , P ⟩ = C.⟨ εˢ Σ , map-εᴹ Ms , map-εᴴ Γ , map-εᴾ P ⟩

open import Data.Product as P

memberᴾ : ∀ {l ls} {T : Pool l} {P : Pools ls} -> (l⊑A : l ⊑ A) -> l ↦ T ∈ᴾ P -> l ↦ (εᴾ (yes l⊑A) T) ∈ᴾ (map-εᴾ P)
memberᴾ {l} l⊑A C.here with l ⊑? A
memberᴾ {T = T} l⊑A C.here | yes p rewrite εᴾ-ext-≡ (yes l⊑A) (yes p) T = here
memberᴾ l⊑A C.here | no ¬p = ⊥-elim (¬p l⊑A)
memberᴾ l⊑A (C.there x) = there (memberᴾ l⊑A x)

memberᵀ : ∀ {l n} {T : Pool l} {Ts : Thread _} -> (l⊑A : l ⊑ A)
          -> n ↦ Ts ∈ᵀ T -> n ↦ (εᵀˢ (yes l⊑A) Ts) ∈ᵀ (εᴾ (yes l⊑A) T)
memberᵀ l⊑A C.here = C.here
memberᵀ l⊑A (C.there x) = C.there (memberᵀ l⊑A x)

updateᵀᴸ : ∀ {l n} {Ts : Thread _}  {T₁ T₂ : Pool l} -> (l⊑A : l ⊑ A) -> T₂ ≔ T₁ [ n ↦ Ts ]ᵀ ->
          (εᴾ (yes l⊑A) T₂) ≔ (εᴾ (yes l⊑A) T₁) [ n ↦ εᵀˢ (yes l⊑A) Ts ]ᵀ
updateᵀᴸ l⊑A C.here = C.here
updateᵀᴸ l⊑A (C.there x) = C.there (updateᵀᴸ l⊑A x)

updateᴾᴸ : ∀ {l ls} {T : Pool l} {P₁ P₂ : Pools ls} -> (l⊑A : l ⊑ A) -> P₂ ≔ P₁ [ l ↦ T ]ᴾ -> (map-εᴾ P₂) ≔ (map-εᴾ P₁) [ l ↦ (εᴾ (yes l⊑A) T) ]ᴾ
updateᴾᴸ {l} l⊑A C.here with l ⊑? A
updateᴾᴸ {T = T} l⊑A C.here | yes p rewrite εᴾ-ext-≡ (yes l⊑A) (yes p) T = here
updateᴾᴸ l⊑A C.here | no ¬p = ⊥-elim (¬p l⊑A)
updateᴾᴸ l⊑A (C.there x) = C.there (updateᴾᴸ l⊑A x)

--------------------------------------------------------------------------------

lengthᵀ-ε-≡ : ∀ {l} (l⊑A : l ⊑ A) (T : Pool l) -> lengthᵀ T ≡ lengthᵀ (εᴾ (yes l⊑A) T)
lengthᵀ-ε-≡ l⊑A C.[] = refl
lengthᵀ-ε-≡ l⊑A (t C.◅ T) rewrite lengthᵀ-ε-≡ l⊑A T = refl
lengthᵀ-ε-≡ l⊑A C.∙ = refl

εᴾ-▻-≡ : ∀ {l} (l⊑A : l ⊑ A) (T : Pool l) (t : Thread l) -> ((εᴾ (yes l⊑A) T) ▻ εᵀˢ (yes l⊑A) t) ≡ εᴾ (yes l⊑A) (T ▻ t)
εᴾ-▻-≡ l⊑A C.[] t = refl
εᴾ-▻-≡ l⊑A (t C.◅ T) t₁ with εᴾ-▻-≡ l⊑A T t₁
... | eq rewrite eq = refl
εᴾ-▻-≡ l⊑A C.∙ t = refl

updateᴾ-▻ : ∀ {l ls} {P₁ P₂ : Pools ls} (T : Pool l) (t : Thread l) -> (l⊑A : l ⊑ A) ->
                 P₁ ≔ P₂ [ l ↦ T ▻ t ]ᴾ ->
                 (map-εᴾ P₁) ≔ (map-εᴾ P₂) [ l ↦ (εᴾ (yes l⊑A) T) ▻ (εᵀˢ (yes l⊑A) t) ]ᴾ
updateᴾ-▻ {l} T t l⊑A x with εᴾ-▻-≡ l⊑A T t
... | eq rewrite eq = updateᴾᴸ l⊑A x

newᴾ∙ : ∀ {H ls} {P₁ P₂ : Pools ls} (T : Pool H) (t : Thread H) -> (H⋤A : H ⋤ A) -> P₂ ≔ P₁ [ H ↦ T ▻ t ]ᴾ -> map-εᴾ P₂ ≡ map-εᴾ P₁
newᴾ∙ {H} T t H⋤A C.here with H ⊑? A
newᴾ∙ T t H⋤A C.here | yes p = ⊥-elim (H⋤A p)
newᴾ∙ T t H⋤A C.here | no ¬p = refl
newᴾ∙ T t H⋤A (C.there x) rewrite newᴾ∙ T t H⋤A x = refl

updateᴾ∙ : ∀ {H ls} {P₁ P₂ : Pools ls} {T : Pool H} -> H ⋤ A -> P₂ ≔ P₁ [ H ↦ T ]ᴾ -> map-εᴾ P₁ ≡  map-εᴾ P₂
updateᴾ∙ {H} H⋤A C.here with H ⊑? A
updateᴾ∙ H⋤A C.here | yes p = ⊥-elim (H⋤A p)
updateᴾ∙ H⋤A C.here | no ¬p = refl
updateᴾ∙ H⋤A (C.there x) rewrite updateᴾ∙ H⋤A x = refl
