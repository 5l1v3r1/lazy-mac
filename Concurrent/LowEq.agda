import Lattice as L
import Scheduler as S
open import Scheduler.Security

module Concurrent.LowEq {𝓛 : L.Lattice} {𝓢 : S.Scheduler 𝓛} (A : L.Label 𝓛) (𝓝 : NIˢ 𝓛 A 𝓢) where

open import Relation.Nullary
open import Types 𝓛

open import Sequential.Semantics 𝓛

open import Sequential.Erasure 𝓛 A as SE hiding (εᵀ ; εᴾ ; εˢ)
open import Sequential.LowEq 𝓛 A using (_≅ᴴ_ ; ⌞_⌟ᴴ ; _≈ᴴ_ ; ⌜_⌝ᴴ)
open import Sequential.PINI 𝓛 A using (stepᴸ ; stepᴴ-Γ)

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

open import Concurrent.Erasure A 𝓝

--------------------------------------------------------------------------------

open Scheduler.Security.NIˢ 𝓛 A 𝓝 renaming (State to Stateˢ)
open import Relation.Binary.PropositionalEquality
open import Data.Empty


_≅ᴳ_ : ∀ {ls} (g₁ g₂ : Global ls) -> Set
g₁ ≅ᴳ g₂ = εᴳ g₁ ≡ εᴳ g₂

lift-εᴳ : ∀ {ls} {Σ₁ Σ₂ : Stateˢ} {Γ₁ Γ₂ : Heaps ls} {P₁ P₂ : Pools ls} -> Σ₁ ≡ Σ₂ -> Γ₁ ≡ Γ₂ -> P₁ ≡ P₂ ->
          _≡_ {_} {Global ls} ⟨ Σ₁ , Γ₁ , P₁ ⟩ ⟨ Σ₂ , Γ₂ , P₂ ⟩
lift-εᴳ eq₁ eq₂ eq₃ rewrite eq₁ | eq₂ | eq₃ = refl

--------------------------------------------------------------------------------

-- Structural low-equivalence for Thread pool
data _≈ᵀ_ {l : Label} : Pool l -> Pool l -> Set where

-- Strucutral low-equivalence for Pools (point-wise)
data _≈ᴾ_ : ∀ {ls} -> Pools ls -> Pools ls -> Set where
  [] : [] ≈ᴾ []
  _◅_ : ∀ {l ls} {T₁ T₂ : Pool l} {P₁ P₂ : Pools ls} {u : Unique l ls} -> T₁ ≈ᵀ T₂ -> P₁ ≈ᴾ P₂ -> (T₁ ◅ P₁) ≈ᴾ (T₂ ◅ P₂)

_≅ᴾ_ : ∀ {ls} (P₁ P₂ : Pools ls) -> Set
P₁ ≅ᴾ P₂ =  εᴾ P₁ ≡ εᴾ P₂

-- structural low-equivalence for global configuration
record _≈ᴳ_ {ls} (g₁ g₂ : Global ls) : Set where
  constructor ⟨_,_,_⟩
  field
      Σ₁≈Σ₂ : Σ g₁ ≈ˢ Σ g₂
      P₁≈P₂ : P g₁ ≈ᴾ P g₂
      Γ₁≈Γ₂ : Γ g₁ ≈ᴴ Γ g₂

open _≈ᴳ_ public

⌜_⌝ᴾ : ∀ {ls} {P₁ P₂ : Pools ls} -> P₁ ≅ᴾ P₂ -> P₁ ≈ᴾ P₂
⌜ eq ⌝ᴾ = {!!}

⌞_⌟ᴾ : ∀ {ls} {P₁ P₂ : Pools ls} -> P₁ ≈ᴾ P₂ -> P₁ ≅ᴾ P₂
⌞ eq ⌟ᴾ = {!!}


⌜_⌝ᴳ : ∀ {ls} {g₁ g₂ : Global ls} -> g₁ ≅ᴳ g₂ -> g₁ ≈ᴳ g₂
⌜ x ⌝ᴳ = ⟨ (⌜ auxˢ x ⌝) ,  ⌜ auxᴾ x ⌝ᴾ ,  ⌜ ⌞ auxᴴ x ⌟ᴴ ⌝ᴴ ⟩
  where auxˢ : ∀ {ls} {Σ₁ Σ₂ : Stateˢ} {Γ₁ Γ₂ : Heaps ls} {P₁ P₂ : Pools ls} ->
                 _≡_ {_} {Global ls} ⟨ Σ₁ , Γ₁ , P₁ ⟩ ⟨ Σ₂ , Γ₂ , P₂ ⟩ -> Σ₁ ≡ Σ₂
        auxˢ refl = refl

        auxᴾ : ∀ {ls} {Σ₁ Σ₂ : Stateˢ} {Γ₁ Γ₂ : Heaps ls} {P₁ P₂ : Pools ls} ->
                 _≡_ {_} {Global ls} ⟨ Σ₁ , Γ₁ , P₁ ⟩ ⟨ Σ₂ , Γ₂ , P₂ ⟩ -> P₁ ≡ P₂
        auxᴾ refl = refl

        auxᴴ : ∀ {ls} {Σ₁ Σ₂ : Stateˢ} {Γ₁ Γ₂ : Heaps ls} {P₁ P₂ : Pools ls} ->
                 _≡_ {_} {Global ls} ⟨ Σ₁ , Γ₁ , P₁ ⟩ ⟨ Σ₂ , Γ₂ , P₂ ⟩ -> Γ₁ ≡ Γ₂
        auxᴴ refl = refl


⌞_⌟ᴳ : ∀ {ls} {g₁ g₂ : Global ls} -> g₁ ≈ᴳ g₂ -> g₁ ≅ᴳ g₂
⌞ ⟨ Σ₁≈Σ₂ , P₁≈P₂ , Γ₁≈Γ₂ ⟩ ⌟ᴳ = {!!} -- ⌞ lift-εᴳ (⌞ Σ₁≈Σ₂ ⌟) {!⌞_⌟ᴴ!} {!⌞_⌟ᴾ!}  ⌟ᴳ -- (εᴾ-refl ⌞ P₁≈P₂ ⌟ᴾ)

refl-≈ᴳ : ∀ {ls} {g : Global ls} -> g ≈ᴳ g
refl-≈ᴳ = ⌜ refl  ⌝ᴳ

sym-≈ᴳ : ∀ {ls} {g₁ g₂ : Global ls} -> g₁ ≈ᴳ g₂ -> g₂ ≈ᴳ g₁
sym-≈ᴳ x = ⌜ sym ⌞ x ⌟ᴳ ⌝ᴳ

trans-≈ᴳ : ∀ {ls} {g₁ g₂ g₃ : Global ls} -> g₁ ≈ᴳ g₂ -> g₂ ≈ᴳ g₃ -> g₁ ≈ᴳ g₃
trans-≈ᴳ x y = ⌜ trans ⌞ x ⌟ᴳ ⌞ y ⌟ᴳ ⌝ᴳ
