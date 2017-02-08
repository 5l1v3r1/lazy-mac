import Lattice as L
import Scheduler as S
open import Scheduler.Security

module Concurrent.LowEq {𝓛 : L.Lattice} {𝓢 : S.Scheduler 𝓛} (A : L.Label 𝓛) (𝓝 : NIˢ 𝓛 A 𝓢) where

open import Relation.Nullary
open import Types 𝓛

open import Sequential.Semantics 𝓛

open import Sequential.Erasure 𝓛 A as SE hiding (εᵀ ; εᴾ ; εˢ)
open import Sequential.LowEq 𝓛 A as LE using (_≅ᴴ_ ; ⌞_⌟ᴴ ; _≈ᴴ_ ; ⌜_⌝ᴴ)
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

open import Data.Product using (_×_)
import Data.Product as P


_≅ᴳ_ : ∀ {ls} (g₁ g₂ : Global ls) -> Set
g₁ ≅ᴳ g₂ = εᴳ g₁ ≡ εᴳ g₂

lift-εᴳ : ∀ {ls} {Σ₁ Σ₂ : Stateˢ} {Γ₁ Γ₂ : Heaps ls} {P₁ P₂ : Pools ls} -> Σ₁ ≡ Σ₂ -> Γ₁ ≡ Γ₂ -> P₁ ≡ P₂ ->
          _≡_ {_} {Global ls} ⟨ Σ₁ , Γ₁ , P₁ ⟩ ⟨ Σ₂ , Γ₂ , P₂ ⟩
lift-εᴳ eq₁ eq₂ eq₃ rewrite eq₁ | eq₂ | eq₃ = refl

--------------------------------------------------------------------------------

_≌ᵗ_ : ∀ {l} -> Thread l -> Thread l -> Set
t₁ ≌ᵗ t₂ = εᵗ t₁ ≡ εᵗ t₂

data _≈ᵗ_ {l : Label} : Thread l -> Thread l -> Set where
  ⟨_,_⟩ : ∀ {τ π} {t₁ t₂ : Term π τ} {S₁ S₂ : Stack l τ _} -> t₁ LE.≈ᵀ t₂ -> S₁ LE.≈ˢ S₂ -> ⟨ t₁ , S₁ ⟩ ≈ᵗ ⟨ t₂ , S₂ ⟩

⌞_⌟ᵗ : ∀ {l} {t₁ t₂ : Thread l} -> t₁ ≈ᵗ t₂ -> t₁ ≌ᵗ t₂
⌞ ⟨ eq₁ , eq₂ ⟩ ⌟ᵗ rewrite LE.⌞ eq₁ ⌟ᵀ | LE.⌞ eq₂ ⌟ˢ = refl

split₁ᵗ : ∀ {l τ₁ τ₂ π₁ π₂} {t₁ : Term π₁ τ₁} {t₂ : Term π₂ τ₂} {S₁ : Stack l _ _} {S₂ : Stack _ _ _ } ->
                _≡_ {_} {Thread l} ⟨ t₁ , S₁ ⟩ ⟨ t₂ , S₂ ⟩ -> τ₁ ≡ τ₂ × (π₁ ≡ π₂)
split₁ᵗ refl = refl P., refl

split₂ᵗ : ∀ {l τ π} {t₁ t₂ : Term π τ} {S₁ S₂ : Stack l _ _} ->
                _≡_ {_} {Thread l} ⟨ t₁ , S₁ ⟩ ⟨ t₂ , S₂ ⟩ -> (t₁ ≡ t₂) × (S₁ ≡ S₂)
split₂ᵗ refl = refl P., refl

⌜_⌝ᵗ : ∀ {l} {t₁ t₂ : Thread l} -> t₁ ≌ᵗ t₂ -> t₁ ≈ᵗ t₂
⌜_⌝ᵗ {t₁ = C.⟨ t , S ⟩} {C.⟨ t₁ , S₁ ⟩} eq with split₁ᵗ eq
... | eq₁ P., eq₂ rewrite eq₁ | eq₂ with split₂ᵗ eq
... | eq₃ P., eq₄ = ⟨ LE.⌜ eq₃ ⌝ᵀ , LE.⌜ eq₄ ⌝ˢ ⟩

--------------------------------------------------------------------------------

_≌ᵀ⟨_⟩_ : ∀ {l} -> Pool l -> Dec (l ⊑ A) ->  Pool l -> Set
T₁ ≌ᵀ⟨ x ⟩ T₂ = εᵀ x T₁ ≡ εᵀ x T₂

-- Structural low-equivalence for Thread pool
data _≈ᵀ⟨_⟩_ {l : Label} : Pool l -> Dec (l ⊑ A) -> Pool l -> Set where
  nil : ∀ (l⊑A : l ⊑ A) -> [] ≈ᵀ⟨ yes l⊑A ⟩ []
  cons :  {T₁ T₂ : Pool l} {t₁ t₂ : Thread l} (l⊑A : l ⊑ A) -> t₁ ≈ᵗ t₂ -> T₁ ≈ᵀ⟨ yes l⊑A ⟩ T₂ -> (t₁ ◅ T₁) ≈ᵀ⟨ yes l⊑A ⟩ (t₂ ◅ T₂)
  ∙ᴸ : ∀ {l⊑A : l ⊑ A} -> ∙ ≈ᵀ⟨ yes l⊑A ⟩ ∙
  ∙ : ∀ {T₁ T₂ : Pool l} {l⋤A : l ⋤ A} -> T₁ ≈ᵀ⟨ no l⋤A ⟩ T₂

-- ⌜_⌝ᵀ : ∀ {l} {T₁ T₂ : Pool l} -> T₁ ≌ᵀ⟨ l ⊑? A ⟩ T₂ -> T₁ ≈ᵀ⟨ l ⊑? A ⟩ T₂
-- ⌜_⌝ᵀ {l}  eq with l ⊑? A
-- ⌜_⌝ᵀ {l} {C.[]} {C.[]} eq | yes p = nil p
-- ⌜_⌝ᵀ {l} {C.[]} {t C.◅ T₂} () | yes p
-- ⌜_⌝ᵀ {l} {C.[]} {C.∙} () | yes p
-- ⌜_⌝ᵀ {l} {t C.◅ T₁} {C.[]} () | yes p
-- ⌜_⌝ᵀ {l} {t C.◅ T₁} {t₁ C.◅ T₂} eq | yes p = {!!}
--   -- rewrite εᵀ-ext-≡ (yes p) (l ⊑? A) T₁ | εᵀ-ext-≡ (yes p) (l ⊑? A) T₂ = cons p {!!} {!⌜ ? ⌝ᵀ!}
-- ⌜_⌝ᵀ {l} {t C.◅ T₁} {C.∙} () | yes p
-- ⌜_⌝ᵀ {l} {C.∙} {C.[]} () | yes p
-- ⌜_⌝ᵀ {l} {C.∙} {t C.◅ T₂} () | yes p
-- ⌜_⌝ᵀ {l} {C.∙} {C.∙} refl | yes p = ∙ᴸ
-- ⌜ eq ⌝ᵀ | no ¬p = ∙

open import Data.Product using (_×_)

splitᵀ : ∀ {l} {t₁ t₂ : Thread l} {T₁ T₂ : Pool l} -> _≡_ {_} {Pool l} (t₁ ◅ T₁) (t₂ ◅ T₂) -> t₁ ≡ t₂ × T₁ ≡ T₂
splitᵀ refl = refl P., refl

⌜_⌝ᵀ : ∀ {l} {x : Dec (l ⊑ A)} {T₁ T₂ : Pool l} -> T₁ ≌ᵀ⟨ x ⟩ T₂ -> T₁ ≈ᵀ⟨ x ⟩ T₂
⌜_⌝ᵀ {x = yes p} {C.[]} {C.[]} refl = nil p
⌜_⌝ᵀ {x = yes p} {C.[]} {t C.◅ T₂} ()
⌜_⌝ᵀ {x = yes p} {C.[]} {C.∙} ()
⌜_⌝ᵀ {x = yes p} {t C.◅ T₁} {C.[]} ()
⌜_⌝ᵀ {x = yes p} {t C.◅ T₁} {t₁ C.◅ T₂} eq with splitᵀ eq
... | eq₁ P., eq₂ = cons p ⌜ eq₁ ⌝ᵗ ⌜ eq₂ ⌝ᵀ
⌜_⌝ᵀ {x = yes p} {t C.◅ T₁} {C.∙} ()
⌜_⌝ᵀ {x = yes p} {C.∙} {C.[]} ()
⌜_⌝ᵀ {x = yes p} {C.∙} {t C.◅ T₂} ()
⌜_⌝ᵀ {x = yes p} {C.∙} {C.∙} refl = ∙ᴸ
⌜_⌝ᵀ {x = no ¬p} eq = ∙

⌞_⌟ᵀ : ∀ {l} {T₁ T₂ : Pool l} {x : Dec (l ⊑ A)}-> T₁ ≈ᵀ⟨ x ⟩ T₂ -> T₁ ≌ᵀ⟨ x ⟩ T₂
⌞ nil l⊑A ⌟ᵀ = refl
⌞ cons l⊑A x eq ⌟ᵀ = cong₂ _◅_ ⌞ x ⌟ᵗ ⌞ eq ⌟ᵀ
⌞ ∙ᴸ ⌟ᵀ = refl
⌞ ∙ ⌟ᵀ = refl

--------------------------------------------------------------------------------

-- Strucutral low-equivalence for Pools (point-wise)
data _≈ᴾ_ : ∀ {ls} -> Pools ls -> Pools ls -> Set where
  [] : [] ≈ᴾ []
  _◅_ : ∀ {l ls} {T₁ T₂ : Pool l} {P₁ P₂ : Pools ls} {u : Unique l ls} -> T₁ ≈ᵀ⟨ l ⊑? A ⟩ T₂ -> P₁ ≈ᴾ P₂ -> (T₁ ◅ P₁) ≈ᴾ (T₂ ◅ P₂)

_≅ᴾ_ : ∀ {ls} (P₁ P₂ : Pools ls) -> Set
P₁ ≅ᴾ P₂ =  εᴾ P₁ ≡ εᴾ P₂

splitᴾ : ∀ {l ls} {P₁ P₂ : Pools ls} {T₁ T₂ : Pool l} {u₁ u₂ : Unique l ls} ->
         _≡_ {_} {Pools (l ∷ ls)} (_◅_ {{u₁}} T₁ P₁ ) (_◅_ {{u₂}} T₂ P₂) -> (u₁ ≡ u₂) × (T₁ ≡ T₂ × P₁ ≡ P₂)
splitᴾ refl = refl P., refl P., refl


⌜_⌝ᴾ : ∀ {ls} {P₁ P₂ : Pools ls} -> P₁ ≅ᴾ P₂ -> P₁ ≈ᴾ P₂
⌜_⌝ᴾ {P₁ = C.[]} {C.[]} refl = []
⌜_⌝ᴾ {P₁ = T C.◅ P₁} {T₁ C.◅ P₂} eq with splitᴾ eq
⌜_⌝ᴾ {._} {T C.◅ P₁} {T₁ C.◅ P₂} eq | refl P., eq₂ P., eq₃ = ⌜ eq₂ ⌝ᵀ ◅ ⌜ eq₃ ⌝ᴾ

⌞_⌟ᴾ : ∀ {ls} {P₁ P₂ : Pools ls} -> P₁ ≈ᴾ P₂ -> P₁ ≅ᴾ P₂
⌞ [] ⌟ᴾ = refl
⌞ x ◅ eq ⌟ᴾ = cong₂ _◅_ ⌞ x ⌟ᵀ ⌞ eq ⌟ᴾ

--------------------------------------------------------------------------------

-- structural low-equivalence for global configuration
record _≈ᴳ_ {ls} (g₁ g₂ : Global ls) : Set where
  constructor ⟨_,_,_⟩
  field
      Σ₁≈Σ₂ : Σ g₁ ≈ˢ Σ g₂
      P₁≈P₂ : P g₁ ≈ᴾ P g₂
      Γ₁≈Γ₂ : Γ g₁ ≈ᴴ Γ g₂

open _≈ᴳ_ public

⌜_⌝ᴳ : ∀ {ls} {g₁ g₂ : Global ls} -> g₁ ≅ᴳ g₂ -> g₁ ≈ᴳ g₂
⌜ x ⌝ᴳ = ⟨ (⌜ auxˢ x ⌝) ,  ⌜ auxᴾ x ⌝ᴾ ,  ⌜ auxᴴ x ⌝ᴴ ⟩
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
⌞ ⟨ Σ₁≈Σ₂ , P₁≈P₂ , Γ₁≈Γ₂ ⟩ ⌟ᴳ = lift-εᴳ (⌞ Σ₁≈Σ₂ ⌟) ⌞ Γ₁≈Γ₂ ⌟ᴴ ⌞ P₁≈P₂ ⌟ᴾ

refl-≈ᴳ : ∀ {ls} {g : Global ls} -> g ≈ᴳ g
refl-≈ᴳ = ⌜ refl  ⌝ᴳ

sym-≈ᴳ : ∀ {ls} {g₁ g₂ : Global ls} -> g₁ ≈ᴳ g₂ -> g₂ ≈ᴳ g₁
sym-≈ᴳ x = ⌜ sym ⌞ x ⌟ᴳ ⌝ᴳ

trans-≈ᴳ : ∀ {ls} {g₁ g₂ g₃ : Global ls} -> g₁ ≈ᴳ g₂ -> g₂ ≈ᴳ g₃ -> g₁ ≈ᴳ g₃
trans-≈ᴳ x y = ⌜ trans ⌞ x ⌟ᴳ ⌞ y ⌟ᴳ ⌝ᴳ
