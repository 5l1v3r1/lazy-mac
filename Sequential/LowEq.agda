import Lattice as L

module Sequential.LowEq (𝓛 : L.Lattice) (A : L.Label 𝓛) where

open import Types 𝓛
open import Sequential.Erasure 𝓛 A as SE

--------------------------------------------------------------------------------
-- Temporarily side-step bug #2245

import Sequential.Calculus as SC
open SC 𝓛

--------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Relation.Nullary
open import Data.Maybe as M
open import Data.Product using (_×_ ; proj₁ ; proj₂)
import Data.Product as P

_≡ᴱ_ : ∀ {l π} -> Env l π -> Env l π -> Set
_≡ᴱ_ = _≡_

_≅ᴴ_ : ∀ {ls} (H₁ H₂ : Heaps ls) -> Set
H₁ ≅ᴴ H₂ = εᴴ H₁ ≡ εᴴ H₂

--------------------------------------------------------------------------------

_≅ᵀ_ : ∀ {π τ} (t₁ t₂ : Term π τ) -> Set
t₁ ≅ᵀ t₂ = εᵀ t₁ ≡ εᵀ t₂

postulate _≈ᵀ_ : ∀ {π τ} -> Term π τ -> Term π τ -> Set
postulate ⌞_⌟ᵀ : ∀ {π τ} {t₁ t₂ : Term π τ} -> t₁ ≈ᵀ t₂ -> t₁ ≅ᵀ t₂
postulate ⌜_⌝ᵀ : ∀ {π τ} {t₁ t₂ : Term π τ} -> t₁ ≅ᵀ t₂ -> t₁ ≈ᵀ t₂

--------------------------------------------------------------------------------

data _≈ᴹᵀ_ {π τ} : Maybe (Term π τ) -> Maybe (Term π τ) -> Set where
  nothing : nothing ≈ᴹᵀ nothing
  just : ∀ {t₁ t₂ : Term π τ} -> t₁ ≈ᵀ t₂ -> just t₁ ≈ᴹᵀ just t₂

_≅ᴹᵀ_ : ∀ {π τ} (mt₁ mt₂ : Maybe (Term π τ)) -> Set
mt₁ ≅ᴹᵀ mt₂ = M.map εᵀ mt₁ ≡ M.map εᵀ mt₂

⌜_⌝ᴹᵀ : ∀ {π τ} {mt₁ mt₂ : Maybe (Term π τ)} -> mt₁ ≅ᴹᵀ mt₂ -> mt₁ ≈ᴹᵀ mt₂
⌜_⌝ᴹᵀ {mt₁ = just x} {just x₁} eq = just ⌜ split eq ⌝ᵀ
  where split : ∀ {π τ} {t₁ t₂ : Term π τ} -> _≡_ {_} {Maybe (Term π τ)} (just t₁) (just t₂) -> t₁ ≡ t₂
        split refl = refl
⌜_⌝ᴹᵀ {mt₁ = just x} {nothing} ()
⌜_⌝ᴹᵀ {mt₁ = nothing} {just x} ()
⌜_⌝ᴹᵀ {mt₁ = nothing} {nothing} refl = nothing

--------------------------------------------------------------------------------

data _≈ᴱ_ {l} : ∀ {π} -> Env l π -> Env l π -> Set where
  [] : [] ≈ᴱ []
  _∷_ : ∀ {π τ} {Δ₁ Δ₂ : Env l π} {mt₁ mt₂ : Maybe (Term π τ)} -> mt₁ ≈ᴹᵀ mt₂ -> Δ₁ ≈ᴱ Δ₂ -> (mt₁ ∷ Δ₁) ≈ᴱ (mt₂ ∷ Δ₂)
  ∙ : ∀ {π} -> ∙ {{π = π}} ≈ᴱ ∙

_≅ᴱ_ : ∀ {π l} -> (Δ₁ Δ₂ : Env l π) -> Set
Δ₁ ≅ᴱ Δ₂ = εᴱ Δ₁ ≡ εᴱ Δ₂

⌜_⌝ᴱ : ∀ {l π} {Δ₁ Δ₂ : Env l π} -> Δ₁ ≅ᴱ Δ₂ -> Δ₁ ≈ᴱ Δ₂
⌜_⌝ᴱ {Δ₁ = SC.[]} {SC.[]} refl = []
⌜_⌝ᴱ {Δ₁ = SC.[]} {SC.∙} ()
⌜_⌝ᴱ {Δ₁ = t SC.∷ Δ₁} {t₁ SC.∷ Δ₂} eq =  ⌜ (proj₁ (split eq)) ⌝ᴹᵀ ∷ ⌜ proj₂ (split eq) ⌝ᴱ
  where split : ∀ {l π τ} {mt₁ mt₂ : Maybe (Term π τ)} {Δ₁ Δ₂ : Env l π} -> (mt₁ ∷ Δ₁) ≡ᴱ (mt₂ ∷ Δ₂) -> mt₁ ≡ mt₂ × Δ₁ ≡ Δ₂
        split refl = refl P., refl
⌜_⌝ᴱ {Δ₁ = t SC.∷ Δ₁} {SC.∙} ()
⌜_⌝ᴱ {Δ₁ = SC.∙} {SC.[]} ()
⌜_⌝ᴱ {Δ₁ = SC.∙} {t SC.∷ Δ₂} ()
⌜_⌝ᴱ {Δ₁ = SC.∙} {SC.∙} refl = ∙

⌞_⌟ᴱ : ∀ {l π} {Δ₁ Δ₂ : Env l π} -> Δ₁ ≈ᴱ Δ₂ -> Δ₁ ≅ᴱ Δ₂
⌞ [] ⌟ᴱ = refl
⌞ nothing ∷ eq ⌟ᴱ rewrite  ⌞ eq ⌟ᴱ = refl
⌞ just x ∷ eq ⌟ᴱ rewrite ⌞ x ⌟ᵀ | ⌞ eq ⌟ᴱ  = refl
⌞ ∙ ⌟ᴱ = refl

--------------------------------------------------------------------------------

data _≈ˣ⟨_⟩_ {l} : Heap l -> Dec (l ⊑ A) -> Heap l -> Set where
  ⟨_,_⟩ : ∀ {π} {l⊑A : l ⊑ A} {Δ₁ Δ₂ : Env l π} -> (M : Memory l) -> Δ₁ ≈ᴱ Δ₂ -> ⟨ M , Δ₁ ⟩ ≈ˣ⟨ yes l⊑A ⟩ ⟨ M , Δ₂ ⟩
  -- TODO do we need to model bullet ∙ heaps ?
  ∙ᴸ : {l⊑A : l ⊑ A} -> ∙ ≈ˣ⟨ yes l⊑A ⟩ ∙
  ∙ : ∀ {H₁ H₂ : Heap l} {l⋤A : l ⋤ A} -> H₁ ≈ˣ⟨ no l⋤A ⟩ H₂

--------------------------------------------------------------------------------

-- Structural low-equivalence for Heaps
data _≈ᴴ_ : ∀ {ls} -> Heaps ls -> Heaps ls -> Set where
  nil : [] ≈ᴴ []
  cons : ∀ {ls} {l} {u : Unique l ls} {Γ₁ Γ₂ : Heaps ls} {H₁ H₂ : Heap l} (x : Dec (l ⊑ A)) ->
               H₁ ≈ˣ⟨ x ⟩ H₂ -> Γ₁ ≈ᴴ Γ₂ -> (_∷_ {{u}} H₁ Γ₁) ≈ᴴ (_∷_ {{u}} H₂ Γ₂)


split : ∀ {ls} {l} {u₁ u₂ : Unique l ls} {Γ₁ Γ₂ : Heaps ls} {H₁ H₂ : Heap l} ->
                 _≡_ {_} {Heaps (l ∷ ls)}  (_∷_ {{u₁}} H₁ Γ₁) (_∷_ {{u₂}} H₂ Γ₂ ) -> u₁ ≡ u₂ × H₁ ≡ H₂ × Γ₁ ≡ Γ₂
split refl = refl P., refl P., refl

split₁ᴴ : ∀ {l π₁ π₂} {M₁ M₂ : Memory l} {Δ₁ : Env l π₁} {Δ₂ : Env l π₂} -> _≡_ {_} {Heap l} ⟨ M₁ , Δ₁ ⟩ ⟨ M₂ , Δ₂ ⟩ -> π₁ ≡ π₂ × M₁ ≡ M₂
split₁ᴴ refl = refl P., refl

split₂ᴴ : ∀ {l π} {M₁ M₂ : Memory l} {Δ₁ Δ₂ : Env l π} -> _≡_ {_} {Heap l} ⟨ M₁ , Δ₁ ⟩ ⟨ M₂ , Δ₂ ⟩ -> Δ₁ ≡ Δ₂
split₂ᴴ refl = refl

aux₂ : ∀ {l} {H₁ H₂ : Heap l} -> (x : Dec (l ⊑ A)) -> SE.εᴹ x H₁ ≡ SE.εᴹ x H₂ -> H₁ ≈ˣ⟨ x ⟩ H₂
aux₂ {H₁ = SC.⟨ x , x₁ ⟩} {SC.⟨ x₂ , x₃ ⟩} (yes p) eq with split₁ᴴ eq
aux₂ {l} {SC.⟨ M , x₁ ⟩} {SC.⟨ .M , x₃ ⟩} (yes p) eq₁ | refl P., refl = ⟨ M , ⌜ split₂ᴴ eq₁ ⌝ᴱ ⟩
aux₂ {H₁ = SC.⟨ x , x₁ ⟩} {SC.∙} (yes p) ()
aux₂ {H₁ = SC.∙} {SC.⟨ x , x₁ ⟩} (yes p) ()
aux₂ {H₁ = SC.∙} {SC.∙} (yes p) refl = ∙ᴸ
aux₂ (no ¬p) eq₁ = ∙
⌜_⌝ᴴ : ∀ {ls} {Γ₁ Γ₂ : Heaps ls} -> Γ₁ ≅ᴴ Γ₂ -> Γ₁ ≈ᴴ Γ₂
⌜_⌝ᴴ {Γ₁ = []} {[]} refl = nil
⌜_⌝ᴴ {Γ₁ = H₁ ∷ Γ₁} {H₂ ∷ Γ₂} eq with split eq
... | eq₁ P., eq₂ P., eq₃ rewrite eq₁ = cons (_ ⊑? A) (aux₂ (_ ⊑? A) eq₂) ⌜ eq₃ ⌝ᴴ

⌞_⌟ᴴ : ∀ {ls} {Γ₁ Γ₂ : Heaps ls} -> Γ₁ ≈ᴴ Γ₂ -> Γ₁ ≅ᴴ Γ₂
⌞ nil ⌟ᴴ = refl
⌞ cons {l = l}  (yes l⊑A) ⟨ M , x ⟩ eq₂ ⌟ᴴ with l ⊑? A
... | yes p rewrite ⌞ x ⌟ᴱ | ⌞ eq₂ ⌟ᴴ = refl
... | no ¬p = ⊥-elim (¬p l⊑A)
⌞ cons ._ ∙ᴸ eq₂ ⌟ᴴ rewrite ⌞ eq₂ ⌟ᴴ = refl
⌞ cons {l = l} (no _) ∙ eq₂ ⌟ᴴ rewrite ⌞ eq₂ ⌟ᴴ with l ⊑? A
⌞ cons (no l⋤A) ∙ eq₂ ⌟ᴴ | yes p = ⊥-elim (l⋤A p)
⌞ cons (no _) ∙ eq₂ ⌟ᴴ | no ¬p = refl

--------------------------------------------------------------------------------
