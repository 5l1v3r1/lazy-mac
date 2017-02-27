import Lattice as L

module Sequential.LowEq (𝓛 : L.Lattice) (A : L.Label 𝓛) where

open import Types 𝓛
open import Sequential.Erasure 𝓛 A as SE
open import Sequential.Graph 𝓛 A

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

_≡ᴱ_ : ∀ {l π} -> Heap l π -> Heap l π -> Set
_≡ᴱ_ = _≡_

_≅ᴴ_ : ∀ {ls} (H₁ H₂ : Heaps ls) -> Set
H₁ ≅ᴴ H₂ = map-εᴴ H₁ ≡ map-εᴴ H₂

--------------------------------------------------------------------------------

_≅ᵀ_ : ∀ {π τ} (t₁ t₂ : Term π τ) -> Set
t₁ ≅ᵀ t₂ = εᵀ t₁ ≡ εᵀ t₂

data _≈ᵀ_ {π τ} (t₁ t₂ : Term π τ) : Set where
  ⟨_,_⟩ : ∀ {t' : Term π τ} -> (e₁ : Eraseᵀ t₁ t') (e₂ : Eraseᵀ t₂ t') -> t₁ ≈ᵀ t₂

⌞_⌟ᵀ : ∀ {π τ} {t₁ t₂ : Term π τ} -> t₁ ≈ᵀ t₂ -> t₁ ≅ᵀ t₂
⌞ ⟨ e₁ , e₂ ⟩ ⌟ᵀ rewrite unlift-εᵀ e₁ | unlift-εᵀ e₂ = refl

⌜_⌝ᵀ : ∀ {π τ} {t₁ t₂ : Term π τ} -> t₁ ≅ᵀ t₂ -> t₁ ≈ᵀ t₂
⌜_⌝ᵀ {t₁ = t₁} {t₂} eq with lift-εᵀ t₁ | lift-εᵀ t₂
... | x | y rewrite eq = ⟨ x , y ⟩

--------------------------------------------------------------------------------

_≅ᶜ_ : ∀ {l π τ₁ τ₂} (C₁ C₂ : Cont l π τ₁ τ₂) -> Set
C₁ ≅ᶜ C₂ = εᶜ C₁ ≡ εᶜ C₂

data _≈ᶜ_ {l π τ₁ τ₂} (C₁ C₂ : Cont l π τ₁ τ₂) : Set where
  Kᶜ : ∀ {Cᴱ : Cont l π τ₁ τ₂} -> Eraseᶜ C₁ Cᴱ -> Eraseᶜ C₂ Cᴱ -> C₁ ≈ᶜ C₂

⌞_⌟ᶜ : ∀ {l π τ₁ τ₂} {C₁ C₂ : Cont l π τ₁ τ₂} -> C₁ ≈ᶜ C₂ -> C₁ ≅ᶜ C₂
⌞ Kᶜ e₁ e₂ ⌟ᶜ rewrite unlift-εᶜ e₁ | unlift-εᶜ e₂ = refl

⌜_⌝ᶜ : ∀ {l π τ₁ τ₂} {C₁ C₂ : Cont l π τ₁ τ₂} -> C₁ ≅ᶜ C₂ -> C₁ ≈ᶜ C₂
⌜_⌝ᶜ {C₁ = C₁} {C₂} eq with lift-εᶜ C₁ | lift-εᶜ C₂
... | e₁ | e₂ rewrite eq = Kᶜ e₁ e₂

--------------------------------------------------------------------------------

_≅ˢ_ : ∀ {l π τ₁ τ₂} (S₁ S₂ : Stack l π τ₁ τ₂) -> Set
S₁ ≅ˢ S₂ = εˢ S₁ ≡ εˢ S₂

data _≈ˢ_ {l π τ₁ τ₂ } (S₁ S₂ : Stack l π τ₁ τ₂) : Set where
  Kˢ : ∀ {Sᴱ : Stack l π τ₁ τ₂} -> Eraseˢ S₁ Sᴱ -> Eraseˢ S₂ Sᴱ -> S₁ ≈ˢ S₂

⌞_⌟ˢ : ∀ {l π τ₁ τ₂} {S₁ S₂ : Stack l π τ₁ τ₂} -> S₁ ≈ˢ S₂ -> S₁ ≅ˢ S₂
⌞ Kˢ e₁ e₂ ⌟ˢ rewrite unlift-εˢ e₁ | unlift-εˢ e₂ = refl

⌜_⌝ˢ : ∀ {l π τ₁ τ₂} {S₁ S₂ : Stack l π τ₁ τ₂} -> S₁ ≅ˢ S₂ -> S₁ ≈ˢ S₂
⌜_⌝ˢ {S₁ = S₁} {S₂} eq with lift-εˢ S₁ | lift-εˢ S₂
... | e₁ | e₂ rewrite eq = Kˢ e₁ e₂

--------------------------------------------------------------------------------

-- TODO remove?

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

-- data _map-≈ᵀ_ {l π} (Δ₁ Δ₂ : Heap l π) : Set where
--   map-Kᵀ : ∀ {Δᴱ : Heap l π} -> EraseMapᵀ Δ₁ Δᴱ -> EraseMapᵀ Δ₂ Δᴱ -> Δ₁ map-≈ᵀ Δ₂

-- _≅ᴱ_ : ∀ {π l} -> (Δ₁ Δ₂ : Heap l π) -> Set
-- Δ₁ ≅ᴱ Δ₂ = map-εᵀ Δ₁ ≡ map-εᵀ Δ₂

-- ⌜_⌝ᴱ : ∀ {l π} {Δ₁ Δ₂ : Heap l π} -> Δ₁ ≅ᴱ Δ₂ -> Δ₁ map-≈ᵀ Δ₂
-- ⌜_⌝ᴱ {Δ₁ = SC.[]} {SC.[]} refl = []
-- ⌜_⌝ᴱ {Δ₁ = SC.[]} {SC.∙} ()
-- ⌜_⌝ᴱ {Δ₁ = t SC.∷ Δ₁} {t₁ SC.∷ Δ₂} eq =  ⌜ (proj₁ (split eq)) ⌝ᴹᵀ ∷ ⌜ proj₂ (split eq) ⌝ᴱ
--   where split : ∀ {l π τ} {mt₁ mt₂ : Maybe (Term π τ)} {Δ₁ Δ₂ : Heap l π} -> (mt₁ ∷ Δ₁) ≡ᴱ (mt₂ ∷ Δ₂) -> mt₁ ≡ mt₂ × Δ₁ ≡ Δ₂
--         split refl = refl P., refl
-- ⌜_⌝ᴱ {Δ₁ = t SC.∷ Δ₁} {SC.∙} ()
-- ⌜_⌝ᴱ {Δ₁ = SC.∙} {SC.[]} ()
-- ⌜_⌝ᴱ {Δ₁ = SC.∙} {t SC.∷ Δ₂} ()
-- ⌜_⌝ᴱ {Δ₁ = SC.∙} {SC.∙} refl = ∙

-- ⌞_⌟ᴱ : ∀ {l π} {Δ₁ Δ₂ : Heap l π} -> Δ₁ map-≈ᵀ Δ₂ -> Δ₁ ≅ᴱ Δ₂
-- ⌞ [] ⌟ᴱ = refl
-- ⌞ nothing ∷ eq ⌟ᴱ rewrite  ⌞ eq ⌟ᴱ = refl
-- ⌞ just x ∷ eq ⌟ᴱ rewrite ⌞ x ⌟ᵀ | ⌞ eq ⌟ᴱ  = refl
-- ⌞ ∙ ⌟ᴱ = refl

--------------------------------------------------------------------------------

data _≈ᴴ⟨_⟩_ {l π} (Δ₁ : Heap l π) (x : Dec (l ⊑ A)) (Δ₂ : Heap l π) : Set where
  Kᴴ : ∀ {Δᴱ : Heap l π} -> Eraseᴴ x Δ₁ Δᴱ -> Eraseᴴ x Δ₂ Δᴱ -> Δ₁ ≈ᴴ⟨ x ⟩ Δ₂

-- ⟨_,_⟩ : ∀ {π} {l⊑A : l ⊑ A} {Δ₁ Δ₂ : Heap l π} -> (M : Memory l) -> Δ₁ map-≈ᵀ Δ₂ -> ⟨ M , Δ₁ ⟩ ≈ᴴ⟨ yes l⊑A ⟩ ⟨ M , Δ₂ ⟩
--   ∙ᴸ : {l⊑A : l ⊑ A} -> ∙ ≈ᴴ⟨ yes l⊑A ⟩ ∙
--   ∙ : ∀ {H₁ H₂ : Heap l} {l⋤A : l ⋤ A} -> H₁ ≈ᴴ⟨ no l⋤A ⟩ H₂


-- data _≈ᴹ⟨_⟩_ {l} : Heap l -> Dec (l ⊑ A) -> Heap l -> Set where
--   ⟨_,_⟩ : ∀ {π} {l⊑A : l ⊑ A} {Δ₁ Δ₂ : Heap l π} -> (M : Memory l) -> Δ₁ map-≈ᵀ Δ₂ -> ⟨ M , Δ₁ ⟩ ≈ᴹ⟨ yes l⊑A ⟩ ⟨ M , Δ₂ ⟩
--   ∙ᴸ : {l⊑A : l ⊑ A} -> ∙ ≈ᴹ⟨ yes l⊑A ⟩ ∙
--   ∙ : ∀ {H₁ H₂ : Heap l} {l⋤A : l ⋤ A} -> H₁ ≈ᴹ⟨ no l⋤A ⟩ H₂


--------------------------------------------------------------------------------

-- -- Structural low-equivalence for Heaps
-- data _≈ᴴ_ : ∀ {ls} -> Heaps ls -> Heaps ls -> Set where
--   nil : [] ≈ᴴ []
--   cons : ∀ {ls} {l} {u : Unique l ls} {Γ₁ Γ₂ : Heaps ls} {H₁ H₂ : Heap l} (x : Dec (l ⊑ A)) ->
--                H₁ ≈ˣ⟨ x ⟩ H₂ -> Γ₁ ≈ᴴ Γ₂ -> (_∷_ {{u}} H₁ Γ₁) ≈ᴴ (_∷_ {{u}} H₂ Γ₂)


-- split : ∀ {ls} {l} {u₁ u₂ : Unique l ls} {Γ₁ Γ₂ : Heaps ls} {H₁ H₂ : Heap l} ->
--                  _≡_ {_} {Heaps (l ∷ ls)}  (_∷_ {{u₁}} H₁ Γ₁) (_∷_ {{u₂}} H₂ Γ₂ ) -> u₁ ≡ u₂ × H₁ ≡ H₂ × Γ₁ ≡ Γ₂
-- split refl = refl P., refl P., refl

-- split₁ᴴ : ∀ {l π₁ π₂} {M₁ M₂ : Memory l} {Δ₁ : Heap l π₁} {Δ₂ : Heap l π₂} -> _≡_ {_} {Heap l} ⟨ M₁ , Δ₁ ⟩ ⟨ M₂ , Δ₂ ⟩ -> π₁ ≡ π₂ × M₁ ≡ M₂
-- split₁ᴴ refl = refl P., refl

-- split₂ᴴ : ∀ {l π} {M₁ M₂ : Memory l} {Δ₁ Δ₂ : Heap l π} -> _≡_ {_} {Heap l} ⟨ M₁ , Δ₁ ⟩ ⟨ M₂ , Δ₂ ⟩ -> Δ₁ ≡ Δ₂
-- split₂ᴴ refl = refl

-- aux₂ : ∀ {l} {H₁ H₂ : Heap l} -> (x : Dec (l ⊑ A)) -> SE.εᴹ x H₁ ≡ SE.εᴹ x H₂ -> H₁ ≈ˣ⟨ x ⟩ H₂
-- aux₂ {H₁ = SC.⟨ x , x₁ ⟩} {SC.⟨ x₂ , x₃ ⟩} (yes p) eq with split₁ᴴ eq
-- aux₂ {l} {SC.⟨ M , x₁ ⟩} {SC.⟨ .M , x₃ ⟩} (yes p) eq₁ | refl P., refl = ⟨ M , ⌜ split₂ᴴ eq₁ ⌝ᴱ ⟩
-- aux₂ {H₁ = SC.⟨ x , x₁ ⟩} {SC.∙} (yes p) ()
-- aux₂ {H₁ = SC.∙} {SC.⟨ x , x₁ ⟩} (yes p) ()
-- aux₂ {H₁ = SC.∙} {SC.∙} (yes p) refl = ∙ᴸ
-- aux₂ (no ¬p) eq₁ = ∙

-- ⌜_⌝ᴴ : ∀ {ls} {Γ₁ Γ₂ : Heaps ls} -> Γ₁ ≅ᴴ Γ₂ -> Γ₁ ≈ᴴ Γ₂
-- ⌜_⌝ᴴ {Γ₁ = []} {[]} refl = nil
-- ⌜_⌝ᴴ {Γ₁ = H₁ ∷ Γ₁} {H₂ ∷ Γ₂} eq with split eq
-- ... | eq₁ P., eq₂ P., eq₃ rewrite eq₁ = cons (_ ⊑? A) (aux₂ (_ ⊑? A) eq₂) ⌜ eq₃ ⌝ᴴ

-- ⌞_⌟ᴴ : ∀ {ls} {Γ₁ Γ₂ : Heaps ls} -> Γ₁ ≈ᴴ Γ₂ -> Γ₁ ≅ᴴ Γ₂
-- ⌞ nil ⌟ᴴ = refl
-- ⌞ cons {l = l}  (yes l⊑A) ⟨ M , x ⟩ eq₂ ⌟ᴴ with l ⊑? A
-- ... | yes p rewrite ⌞ x ⌟ᴱ | ⌞ eq₂ ⌟ᴴ = refl
-- ... | no ¬p = ⊥-elim (¬p l⊑A)
-- ⌞ cons ._ ∙ᴸ eq₂ ⌟ᴴ rewrite ⌞ eq₂ ⌟ᴴ = refl
-- ⌞ cons {l = l} (no _) ∙ eq₂ ⌟ᴴ rewrite ⌞ eq₂ ⌟ᴴ with l ⊑? A
-- ⌞ cons (no l⋤A) ∙ eq₂ ⌟ᴴ | yes p = ⊥-elim (l⋤A p)
-- ⌞ cons (no _) ∙ eq₂ ⌟ᴴ | no ¬p = refl

-- --------------------------------------------------------------------------------

_≅ᴾ⟨_⟩_ : ∀ {l ls τ} -> Program l ls τ -> Dec (l ⊑ A) -> Program l ls τ -> Set
p₁ ≅ᴾ⟨ x ⟩ p₂ = ε₁ᴾ x p₁ ≡ ε₁ᴾ x p₂

-- Program low-equivalence
data _≈ᴾ⟨_⟩_ {l ls τ} (p₁ : Program l ls τ) (x : Dec (l ⊑ A)) (p₂ : Program l ls τ) : Set where
  Kᴾ : ∀ {pᴱ : Program l ls τ} -> Eraseᴾ x p₁ pᴱ -> Eraseᴾ x p₂ pᴱ -> p₁ ≈ᴾ⟨ x ⟩ p₂

⌜_⌝ᴾ : ∀ {l ls τ} {p₁ p₂ : Program l ls τ} {x : Dec _} -> p₁ ≅ᴾ⟨ x ⟩ p₂ -> p₁ ≈ᴾ⟨ x ⟩ p₂
⌜_⌝ᴾ {p₁ = p₁} {p₂} {x} eq with lift-εᴾ x p₁ | lift-εᴾ x p₂
... | e₁ | e₂ rewrite eq = Kᴾ e₁ e₂

⌞_⌟ᴾ : ∀ {l ls τ} {p₁ p₂ : Program l ls τ} {x : Dec _} -> p₁ ≈ᴾ⟨ x ⟩ p₂ -> p₁ ≅ᴾ⟨ x ⟩ p₂
⌞ Kᴾ e₁ e₂ ⌟ᴾ rewrite unlift-εᴾ e₁ | unlift-εᴾ e₂ = refl

_≅ᴾ_ : ∀ {l ls τ} -> Program l ls τ -> Program l ls τ -> Set
p₁ ≅ᴾ p₂ = p₁ ≅ᴾ⟨ (_ ⊑? A) ⟩ p₂
