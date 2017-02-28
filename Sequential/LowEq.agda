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

-- -- TODO remove?

-- data _≈ᴴ⟨_⟩_ {l π} (Δ₁ : Heap l π) (x : Dec (l ⊑ A)) (Δ₂ : Heap l π) : Set where
--   Kᴴ : ∀ {Δᴱ : Heap l π} -> Eraseᴴ x Δ₁ Δᴱ -> Eraseᴴ x Δ₂ Δᴱ -> Δ₁ ≈ᴴ⟨ x ⟩ Δ₂

--------------------------------------------------------------------------------
-- Structural low-equivalence for Heaps

_map-≅ᴴ_ : ∀ {ls} (Γ₁ Γ₂ : Heaps ls) -> Set
Γ₁ map-≅ᴴ Γ₂ = map-εᴴ Γ₁ ≡ map-εᴴ Γ₂

data _map-≈ᴴ_ {ls} (Γ₁ Γ₂ : Heaps ls) : Set where
  K-mapᴴ : ∀ {Γᴱ : Heaps ls} -> EraseMapᴴ Γ₁ Γᴱ -> EraseMapᴴ Γ₂ Γᴱ -> Γ₁ map-≈ᴴ Γ₂

map-⌞_⌟ᴴ : ∀ {ls} {Γ₁ Γ₂ : Heaps ls} -> Γ₁ map-≈ᴴ Γ₂ -> Γ₁ map-≅ᴴ Γ₂
map-⌞ K-mapᴴ e₁ e₂ ⌟ᴴ rewrite unlift-map-εᴴ e₁ | unlift-map-εᴴ e₂ = refl

map-⌜_⌝ᴴ : ∀ {ls} {Γ₁ Γ₂ : Heaps ls} -> Γ₁ map-≅ᴴ Γ₂ -> Γ₁ map-≈ᴴ Γ₂
map-⌜_⌝ᴴ {Γ₁ = Γ₁} {Γ₂} eq with lift-map-εᴴ Γ₁ | lift-map-εᴴ Γ₂
... | e₁ | e₂ rewrite eq = K-mapᴴ e₁ e₂

trans-≈ᴴ : ∀ {ls} {Γ₁ Γ₂ Γ₃ : Heaps ls} -> Γ₁ map-≈ᴴ Γ₂ -> Γ₂ map-≈ᴴ Γ₃ -> Γ₁ map-≈ᴴ Γ₃
trans-≈ᴴ a b = map-⌜ trans map-⌞ a ⌟ᴴ map-⌞ b ⌟ᴴ ⌝ᴴ

--------------------------------------------------------------------------------

_map-≅ᴹ_ : ∀ {ls} (Ms₁ Ms₂ : Memories ls) -> Set
Ms₁ map-≅ᴹ Ms₂ = map-εᴹ Ms₁ ≡ map-εᴹ Ms₂

data _map-≈ᴹ_ {ls} (Ms₁ Ms₂ : Memories ls) : Set where
  K-mapᴹ : ∀ {Msᴱ : Memories ls} -> EraseMapᴹ Ms₁ Msᴱ -> EraseMapᴹ Ms₂ Msᴱ -> Ms₁ map-≈ᴹ Ms₂

map-⌞_⌟ᴹ : ∀ {ls} {Ms₁ Ms₂ : Memories ls} -> Ms₁ map-≈ᴹ Ms₂ -> Ms₁ map-≅ᴹ Ms₂
map-⌞ K-mapᴹ e₁ e₂ ⌟ᴹ rewrite unlift-map-εᴹ e₁ | unlift-map-εᴹ e₂ = refl

map-⌜_⌝ᴹ : ∀ {ls} {Ms₁ Ms₂ : Memories ls} -> Ms₁ map-≅ᴹ Ms₂ -> Ms₁ map-≈ᴹ Ms₂
map-⌜_⌝ᴹ {Ms₁ = Ms₁} {Ms₂} eq with lift-map-εᴹ Ms₁ | lift-map-εᴹ Ms₂
... | e₁ | e₂ rewrite eq = K-mapᴹ e₁ e₂

--------------------------------------------------------------------------------

_≅ᵀˢ⟨_⟩_ : ∀ {l τ} -> TS∙ l τ -> Dec (l ⊑ A) -> TS∙ l τ -> Set
Ts₁  ≅ᵀˢ⟨ x ⟩ Ts₂ = εᵀˢ x Ts₁ ≡ εᵀˢ x Ts₂

data _≈ᵀˢ⟨_⟩_ {l τ} (Ts₁ : TS∙ l τ) (x : Dec (l ⊑ A)) (Ts₂ : TS∙ l τ) : Set where
  Kᵀˢ : ∀ {Tsᴱ : TS∙ l τ} -> Eraseᵀˢ x Ts₁ Tsᴱ -> Eraseᵀˢ x Ts₂ Tsᴱ -> Ts₁ ≈ᵀˢ⟨ x ⟩ Ts₂

⌞_⌟ᵀˢ : ∀ {l τ} {Ts₁ Ts₂ : TS∙ l τ} {x : Dec (l ⊑ A)} -> Ts₁ ≈ᵀˢ⟨ x ⟩ Ts₂ -> Ts₁ ≅ᵀˢ⟨ x ⟩ Ts₂
⌞ Kᵀˢ e₁ e₂ ⌟ᵀˢ rewrite unlift-εᵀˢ e₁ | unlift-εᵀˢ e₂ = refl

⌜_⌝ᵀˢ : ∀ {l τ} {Ts₁ Ts₂ : TS∙ l τ} {x : Dec (l ⊑ A)} -> Ts₁ ≅ᵀˢ⟨ x ⟩ Ts₂ -> Ts₁ ≈ᵀˢ⟨ x ⟩ Ts₂
⌜_⌝ᵀˢ {Ts₁ = Ts₁} {Ts₂} {x} eq with lift-εᵀˢ x Ts₁ | lift-εᵀˢ x Ts₂
... | e₁ | e₂ rewrite eq = Kᵀˢ e₁ e₂

--------------------------------------------------------------------------------

_≅ᴾ⟨_⟩_ : ∀ {l ls τ} -> Program l ls τ -> Dec (l ⊑ A) -> Program l ls τ -> Set
p₁ ≅ᴾ⟨ x ⟩ p₂ = ε₁ᴾ x p₁ ≡ ε₁ᴾ x p₂

-- Program low-equivalence
record _≈ᴾ⟨_⟩_ {l ls τ} (p₁ : Program l ls τ) (x : Dec (l ⊑ A)) (p₂ : Program l ls τ) : Set where
  constructor ⟨_,_,_⟩
  field
    Ms₁≈Ms₂ : (Ms p₁) map-≈ᴹ (Ms p₂)
    Γ₁≈Γ₂ : (Γ p₁) map-≈ᴴ (Γ p₂)
    Ts₁≈Ts₂ : (TS p₁) ≈ᵀˢ⟨ x ⟩ (TS p₂)

⌞_⌟ᴾ : ∀ {l ls τ} {p₁ p₂ : Program l ls τ} {x : Dec _} -> p₁ ≈ᴾ⟨ x ⟩ p₂ -> p₁ ≅ᴾ⟨ x ⟩ p₂
⌞ ⟨ Ms₁≈Ms₂ , Γ₁≈Γ₂ , Ts₁≈Ts₂ ⟩ ⌟ᴾ rewrite map-⌞ Ms₁≈Ms₂ ⌟ᴹ | map-⌞ Γ₁≈Γ₂ ⌟ᴴ | ⌞ Ts₁≈Ts₂ ⌟ᵀˢ = refl

⌜_⌝ᴾ : ∀ {l ls τ} {p₁ p₂ : Program l ls τ} {x : Dec _} -> p₁ ≅ᴾ⟨ x ⟩ p₂ -> p₁ ≈ᴾ⟨ x ⟩ p₂
⌜ eq ⌝ᴾ = ⟨ map-⌜ auxᴹ eq ⌝ᴹ , map-⌜ auxᴴ eq ⌝ᴴ , ⌜ auxᵀˢ eq ⌝ᵀˢ ⟩
  where auxᴹ : ∀ {l ls τ} {p₁ p₂ : Program l ls τ} -> p₁ ≡ p₂ -> (Ms p₁) ≡ (Ms p₂)
        auxᴹ refl = refl

        auxᴴ : ∀ {l ls τ} {p₁ p₂ : Program l ls τ} -> p₁ ≡ p₂ -> (Γ p₁) ≡ (Γ p₂)
        auxᴴ refl = refl

        auxᵀˢ : ∀ {l ls τ} {p₁ p₂ : Program l ls τ} -> p₁ ≡ p₂ -> (TS p₁) ≡ (TS p₂)
        auxᵀˢ refl = refl

_≅ᴾ_ : ∀ {l ls τ} -> Program l ls τ -> Program l ls τ -> Set
p₁ ≅ᴾ p₂ = p₁ ≅ᴾ⟨ (_ ⊑? A) ⟩ p₂
