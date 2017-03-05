import Lattice as L

module Sequential.Security.LowEq (𝓛 : L.Lattice) (A : L.Label 𝓛) where

open import Types 𝓛
open import Sequential.Security.Erasure 𝓛 A as SE
import Sequential.Security.Graph as G
open G 𝓛 A

--------------------------------------------------------------------------------
-- Temporarily side-step bug #2245

import Sequential.Calculus as SC
open SC 𝓛

--------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Relation.Nullary
open import Data.Maybe as M

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

refl-≈ᵀ : ∀ {π τ} {t : Term π τ} -> t ≈ᵀ t
refl-≈ᵀ = ⌜ refl ⌝ᵀ

sym-≈ᵀ : ∀ {π τ} {t₁ t₂ : Term π τ} -> t₁ ≈ᵀ t₂ -> t₂ ≈ᵀ t₁
sym-≈ᵀ t₁≈t₂ = ⌜ sym ⌞ t₁≈t₂ ⌟ᵀ ⌝ᵀ

trans-≈ᵀ : ∀ {π τ} {t₁ t₂ t₃ : Term π τ} -> t₁ ≈ᵀ t₂ -> t₂ ≈ᵀ t₃ -> t₁ ≈ᵀ t₃
trans-≈ᵀ t₁≈t₂ t₂≈t₃ = ⌜ trans ⌞ t₁≈t₂ ⌟ᵀ ⌞ t₂≈t₃ ⌟ᵀ ⌝ᵀ

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

_map-≅ᵀ_ : ∀ {l π} -> Heap l π  -> Heap l π -> Set
Δ₁ map-≅ᵀ Δ₂ = map-εᵀ Δ₁ ≡ map-εᵀ Δ₂

data _map-≈ᵀ_ {l π} (Δ₁ Δ₂ : Heap l π) : Set where
  K-mapᵀ : ∀ {Δᴱ : Heap l π} -> (e₁ : EraseMapᵀ Δ₁ Δᴱ) (e₂ : EraseMapᵀ Δ₂ Δᴱ) -> Δ₁ map-≈ᵀ Δ₂

map-⌞_⌟ᵀ : ∀ {l π} {Δ₁ Δ₂ : Heap l π} -> Δ₁ map-≈ᵀ Δ₂ -> Δ₁ map-≅ᵀ Δ₂
map-⌞ K-mapᵀ e₁ e₂ ⌟ᵀ rewrite unlift-map-εᵀ e₁ | unlift-map-εᵀ e₂ = refl

map-⌜_⌝ᵀ : ∀ {l π} {Δ₁ Δ₂ : Heap l π} -> Δ₁ map-≅ᵀ Δ₂ -> Δ₁ map-≈ᵀ Δ₂
map-⌜_⌝ᵀ {Δ₁ = Δ₁} {Δ₂} eq with lift-map-εᵀ Δ₁ | lift-map-εᵀ Δ₂
... | e₁ | e₂ rewrite eq = K-mapᵀ e₁ e₂


--------------------------------------------------------------------------------

_≅ᴴ⟨_⟩_ : ∀ {l} -> Heap∙ l -> Dec (l ⊑ A) -> Heap∙ l -> Set
H₁ ≅ᴴ⟨ x ⟩ H₂ = εᴴ x H₁ ≡ εᴴ x H₂

data _≈ᴴ⟨_⟩_ {l} (H₁ : Heap∙ l) (x : Dec (l ⊑ A)) (H₂ : Heap∙ l) : Set where
  Kᴴ : ∀ {Hᴱ : Heap∙ l} -> (e₁ : Eraseᴴ x H₁ Hᴱ) (e₂ : Eraseᴴ x H₂ Hᴱ) -> H₁ ≈ᴴ⟨ x ⟩ H₂

⌞_⌟ᴴ : ∀ {l} {H₁ H₂ : Heap∙ l} {x : Dec (l ⊑ A)} -> H₁ ≈ᴴ⟨ x ⟩ H₂ -> H₁ ≅ᴴ⟨ x ⟩ H₂
⌞ Kᴴ e₁ e₂ ⌟ᴴ rewrite unlift-εᴴ e₁ | unlift-εᴴ e₂ = refl

⌜_⌝ᴴ : ∀ {l} {H₁ H₂ : Heap∙ l} {x : Dec (l ⊑ A)} -> H₁ ≅ᴴ⟨ x ⟩ H₂ -> H₁ ≈ᴴ⟨ x ⟩ H₂
⌜_⌝ᴴ {H₁ = H₁} {H₂} {x} eq with lift-εᴴ x H₁ | lift-εᴴ x H₂
... | e₁ | e₂ rewrite eq = Kᴴ e₁ e₂

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

_≅ᴹ⟨_⟩_ : ∀ {l} -> Memory l -> Dec (l ⊑ A) -> Memory l -> Set
M₁ ≅ᴹ⟨ x ⟩ M₂ = εᴹ x M₁ ≡ εᴹ x M₂

data _≈ᴹ⟨_⟩_ {l} (M₁ : Memory l) (x : Dec (l ⊑ A)) (M₂ : Memory l) : Set where
  Kᴹ : ∀ {Mᴱ : Memory l} -> Eraseᴹ x M₁ Mᴱ -> Eraseᴹ x M₂ Mᴱ -> M₁ ≈ᴹ⟨ x ⟩ M₂

⌞_⌟ᴹ : ∀ {l} {M₁ M₂ : Memory l} {x : Dec _}  -> M₁ ≈ᴹ⟨ x ⟩ M₂ -> M₁ ≅ᴹ⟨ x ⟩ M₂
⌞ Kᴹ e₁ e₂ ⌟ᴹ rewrite unlift-εᴹ e₁ | unlift-εᴹ e₂ = refl

⌜_⌝ᴹ : ∀ {l} {M₁ M₂ : Memory l} {x : Dec (l ⊑ A)} -> M₁ ≅ᴹ⟨ x ⟩ M₂ -> M₁ ≈ᴹ⟨ x ⟩  M₂
⌜_⌝ᴹ {M₁ = M₁} {M₂} {x} eq with lift-εᴹ x M₁ | lift-εᴹ x M₂
... | e₁ | e₂ rewrite eq = Kᴹ e₁ e₂

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

trans-≈ᴹ : ∀ {ls} {Ms₁ Ms₂ Ms₃ : Memories ls} -> Ms₁ map-≈ᴹ Ms₂ -> Ms₂ map-≈ᴹ Ms₃ -> Ms₁ map-≈ᴹ Ms₃
trans-≈ᴹ a b = map-⌜ trans map-⌞ a ⌟ᴹ map-⌞ b ⌟ᴹ ⌝ᴹ


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


refl-≈ᵀˢ : ∀ {l τ} {Ts : TS∙ l τ} -> Ts ≈ᵀˢ⟨ l ⊑? A ⟩ Ts
refl-≈ᵀˢ = ⌜ refl ⌝ᵀˢ

sym-≈ᵀˢ : ∀ {l τ} {Ts₁ Ts₂ : TS∙ l τ} {x : Dec (l ⊑ A)} -> Ts₁ ≈ᵀˢ⟨ x ⟩ Ts₂ -> Ts₂ ≈ᵀˢ⟨ x ⟩ Ts₁
sym-≈ᵀˢ Ts₁≈Ts₂ = ⌜ sym ⌞ Ts₁≈Ts₂ ⌟ᵀˢ ⌝ᵀˢ

trans-≈ᵀˢ : ∀ {l τ} {Ts₁ Ts₂ Ts₃ : TS∙ l τ} {x : Dec (l ⊑ A)} -> Ts₁ ≈ᵀˢ⟨ x ⟩ Ts₂ -> Ts₂ ≈ᵀˢ⟨ x ⟩ Ts₃ -> Ts₁ ≈ᵀˢ⟨ x ⟩ Ts₃
trans-≈ᵀˢ Ts₁≈Ts₂ Ts₂≈Ts₃ = ⌜ trans ⌞ Ts₁≈Ts₂ ⌟ᵀˢ ⌞ Ts₂≈Ts₃ ⌟ᵀˢ ⌝ᵀˢ

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

refl-≈ᴾ : ∀ {l ls τ} {p : Program l ls τ} -> p ≈ᴾ⟨ l ⊑? A ⟩ p
refl-≈ᴾ {l} = ⌜ refl ⌝ᴾ

sym-≈ᴾ : ∀ {l ls τ} {p₁ p₂ : Program l ls τ} {x : Dec (l ⊑ A)} -> p₁ ≈ᴾ⟨ x ⟩ p₂ -> p₂ ≈ᴾ⟨ x ⟩ p₁
sym-≈ᴾ eq = ⌜ sym ⌞ eq ⌟ᴾ ⌝ᴾ

trans-≈ᴾ : ∀ {l ls τ} {p₁ p₂ p₃ : Program l ls τ} {x : Dec (l ⊑ A)} -> p₁ ≈ᴾ⟨ x ⟩ p₂ -> p₂ ≈ᴾ⟨ x ⟩ p₃ -> p₁ ≈ᴾ⟨ x ⟩ p₃
trans-≈ᴾ eq₁ eq₂ = ⌜ trans ⌞ eq₁ ⌟ᴾ ⌞ eq₂ ⌟ᴾ ⌝ᴾ
