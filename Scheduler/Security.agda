open import Lattice using (Lattice ; Label)
import Scheduler.Base as S

module Scheduler.Security (𝓛 : Lattice) (A : Label 𝓛) where

  open import Scheduler.Base 𝓛
  open Lattice.Lattice 𝓛

  open import Data.Nat
  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality

  -- Erasure of labeled events
  εᴱ : ∀ {l} -> Event l -> Event l
  εᴱ (Fork h n p) with h ⊑? A
  εᴱ (Fork h n p) | yes _ = Fork h n p
  εᴱ (Fork h n p) | no ¬p = Step
  εᴱ e = e

  -- Erasure of labeled messages
  εᴹ : ∀ {l} -> Dec (l ⊑ A) -> Message l -> Message l
  εᴹ (yes p) (l , n , e) = l , n , εᴱ e
  εᴹ (no ¬p) (l , n , e) = l , n , ∙


  record NIˢ (𝓢 : S.Scheduler 𝓛) : Set₁ where
    open Scheduler 𝓢 public
    field
      εˢ  : State -> State
      _≈ˢ_ : State -> State -> Set

      ⌞_⌟ : ∀ {Σ₁ Σ₂} -> Σ₁ ≈ˢ Σ₂ -> εˢ Σ₁ ≡ εˢ Σ₂
      ⌜_⌝ : ∀ {Σ₁ Σ₂} -> εˢ Σ₁ ≡ εˢ Σ₂ -> Σ₁ ≈ˢ Σ₂

      εˢ-simᴸ : ∀ {Σ₁ Σ₂ : State} {l} {m : Message l} -> (l⊑A : l ⊑ A) -> Σ₁ ⟶ Σ₂ ↑ m -> (εˢ Σ₁) ⟶ (εˢ Σ₂) ↑ (εᴹ (yes l⊑A) m)
      εˢ-simᴴ : ∀ {Σ₁ Σ₂ l} {m : Message l} -> l ⋤ A -> Σ₁ ⟶ Σ₂ ↑ m -> Σ₁ ≈ˢ Σ₂

      -- Annotated low-equivalence
      _≈ˢ-⟨_,_⟩_ : State -> ℕ -> ℕ -> State -> Set
      offset₁ : {Σ₁ Σ₂ : State} -> Σ₁ ≈ˢ Σ₂ -> ℕ
      offset₂ : {Σ₁ Σ₂ : State} -> Σ₁ ≈ˢ Σ₂ -> ℕ
      align : ∀ {Σ₁ Σ₂} -> (eq : Σ₁ ≈ˢ Σ₂) -> Σ₁ ≈ˢ-⟨ offset₁ eq , offset₂ eq ⟩ Σ₂
      forget : ∀ {Σ₁ Σ₂ n m} -> Σ₁ ≈ˢ-⟨ n , m ⟩ Σ₂ -> Σ₁ ≈ˢ Σ₂

  open NIˢ
