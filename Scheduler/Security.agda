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

      εˢ-simᴸ : ∀ {s₁ s₂ : State} {l} {m : Message l} -> (l⊑A : l ⊑ A) -> s₁ ⟶ s₂ ↑ m -> (εˢ s₁) ⟶ (εˢ s₂) ↑ (εᴹ (yes l⊑A) m)
      εˢ-simᴴ : ∀ {s₁ s₂ l} {m : Message l} -> l ⋤ A -> s₁ ⟶ s₂ ↑ m -> s₁ ≈ˢ s₂

      -- Annotated low-equivalence
      _≈ˢ-⟨_,_⟩_ : State -> ℕ -> ℕ -> State -> Set
      offset₁ : {s₁ s₂ : State} -> s₁ ≈ˢ s₂ -> ℕ
      offset₂ : {s₁ s₂ : State} -> s₁ ≈ˢ s₂ -> ℕ
      align : ∀ {s₁ s₂} -> (eq : s₁ ≈ˢ s₂) -> s₁ ≈ˢ-⟨ offset₁ eq , offset₂ eq ⟩ s₂
      forget : ∀ {s₁ s₂ n m} -> s₁ ≈ˢ-⟨ n , m ⟩ s₂ -> s₁ ≈ˢ s₂

  open NIˢ
