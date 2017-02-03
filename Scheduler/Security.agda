open import Lattice using (Lattice ; Label)
import Scheduler.Base as S

module Scheduler.Security (𝓛 : Lattice) (A : Label 𝓛) (𝓢 : S.Scheduler 𝓛) where

  open import Scheduler.Base 𝓛
  open Lattice.Lattice 𝓛
  open Scheduler 𝓢 public

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
  ε₁ᴹ : ∀ {l} -> Dec (l ⊑ A) -> Message l -> Message l
  ε₁ᴹ (yes p) (l , n , e) = l , n , εᴱ e
  ε₁ᴹ (no ¬p) (l , n , e) = l , n , ∙

  εᴹ : ∀ {l} -> Message l -> Message l
  εᴹ = ε₁ᴹ (_ ⊑? A)


  record NI-Sch : Set₁ where
    constructor Sec
    field
      εˢ  : State -> State
      _≈ˢ_ : State -> State -> Set  -- I expect this to be equivalent to the kerner of the erasure function, i.e. s₁ ≈ˢ s₂ ⇔ εˢ s₁ ≡ εˢ s₂

      ε-sch-dist : ∀ {s₁ s₂ : State} {l} {m : Message l} ->  s₁ ⟶ s₂ ↑ m -> (εˢ s₁) ⟶ (εˢ s₂) ↑ (εᴹ m)
      ε-sch-≡ : ∀ {s₁ s₂ l} {m : Message l} -> l ⋤ A -> s₁ ⟶ s₂ ↑ m -> s₁ ≈ˢ s₂
      determinismˢ : ∀ {l n e} {s₁ s₂ s₃ : State} -> s₁ ⟶ s₂ ↑ (l , n , e) -> s₁ ⟶ s₃ ↑ (l , n , e) -> s₂ ≡ s₃

      -- Annotated low-equivalence
      _≈ˢ-⟨_,_⟩_ : State -> ℕ -> ℕ -> State -> Set
      offset₁ : {s₁ s₂ : State} -> s₁ ≈ˢ s₂ -> ℕ
      offset₂ : {s₁ s₂ : State} -> s₁ ≈ˢ s₂ -> ℕ
      align : ∀ {s₁ s₂} -> (eq : s₁ ≈ˢ s₂) -> s₁ ≈ˢ-⟨ offset₁ eq , offset₂ eq ⟩ s₂
      forget : ∀ {s₁ s₂ n m} -> s₁ ≈ˢ-⟨ n , m ⟩ s₂ -> s₁ ≈ˢ s₂
