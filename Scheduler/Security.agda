open import Lattice using (Lattice ; Label)
import Scheduler.Base as S

module Scheduler.Security (𝓛 : Lattice) (A : Label 𝓛) where

  open import Scheduler.Base 𝓛
  open Lattice.Lattice 𝓛

  open import Data.Nat
  open import Data.Product
  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality

  -- Erasure of labeled events
  εᴱ : ∀ {l} -> Event l -> Event l
  εᴱ (Fork h n p) with h ⊑? A
  εᴱ (Fork h n p) | yes _ = Fork h n p
  εᴱ (Fork h n p) | no ¬p = Step
  εᴱ e = e

  -- Erasure of labeled messages
  εᴹ : ∀ {l} -> Message l -> Message l
  εᴹ ⟪ l , n , e ⟫ = ⟪ l , n , εᴱ e ⟫


  record NIˢ (𝓢 : S.Scheduler 𝓛) : Set₁ where
    open Scheduler 𝓢 public
    field
      εˢ  : State -> State
      _≈ˢ_ : State -> State -> Set

      ⌞_⌟ : ∀ {Σ₁ Σ₂} -> Σ₁ ≈ˢ Σ₂ -> εˢ Σ₁ ≡ εˢ Σ₂
      ⌜_⌝ : ∀ {Σ₁ Σ₂} -> εˢ Σ₁ ≡ εˢ Σ₂ -> Σ₁ ≈ˢ Σ₂

      εˢ-simᴸ : ∀ {Σ₁ Σ₂ : State} {l} {m : Message l} -> (l⊑A : l ⊑ A) -> Σ₁ ⟶ Σ₂ ↑ m -> (εˢ Σ₁) ⟶ (εˢ Σ₂) ↑ (εᴹ m)
      εˢ-simᴴ : ∀ {Σ₁ Σ₂ l} {m : Message l} -> l ⋤ A -> Σ₁ ⟶ Σ₂ ↑ m -> Σ₁ ≈ˢ Σ₂

      -- Annotated low-equivalence
      _≈ˢ-⟨_,_⟩_ : State -> ℕ -> ℕ -> State -> Set
      offset₁ : {Σ₁ Σ₂ : State} -> Σ₁ ≈ˢ Σ₂ -> ℕ
      offset₂ : {Σ₁ Σ₂ : State} -> Σ₁ ≈ˢ Σ₂ -> ℕ
      align : ∀ {Σ₁ Σ₂} -> (eq : Σ₁ ≈ˢ Σ₂) -> Σ₁ ≈ˢ-⟨ offset₁ eq , offset₂ eq ⟩ Σ₂
      forget : ∀ {Σ₁ Σ₂ n m} -> Σ₁ ≈ˢ-⟨ n , m ⟩ Σ₂ -> Σ₁ ≈ˢ Σ₂

      -- The Thread Id in a fork should not affect the state
      id-≈ˢ : ∀ {Σ₁ Σ₂ L m₁ n H} -> (m₂ : ℕ) (L⊑H : L ⊑ H) -> L ⊑ A -> H ⋤ A -> Σ₁ ⟶ Σ₂ ↑ S.⟪ L , n , (Fork H m₁ L⊑H) ⟫
              -> ∃ (λ Σ₂' → Σ₁ ⟶ Σ₂' ↑ S.⟪ L , n , (Fork H m₂ L⊑H) ⟫ × Σ₂ ≈ˢ Σ₂')

      -- Forking a high thread should be (low) equivalent as non forking
      step-≈ˢ : ∀ {Σ₁ Σ₂ L H n m} -> (L⊑H : L ⊑ H) -> L ⊑ A -> H ⋤ A -> Σ₁ ⟶ Σ₂ ↑ ⟪ L , n , Fork H m L⊑H ⟫
              -> ∃ (λ Σ₂' → Σ₁ ⟶ Σ₂' ↑ S.⟪ L , n , Step ⟫ × Σ₂ ≈ˢ Σ₂')

      -- The converse property, at any time you if you step I should be able to fork a high thread
      fork-≈ˢ : ∀ {Σ₁ Σ₂ L H n} -> (m : ℕ) (L⊑H : L ⊑ H) -> L ⊑ A -> H ⋤ A -> Σ₁ ⟶ Σ₂ ↑ ⟪ L , n , Step ⟫
              -> ∃ (λ Σ₂' → Σ₁ ⟶ Σ₂' ↑ S.⟪ L , n , Fork H m L⊑H ⟫ × Σ₂ ≈ˢ Σ₂')


      -- Starvation-free
      squareˢ : ∀ {Σ₁ Σ₁' Σ₂ L e n n₁} -> L ⊑ A -> Σ₁ ≈ˢ-⟨ n₁ , 0 ⟩ Σ₂ -> Σ₁ ⟶ Σ₁' ↑ ⟪ L , n , e ⟫ ->
            ∃ (λ Σ₂' → Σ₂ ⟶ Σ₂' ↑ ⟪ L , n , e ⟫ × Σ₁' ≈ˢ Σ₂')

    refl-≈ˢ : ∀ {Σ} -> Σ ≈ˢ Σ
    refl-≈ˢ = ⌜ refl ⌝

    sym-≈ˢ : ∀ {Σ₁ Σ₂} -> Σ₁ ≈ˢ Σ₂ -> Σ₂ ≈ˢ Σ₁
    sym-≈ˢ x = ⌜ sym (⌞ x ⌟) ⌝

    trans-≈ˢ : ∀ {Σ₁ Σ₂ Σ₃} -> Σ₁ ≈ˢ Σ₂ -> Σ₂ ≈ˢ Σ₃ -> Σ₁ ≈ˢ Σ₃
    trans-≈ˢ x y = ⌜ trans (⌞ x ⌟) (⌞ y ⌟) ⌝

  open NIˢ
