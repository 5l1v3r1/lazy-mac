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

  -- Low-equivalence for events
  -- To prove that it corresponds to εᴹ, we need to extend ℕ with • and use it to
  -- overwrite the id of high threads forked from low contexts
  data _≈ᴱ⟨_⟩_ {l} : Event l -> Dec (l ⊑ A) -> Event l -> Set where
    Step : ∀ {l⊑A : l ⊑ A} -> Step ≈ᴱ⟨ yes l⊑A ⟩ Step
    Skip : ∀ {l⊑A : l ⊑ A} -> Skip ≈ᴱ⟨ yes l⊑A ⟩ Skip
    Done : ∀ {l⊑A : l ⊑ A} -> Done ≈ᴱ⟨ yes l⊑A ⟩ Done
    Forkᴸ : ∀ {h n} {l⊑A : l ⊑ A} {l⊑h : l ⊑ h} -> (h⊑A : h ⊑ A) -> Fork h n l⊑h ≈ᴱ⟨ yes l⊑A ⟩ Fork h n l⊑h
    Forkᴴ : ∀ {h n₁ n₂} {l⊑A : l ⊑ A} {l⊑h : l ⊑ h} -> (h⋤A : h ⋤ A) -> Fork h n₁ l⊑h ≈ᴱ⟨ yes l⊑A ⟩ Fork h n₂ l⊑h
    ∙ : ∀ {e₁ e₂ : Event l} {l⋤A : l ⋤ A} -> e₁ ≈ᴱ⟨ no l⋤A ⟩ e₂

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

      -- Starvation-free
      triangleˢ : ∀ {L H n m i j e e' Σ₁ Σ₂ Σ₁' Σ₂'}  -> L ⊑ A -> Σ₁ ≈ˢ-⟨ i , suc j ⟩ Σ₂ ->
                   Σ₁ ⟶ Σ₁' ↑ ⟪ L , n , e ⟫ -> Σ₂ ⟶ Σ₂' ↑ ⟪ H , m , e' ⟫ -> (H ⋤ A) × (Σ₁ ≈ˢ-⟨ i , j ⟩ Σ₂')

      -- Splitting square and triangle in two separate lemmas for convenience
      redex-≈ˢ : ∀ {L i n e₁ e₂ Σ₁ Σ₂ Σ₁'} -> (L⊑A : L ⊑ A) -> Σ₁ ⟶ Σ₁' ↑ ⟪ L , n , e₁ ⟫ -> Σ₁ ≈ˢ-⟨ i , 0 ⟩ Σ₂ ->
                      e₁ ≈ᴱ⟨ yes L⊑A ⟩ e₂ -> ∃ (λ Σ₂' → Σ₂ ⟶ Σ₂' ↑ ⟪ L , n , e₂ ⟫)

      redex-≈▵ˢ : ∀ {Σ₁ Σ₁' Σ₂ L e n n₁ n₂} -> L ⊑ A -> Σ₁ ≈ˢ-⟨ n₁ , suc n₂ ⟩ Σ₂ -> Σ₁ ⟶ Σ₁' ↑ ⟪ L , n , e ⟫ ->
                  ∃ (λ x → ∀ (e : Event _) → ∃ (λ Σ₂' →  Σ₂ ⟶ Σ₂' ↑ ⟪ proj₁ x , proj₂ x , e ⟫ ))


    refl-≈ˢ : ∀ {Σ} -> Σ ≈ˢ Σ
    refl-≈ˢ = ⌜ refl ⌝

    sym-≈ˢ : ∀ {Σ₁ Σ₂} -> Σ₁ ≈ˢ Σ₂ -> Σ₂ ≈ˢ Σ₁
    sym-≈ˢ x = ⌜ sym (⌞ x ⌟) ⌝

    trans-≈ˢ : ∀ {Σ₁ Σ₂ Σ₃} -> Σ₁ ≈ˢ Σ₂ -> Σ₂ ≈ˢ Σ₃ -> Σ₁ ≈ˢ Σ₃
    trans-≈ˢ x y = ⌜ trans (⌞ x ⌟) (⌞ y ⌟) ⌝

  open NIˢ
