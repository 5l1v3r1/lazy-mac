import Lattice as L

module Sequential.PINI (𝓛 : L.Lattice) (A : L.Label 𝓛) where

open import Types 𝓛
open import Sequential.Calculus 𝓛
open import Sequential.Semantics 𝓛
open import Sequential.Determinism 𝓛
open import Sequential.Erasure 𝓛 A

open import Relation.Binary.PropositionalEquality

data _≈ᴾ_ {l ls τ} (p₁ p₂ : Program l ls τ) : Set where
  ε-refl : εᴾ p₁ ≡ εᴾ p₂ -> p₁ ≈ᴾ p₂

pini : ∀ {l ls τ} {p₁ p₁' p₂ p₂' : Program l ls τ} -> p₁ ≈ᴾ p₂ -> p₁ ⟼ p₁' -> p₂ ⟼ p₂' -> p₁' ≈ᴾ p₂'
pini (ε-refl eq) s₁ s₂ = ε-refl (aux eq (εᴾ-sim s₁) (εᴾ-sim s₂))
  where aux : ∀ {l ls τ} {p₁ p₁' p₂ p₂' : Program l ls τ} -> p₁ ≡ p₂ -> p₁ ⟼ p₁' -> p₂ ⟼ p₂' -> p₁' ≡ p₂'
        aux refl x y = determinismᴾ x y

-- TODO move to PINI ?
data _≈ᴴ_ {ls} (Γ₁ Γ₂ : Heap ls) : Set where
  εᴴ-refl : εᴴ Γ₁ ≡ εᴴ Γ₂ -> Γ₁ ≈ᴴ Γ₂

data _≈ˢ_ {l τ₁ τ₂} (S₁ S₂ : Stack l τ₁ τ₂) : Set where
  εˢ-refl : εˢ S₁ ≡ εˢ S₂ -> S₁ ≈ˢ S₂

data _≈ᵀ_ {π τ} (t₁ t₂ : Term π τ) : Set where
  εᵀ-refl : εᵀ t₁ ≡ εᵀ t₂ -> t₁ ≈ᵀ t₂


-- Structural Low-equivalence
data _⋍ᴾ_  {l ls τ} : (p₁ p₂ : Program l ls τ) -> Set where
  ∙ : ∙ ⋍ᴾ ∙
  ⟨_,_,_⟩ : ∀ {π τ' Γ₁ Γ₂ S₁ S₂} {t₁ t₂ : Term π τ'} -> Γ₁ ≈ᴴ Γ₂ -> t₁ ≈ᵀ t₂ -> S₁ ≈ˢ S₂ -> ⟨ Γ₁ , t₁ , S₁ ⟩ ⋍ᴾ ⟨ Γ₂ , t₂ , S₂ ⟩

open import Relation.Nullary

⋍ᴾ-≈ᴾ : ∀ {l ls τ} {p₁ p₂ : Program l ls τ} -> p₁ ⋍ᴾ p₂ -> p₁ ≈ᴾ p₂
⋍ᴾ-≈ᴾ ∙ = ε-refl refl
⋍ᴾ-≈ᴾ {l} ⟨ x , y , z ⟩ = ε-refl (aux (_ ⊑? A) x y z)
  where aux : ∀ {π τ τ' ls l} {Γ₁ Γ₂ : Heap ls} {S₁ S₂ : Stack l τ' τ} {t₁ t₂ : Term π τ'} ->
                  (x : Dec (l ⊑ A)) -> Γ₁ ≈ᴴ Γ₂ -> t₁ ≈ᵀ t₂ -> S₁ ≈ˢ S₂ -> (ε₁ᴾ x ⟨ Γ₁ , t₁ , S₁ ⟩) ≡ (ε₁ᴾ x ⟨ Γ₂ , t₂ , S₂ ⟩)
        aux (yes p) (εᴴ-refl eq₁) (εᵀ-refl eq₂) (εˢ-refl eq₃) rewrite eq₁ | eq₂ | eq₃ = refl
        aux (no ¬p) eq₃ eq₄ eq₅ = refl

-- TODO we must use heterogeneous equality because in a single step the type and context of terms may change

≈ᴾ-⋍ᴾ : ∀ {l ls τ} {p₁ p₂ : Program l ls τ} -> p₁ ≈ᴾ p₂ -> p₁ ⋍ᴾ p₂
≈ᴾ-⋍ᴾ = {!!}
-- ≈ᴾ-⋍ᴾ {p₁ = ⟨ Γ , t , S ⟩} {⟨ Γ₁ , t₁ , S₁ ⟩} (ε-refl x) with εᴾ ⟨ Γ , t , S ⟩ | εᴾ ⟨ Γ₁ , t₁ , S₁ ⟩
-- ≈ᴾ-⋍ᴾ {l} {ls} {τ} {⟨ Γ , t , S ⟩} {⟨ Γ₁ , t₁ , S₁ ⟩} (ε-refl refl) | a | .a = {!⟨_,_,_⟩ ? ? ?!}
-- ≈ᴾ-⋍ᴾ {p₁ = ⟨ Γ , t , S ⟩} {∙} (ε-refl x) = {!!}
-- ≈ᴾ-⋍ᴾ {p₁ = ∙} {⟨ Γ , t , S ⟩} (ε-refl x) = {!!}
-- ≈ᴾ-⋍ᴾ {p₁ = ∙} {∙} (ε-refl refl) = ∙

stepᴴ : ∀ {H ls τ} {p₁ p₂ : Program H ls τ} -> H ⋤ A -> p₁ ⟼ p₂ -> p₁ ⋍ᴾ p₂
stepᴴ H⋤A (Pure l∈Γ step uᴴ) = {! ⟨ ? , ? , ? ⟩!}
stepᴴ H⋤A (New H∈Γ uᴴ) = {!!}
stepᴴ H⋤A New∙ = {!!}
stepᴴ H⋤A (Write₂ H∈Γ uᴹ uᴴ) = {!!}
stepᴴ H⋤A (Writeᴰ₂ H∈Γ uᴹ uᴴ) = {!!}
stepᴴ H⋤A Write∙₂ = {!!}
stepᴴ H⋤A (Read₂ l∈Γ n∈M) = {!!}
stepᴴ H⋤A (Readᴰ₂ L∈Γ n∈M) = {!!}
stepᴴ H⋤A (DeepDupˢ L⊏l L∈Γ t∈Δ) = {!!}
stepᴴ H⋤A Hole = ∙
