{-# OPTIONS --rewriting #-}

module Sequential.Determinism where

open import Sequential.Calculus
open import Sequential.Semantics
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality

open import Types

updateᴱ-≡ : ∀ {π π' τ l} {mt : Maybe (Term π' τ)} {Δ Δ₁ Δ₂ : Env l π} {τ∈π : τ ∈ π}
           -> Updateᴱ mt τ∈π Δ Δ₁ -> Updateᴱ mt τ∈π Δ Δ₂ -> Δ₁ ≡ Δ₂
updateᴱ-≡ here here = refl
updateᴱ-≡ (there a) (there b) rewrite updateᴱ-≡ a b = refl
updateᴱ-≡ ∙ ∙ = refl

-- My own heterogeneous equality for terms to ease unification
data _≅ᵀ_ {π τ} (t : Term π τ) : ∀ {π'} -> Term π' τ -> Set where
  refl : t ≅ᵀ t

memberᴱ-≅ᵀ : ∀ {τ l π π₁ π₂} {Δ : Env l π} {t₁ : Term π₁ τ} {t₂ : Term π₂ τ} (τ∈π : τ ∈ᴿ π) -> τ∈π ↦ t₁ ∈ᴱ Δ -> τ∈π ↦ t₂ ∈ᴱ Δ -> t₁ ≅ᵀ t₂
memberᴱ-≅ᵀ τ∈π x y = aux x y
  where aux : ∀ {τ l π π₁ π₂} {Δ : Env l π} {t₁ : Term π₁ τ} {t₂ : Term π₂ τ} {τ∈π : τ ∈ π}
                   -> Memberᴱ (just t₁) τ∈π Δ -> Memberᴱ (just t₂) τ∈π Δ -> t₁ ≅ᵀ t₂
        aux here here = refl
        aux (there x) (there y) with aux x y
        ... | refl = refl

-- member-∈ : ∀ {l ls π} {Δ : Env l π} {Γ : Heap ls} -> l ↦ Δ ∈ᴴ Γ -> l ∈ ls
-- member-∈ here = here
-- member-∈ (there x) = there (member-∈ x)

-- update-∈ : ∀ {l ls π} {Δ : Env l π} {Γ Γ' : Heap ls} -> Γ' ≔ Γ [ l ↦ Δ ]ᴴ -> l ∈ ls
-- update-∈ here = here
-- update-∈ (there x) = there (update-∈ x)

-- memberᴴ-≅ : ∀ {l π₁ π₂ ls} {Γ : Heap ls} {Δ₁ : Env l π₁} {Δ₂ : Env l π₂} ->
--             l ↦ Δ₁ ∈ᴴ Γ -> l ↦ Δ₂ ∈ᴴ Γ -> Δ₁ ≅ Δ₂
-- memberᴴ-≅ here here = refl
-- memberᴴ-≅ here (there {u = u} b) = ⊥-elim (∈-not-unique (member-∈ b) u)
-- memberᴴ-≅ (there {u = u} a) here = ⊥-elim (∈-not-unique (member-∈ a) u)
-- memberᴴ-≅ (there a) (there b) = memberᴴ-≅ a b

-- updateᴴ-≡ : ∀ {l ls π} {Γ Γ₁ Γ₂ : Heap ls} {Δ : Env l π} -> Γ₁ ≔ Γ [ l ↦ Δ ]ᴴ -> Γ₂ ≔ Γ [ l ↦ Δ ]ᴴ -> Γ₁ ≡ Γ₂
-- updateᴴ-≡ here here = refl
-- updateᴴ-≡ here (there {u = u} b) = ⊥-elim (∈-not-unique (update-∈ b) u)
-- updateᴴ-≡ (there {u = u} a) here = ⊥-elim (∈-not-unique (update-∈ a) u)
-- updateᴴ-≡ (there a) (there b) rewrite updateᴴ-≡ a b = refl

determinism : ∀ {l τ} {s₁ s₂ s₃ : State l τ} -> s₁ ⇝ s₂ -> s₁ ⇝ s₃ -> s₂ ≡ s₃
determinism App₁ App₁ = refl
determinism App₁ (Var₂ τ∈π () uᴱ)
determinism (App₂ α∈π) (App₂ .α∈π) = refl
determinism (Var₁ τ∈π t∈Δ ¬val rᴱ) (Var₁ .τ∈π t∈Δ₁ ¬val₁ rᴱ₁) with memberᴱ-≅ᵀ τ∈π t∈Δ t∈Δ₁
... | refl rewrite updateᴱ-≡ rᴱ rᴱ₁ = refl
determinism (Var₁ τ∈π t∈Δ ¬val rᴱ) (Var₁' .τ∈π v∈Δ val) with memberᴱ-≅ᵀ τ∈π t∈Δ v∈Δ
... | refl = ⊥-elim (¬val val)
determinism (Var₁ τ∈π t∈Δ ¬val rᴱ) (Var₂ τ∈π₁ () uᴱ)
determinism (Var₁' τ∈π v∈Δ val) (Var₁ .τ∈π t∈Δ ¬val rᴱ) with memberᴱ-≅ᵀ τ∈π t∈Δ v∈Δ
... | refl = ⊥-elim (¬val val)
determinism (Var₁' τ∈π v∈Δ val) (Var₁' .τ∈π v∈Δ₁ val₁) with memberᴱ-≅ᵀ τ∈π v∈Δ v∈Δ₁
... | refl = refl
determinism (Var₁' τ∈π v∈Δ val) (Var₂ τ∈π₁ () uᴱ)
determinism (Var₂ τ∈π () uᴱ) App₁
determinism (Var₂ τ∈π () uᴱ) (Var₁ τ∈π₁ t∈Δ ¬val rᴱ)
determinism (Var₂ τ∈π () uᴱ) (Var₁' τ∈π₁ v∈Δ val₁)
determinism (Var₂ τ∈π val uᴱ) (Var₂ .τ∈π val₁ uᴱ₁) rewrite updateᴱ-≡ uᴱ uᴱ₁ = refl
determinism (Var₂ τ∈π () uᴱ) If
determinism (Var₂ τ∈π () uᴱ) Return
determinism (Var₂ τ∈π () uᴱ) Bind₁
determinism (Var₂ τ∈π () uᴱ) (Label' p)
determinism (Var₂ τ∈π () uᴱ) (Label'∙ p)
determinism (Var₂ τ∈π () uᴱ) (Unlabel₁ p)
determinism (Var₂ τ∈π () uᴱ) UnId₁
determinism (Var₂ τ∈π () uᴱ) (Fork p)
determinism (Var₂ τ∈π () uᴱ) (DeepDup τ∈π' t∈Δ)
determinism (Var₂ τ∈π () uᴱ) (DeepDup' ¬var)
determinism If (Var₂ τ∈π () uᴱ)
determinism If If = refl
determinism IfTrue IfTrue = refl
determinism IfFalse IfFalse = refl
determinism Return (Var₂ τ∈π () uᴱ)
determinism Return Return = refl
determinism Bind₁ (Var₂ τ∈π () uᴱ)
determinism Bind₁ Bind₁ = refl
determinism Bind₂ Bind₂ = refl
determinism (Label' p) (Var₂ τ∈π () uᴱ)
determinism (Label' p) (Label' .p) = refl
determinism (Label'∙ p) (Var₂ τ∈π () uᴱ)
determinism (Label'∙ p) (Label'∙ .p) = refl
determinism (Unlabel₁ p) (Var₂ τ∈π () uᴱ)
determinism (Unlabel₁ p) (Unlabel₁ .p) = refl
determinism (Unlabel₂ p) (Unlabel₂ .p) = refl
determinism UnId₁ (Var₂ τ∈π () uᴱ)
determinism UnId₁ UnId₁ = refl
determinism UnId₂ UnId₂ = refl
determinism (Fork p) (Var₂ τ∈π () uᴱ)
determinism (Fork p) (Fork .p) = refl
determinism (DeepDup τ∈π t∈Δ) (DeepDup .τ∈π t∈Δ₁) with memberᴱ-≅ᵀ τ∈π t∈Δ t∈Δ₁
... | refl = refl
determinism (DeepDup τ∈π t∈Δ) (DeepDup' ¬var) = ⊥-elim (¬var (Var τ∈π))
determinism (DeepDup τ∈π t∈Δ) (Var₂ _ () _)
determinism (DeepDup' ¬var) (DeepDup' ¬var') = refl
determinism (DeepDup' ¬var) (Var₂ τ∈π () _)
determinism (DeepDup' ¬var) (DeepDup τ∈π t∈Δ) = ⊥-elim (¬var (Var _))
determinism Hole Hole = refl
