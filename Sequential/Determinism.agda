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

memberᴱ-≅ᵀ : ∀ {τ l π π₁ π₂} {Δ : Env l π} {t₁ : Term π₁ τ} {t₂ : Term π₂ τ} {τ∈π : τ ∈ π} -> τ∈π ↦ t₁ ∈ᴱ Δ -> τ∈π ↦ t₂ ∈ᴱ Δ -> t₁ ≅ᵀ t₂
memberᴱ-≅ᵀ here here = refl
memberᴱ-≅ᵀ (there a) (there b) with memberᴱ-≅ᵀ a b
memberᴱ-≅ᵀ (there a) (there b) | refl = refl

member-∈ : ∀ {l ls π} {Δ : Env l π} {Γ : Heap ls} -> l ↦ Δ ∈ᴴ Γ -> l ∈ ls
member-∈ here = here
member-∈ (there x) = there (member-∈ x)

update-∈ : ∀ {l ls π} {Δ : Env l π} {Γ Γ' : Heap ls} -> Γ' ≔ Γ [ l ↦ Δ ]ᴴ -> l ∈ ls
update-∈ here = here
update-∈ (there x) = there (update-∈ x)

memberᴴ-≡ : ∀ {l π₁ π₂ ls} {Γ : Heap ls} {Δ₁ : Env l π₁} {Δ₂ : Env l π₂} ->
            l ↦ Δ₁ ∈ᴴ Γ -> l ↦ Δ₂ ∈ᴴ Γ -> Δ₁ ≅ Δ₂
memberᴴ-≡ here here = refl
memberᴴ-≡ here (there {u = u} b) = ⊥-elim (∈-not-unique (member-∈ b) u)
memberᴴ-≡ (there {u = u} a) here = ⊥-elim (∈-not-unique (member-∈ a) u)
memberᴴ-≡ (there a) (there b) = memberᴴ-≡ a b

updateᴴ-≡ : ∀ {l ls π} {Γ Γ₁ Γ₂ : Heap ls} {Δ : Env l π} -> Γ₁ ≔ Γ [ l ↦ Δ ]ᴴ -> Γ₂ ≔ Γ [ l ↦ Δ ]ᴴ -> Γ₁ ≡ Γ₂
updateᴴ-≡ here here = refl
updateᴴ-≡ here (there {u = u} b) = ⊥-elim (∈-not-unique (update-∈ b) u)
updateᴴ-≡ (there {u = u} a) here = ⊥-elim (∈-not-unique (update-∈ a) u)
updateᴴ-≡ (there a) (there b) rewrite updateᴴ-≡ a b = refl

determinism : ∀ {ls l τ} {s₁ s₂ s₃ : State ls l τ} -> s₁ ⇝ s₂ -> s₁ ⇝ s₃ -> s₂ ≡ s₃
determinism (App₁ Δ∈Γ uᴴ) (App₁ Δ∈Γ₁ uᴴ₁) with memberᴴ-≡ Δ∈Γ Δ∈Γ₁
... | refl rewrite updateᴴ-≡ uᴴ uᴴ₁ = refl
determinism (App₁ Δ∈Γ uᴴ) (Var₂ Δ∈Γ₁ x∈π () uᴱ₁ uᴴ₁)
determinism (App₂ y∈π x∈π) (App₂ y∈π₁ .x∈π) = refl
determinism (Var₁ Δ∈Γ x∈π t∈Δ ¬val rᴱ uᴴ) (Var₁ Δ∈Γ₁ .x∈π t∈Δ₁ ¬val₁ rᴱ₁ uᴴ₁) with memberᴴ-≡ Δ∈Γ Δ∈Γ₁
... | refl with memberᴱ-≅ᵀ t∈Δ t∈Δ₁
... | refl rewrite updateᴱ-≡ rᴱ rᴱ₁ | updateᴴ-≡ uᴴ uᴴ₁ = refl
determinism (Var₁ Δ∈Γ x∈π t∈Δ ¬val rᴱ uᴴ) (Var₁' Δ∈Γ₁ .x∈π v∈Δ val) with memberᴴ-≡ Δ∈Γ Δ∈Γ₁
... | refl with memberᴱ-≅ᵀ t∈Δ v∈Δ
... | refl = ⊥-elim (¬val val)
determinism (Var₁ Δ∈Γ x∈π t∈Δ ¬val rᴱ uᴴ) (Var₂ Δ∈Γ₁ x∈π₁ () uᴱ uᴴ₁)
determinism (Var₁' Δ∈Γ x∈π v∈Δ val) (Var₁ Δ∈Γ₁ .x∈π t∈Δ ¬val rᴱ uᴴ) with memberᴴ-≡ Δ∈Γ Δ∈Γ₁
... | refl with memberᴱ-≅ᵀ t∈Δ v∈Δ
... | refl = ⊥-elim (¬val val)
determinism (Var₁' Δ∈Γ x∈π v∈Δ val) (Var₁' Δ∈Γ₁ .x∈π v∈Δ₁ val₁) with memberᴴ-≡ Δ∈Γ Δ∈Γ₁
... | refl with memberᴱ-≅ᵀ v∈Δ v∈Δ₁
... | refl = refl
determinism (Var₁' Δ∈Γ x∈π v∈Δ v) (Var₂ Δ∈Γ₁ x∈π₁ () uᴱ uᴴ)
determinism (Var₂ Δ∈Γ x∈π () uᴱ uᴴ) (App₁ Δ∈Γ₁ uᴴ₁)
determinism (Var₂ Δ∈Γ x∈π () uᴱ uᴴ) (Var₁ Δ∈Γ₁ x∈π₁ t∈Δ ¬val rᴱ uᴴ₁)
determinism (Var₂ Δ∈Γ x∈π () uᴱ uᴴ) (Var₁' Δ∈Γ₁ x∈π₁ v∈Δ val₁)
determinism (Var₂ Δ∈Γ x∈π val uᴱ uᴴ) (Var₂ Δ∈Γ₁ .x∈π val₁ uᴱ₁ uᴴ₁) with memberᴴ-≡ Δ∈Γ Δ∈Γ₁
... | refl rewrite updateᴱ-≡ uᴱ uᴱ₁ | updateᴴ-≡ uᴴ uᴴ₁ = refl
determinism (Var₂ Δ∈Γ x∈π () uᴱ uᴴ) If
determinism (Var₂ Δ∈Γ x∈π () uᴱ uᴴ) Return
determinism (Var₂ Δ∈Γ x∈π () uᴱ uᴴ) Bind₁
determinism (Var₂ Δ∈Γ x∈π () uᴱ uᴴ) (Label' p)
determinism (Var₂ Δ∈Γ x∈π () uᴱ uᴴ) (Label'∙ p)
determinism (Var₂ Δ∈Γ x∈π () uᴱ uᴴ) (Unlabel₁ p)
determinism (Var₂ Δ∈Γ x∈π () uᴱ uᴴ) (Unlabel∙₁ p)
determinism (Var₂ Δ∈Γ x∈π () uᴱ uᴴ) UnId₁
determinism (Var₂ Δ∈Γ x∈π () uᴱ uᴴ) (Fork p)
determinism If (Var₂ Δ∈Γ x∈π () uᴱ uᴴ)
determinism If If = refl
determinism IfTrue IfTrue = refl
determinism IfFalse IfFalse = refl
determinism Return (Var₂ Δ∈Γ x∈π () uᴱ uᴴ)
determinism Return Return = refl
determinism Bind₁ (Var₂ Δ∈Γ x∈π () uᴱ uᴴ)
determinism Bind₁ Bind₁ = refl
determinism Bind₂ Bind₂ = refl
determinism (Label' p) (Var₂ Δ∈Γ x∈π () uᴱ uᴴ)
determinism (Label' p) (Label' .p) = refl
determinism (Label'∙ p) (Var₂ Δ∈Γ x∈π () uᴱ uᴴ)
determinism (Label'∙ p) (Label'∙ .p) = refl
determinism (Unlabel₁ p) (Var₂ Δ∈Γ x∈π () uᴱ uᴴ)
determinism (Unlabel₁ p) (Unlabel₁ .p) = refl
determinism (Unlabel₂ p) (Unlabel₂ .p) = refl
determinism (Unlabel∙₁ p) (Var₂ Δ∈Γ x∈π () uᴱ uᴴ)
determinism (Unlabel∙₁ p) (Unlabel∙₁ .p) = refl
determinism (Unlabel∙₂ p) (Unlabel∙₂ .p) = refl
determinism UnId₁ (Var₂ Δ∈Γ x∈π () uᴱ uᴴ)
determinism UnId₁ UnId₁ = refl
determinism UnId₂ UnId₂ = refl
determinism (Fork p) (Var₂ Δ∈Γ x∈π () uᴱ uᴴ)
determinism (Fork p) (Fork .p) = refl
-- Morally they are the same, however the context π is chosen non deterministically
-- I wonder if this can be made to work using π = ∙ or if it is pushing it too much.
determinism Hole Hole = {!!} -- π₁ ≠ π₂
