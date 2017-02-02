{-# OPTIONS --rewriting #-}

module Sequential.Determinism where

open import Sequential.Calculus
open import Sequential.Semantics
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality

open import Types

updateᴱ-≡ : ∀ {π π' τ l} {mt : Maybe (Term π' τ)} {Δ Δ₁ Δ₂ : Env l π} {τ∈π : τ ∈⟨ l ⟩ π}
           -> Updateᴱ mt τ∈π Δ Δ₁ -> Updateᴱ mt τ∈π Δ Δ₂ -> Δ₁ ≡ Δ₂
updateᴱ-≡ here here = refl
updateᴱ-≡ (there a) (there b) rewrite updateᴱ-≡ a b = refl

-- My own heterogeneous equality for terms to ease unification
data _≅ᵀ_ {π τ} (t : Term π τ) : ∀ {π'} -> Term π' τ -> Set where
  refl : t ≅ᵀ t

memberᴱ-≅ᵀ : ∀ {τ l π π₁ π₂} {Δ : Env l π} {t₁ : Term π₁ τ} {t₂ : Term π₂ τ} (τ∈π : τ ∈⟨ l ⟩ᴿ π) -> τ∈π ↦ t₁ ∈ᴱ Δ -> τ∈π ↦ t₂ ∈ᴱ Δ -> t₁ ≅ᵀ t₂
memberᴱ-≅ᵀ τ∈π x y = aux x y
  where aux : ∀ {τ l π π₁ π₂} {Δ : Env l π} {t₁ : Term π₁ τ} {t₂ : Term π₂ τ} {τ∈π : τ ∈⟨ l ⟩ π}
                   -> Memberᴱ (just t₁) τ∈π Δ -> Memberᴱ (just t₂) τ∈π Δ -> t₁ ≅ᵀ t₂
        aux here here = refl
        aux (there x) (there y) with aux x y
        ... | refl = refl

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
determinism (Var₂ τ∈π () uᴱ) (New₁ ¬var)
determinism (Var₂ τ∈π () uᴱ) (New∙₁ ¬var)
determinism (Var₂ τ∈π () uᴱ) Write₁
determinism (Var₂ τ∈π () uᴱ) Write∙₁
determinism (Var₂ τ∈π () uᴱ) Read₁
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
determinism (New₁ ¬var) (Var₂ τ∈π () uᴱ)
determinism (New₁ ¬var) (New₁ ¬var₁) = refl
determinism (New∙₁ ¬var) (Var₂ τ∈π () uᴱ)
determinism (New∙₁ ¬var) (New∙₁ ¬var₁) = refl
determinism Write₁ (Var₂ τ∈π () uᴱ)
determinism Write₁ Write₁ = refl
determinism Write∙₁ (Var₂ τ∈π () uᴱ)
determinism Write∙₁ Write∙₁ = refl
determinism Read₁ (Var₂ τ∈π () uᴱ)
determinism Read₁ Read₁ = refl
determinism Hole₁ Hole₁ = refl
determinism Hole₂ Hole₂ = refl

memberᴴ-≅ : ∀ {l π₁ π₂ ls} {Γ : Heap ls} {x : Memory l × Env l π₁} {y : Memory l × Env l π₂} ->
            l ↦ x ∈ᴴ Γ -> l ↦ y ∈ᴴ Γ -> x ≅ y
memberᴴ-≅ here here = refl
memberᴴ-≅ here (there {u = u} b) = ⊥-elim (∈-not-unique (member-∈ b) u)
memberᴴ-≅ (there {u = u} a) here = ⊥-elim (∈-not-unique (member-∈ a) u)
memberᴴ-≅ (there a) (there b) = memberᴴ-≅ a b

updateᴴ-≡ : ∀ {l ls π} {Γ Γ₁ Γ₂ : Heap ls} {x : Memory l × Env l π} -> Γ₁ ≔ Γ [ l ↦ x ]ᴴ -> Γ₂ ≔ Γ [ l ↦ x ]ᴴ -> Γ₁ ≡ Γ₂
updateᴴ-≡ here here = refl
updateᴴ-≡ here (there {u = u} b) = ⊥-elim (∈-not-unique (update-∈ b) u)
updateᴴ-≡ (there {u = u} a) here = ⊥-elim (∈-not-unique (update-∈ a) u)
updateᴴ-≡ (there a) (there b) rewrite updateᴴ-≡ a b = refl

updateᴹ-≡ : ∀ {l n τ} {M₁ M₂ M₃ : Memory l} {c : Cell l τ} -> M₂ ≔ M₁ [ n ↦ c ]ᴹ -> M₃ ≔ M₁ [ n ↦ c ]ᴹ -> M₂ ≡ M₃
updateᴹ-≡ here here = refl
updateᴹ-≡ (there x) (there y) rewrite updateᴹ-≡ x y = refl

memberᴹ-≡ : ∀ {l n τ} {M : Memory l} {c₁ c₂ : Cell l τ} -> n ↦ c₁ ∈ᴹ M -> n ↦ c₂ ∈ᴹ M -> c₁ ≡ c₂
memberᴹ-≡ here here = refl
memberᴹ-≡ (there x) (there y) rewrite memberᴹ-≡ x y = refl

determinism⟼ : ∀ {l ls τ} {p₁ p₂ p₃ : Program l ls τ} -> p₁ ⟼ p₂ -> p₁ ⟼ p₃ -> p₂ ≡ p₃
determinism⟼ (Pure l∈Γ step uᴴ) (Pure l∈Γ₁ step₁ uᴴ₁) with memberᴴ-≅ l∈Γ l∈Γ₁
... | refl with determinism step step₁
... | refl rewrite updateᴴ-≡ uᴴ uᴴ₁ = refl
determinism⟼ (Pure l∈Γ (Var₂ τ∈π () uᴱ) uᴴ) (New H∈Γ uᴴ₁)
determinism⟼ (Pure l∈Γ (New₁ ¬var) uᴴ) (New H∈Γ uᴴ₁) = ⊥-elim (¬var (Var ⟪ _ ⟫))
determinism⟼ (Pure l∈Γ (Var₂ τ∈π () uᴱ) uᴴ) New∙
determinism⟼ (Pure l∈Γ (New∙₁ ¬var) uᴴ) New∙ = ⊥-elim (¬var (Var ⟪ _ ⟫))
determinism⟼ (Pure l∈Γ () uᴴ) (Write₂ H∈Γ uᴹ uᴴ₁)
determinism⟼ (Pure l∈Γ () uᴴ) (Writeᴰ₂ H∈Γ uᴹ uᴴ₁)
determinism⟼ (Pure l∈Γ () uᴴ) Write∙₂
determinism⟼ (Pure l∈Γ () uᴴ) (Read₂ l∈Γ₁ n∈M)
determinism⟼ (Pure l∈Γ () uᴴ) (Readᴰ₂ L∈Γ t∈M)
determinism⟼ (Pure l∈Γ (Var₂ τ∈π () uᴱ) uᴴ) (DeepDupˢ L⊏l L∈Γ t∈Δ)
determinism⟼ (Pure l∈Γ (DeepDup ._ t∈Δ) uᴴ) (DeepDupˢ (L⊑l , L≢l) L∈Γ t∈Δ₁) = ⊥-elim (L≢l refl)
determinism⟼ (Pure l∈Γ (DeepDup' ¬var) uᴴ) (DeepDupˢ L⊏l L∈Γ t∈Δ) = ⊥-elim (¬var (Var ⟪ _ ⟫))
determinism⟼ (New H∈Γ uᴴ) (Pure l∈Γ (Var₂ τ∈π () uᴱ) uᴴ₁)
determinism⟼ (New H∈Γ uᴴ) (Pure l∈Γ (New₁ ¬var) uᴴ₁) = ⊥-elim (¬var (Var ⟪ _ ⟫))
determinism⟼ (New H∈Γ uᴴ) (New H∈Γ₁ uᴴ₁) with memberᴴ-≅ H∈Γ H∈Γ₁
... | refl rewrite updateᴴ-≡ uᴴ uᴴ₁ = refl
determinism⟼ New∙ (Pure l∈Γ (Var₂ τ∈π () uᴱ) uᴴ)
determinism⟼ New∙ (Pure l∈Γ (New∙₁ ¬var) uᴴ) = ⊥-elim (¬var (Var ⟪ _ ⟫))
determinism⟼ New∙ New∙ = refl
determinism⟼ (Write₂ H∈Γ uᴹ uᴴ) (Pure l∈Γ () uᴴ₁)
determinism⟼ (Write₂ H∈Γ uᴹ uᴴ) (Write₂ H∈Γ₁ uᴹ₁ uᴴ₁) with memberᴴ-≅ H∈Γ H∈Γ₁
... | refl rewrite updateᴹ-≡ uᴹ uᴹ₁ | updateᴴ-≡ uᴴ uᴴ₁ = refl
determinism⟼ (Writeᴰ₂ H∈Γ uᴹ uᴴ) (Pure l∈Γ () uᴴ₁)
determinism⟼ (Writeᴰ₂ H∈Γ uᴹ uᴴ) (Writeᴰ₂ H∈Γ₁ uᴹ₁ uᴴ₁) with memberᴴ-≅ H∈Γ H∈Γ₁
... | refl rewrite updateᴹ-≡ uᴹ uᴹ₁ | updateᴴ-≡ uᴴ uᴴ₁ = refl
determinism⟼ Write∙₂ (Pure l∈Γ () uᴴ)
determinism⟼ Write∙₂ Write∙₂ = refl
determinism⟼ (Read₂ l∈Γ n∈M) (Pure l∈Γ₁ () uᴴ)
determinism⟼ (Read₂ l∈Γ n∈M) (Read₂ l∈Γ₁ n∈M₁) with memberᴴ-≅ l∈Γ l∈Γ₁
... | refl with memberᴹ-≡ n∈M n∈M₁
... | refl = refl
determinism⟼ (Readᴰ₂ L∈Γ t∈M) (Pure l∈Γ () uᴴ)
determinism⟼ (Readᴰ₂ L∈Γ n∈M) (Readᴰ₂ L∈Γ₁ n∈M₁) with memberᴴ-≅ L∈Γ L∈Γ₁
... | refl with memberᴹ-≡ n∈M n∈M₁
... | refl = refl
determinism⟼ (DeepDupˢ L⊏l L∈Γ t∈Δ) (Pure l∈Γ (Var₂ τ∈π () uᴱ) uᴴ)
determinism⟼ (DeepDupˢ (L⊑l , L≢l) L∈Γ t∈Δ) (Pure l∈Γ (DeepDup ._ t∈Δ₁) uᴴ) = ⊥-elim (L≢l refl)
determinism⟼ (DeepDupˢ L⊏l L∈Γ t∈Δ) (Pure l∈Γ (DeepDup' ¬var) uᴴ) = ⊥-elim (¬var (Var ⟪ _ ⟫))
determinism⟼ (DeepDupˢ {τ∈π = τ∈π} L⊏l L∈Γ t∈Δ) (DeepDupˢ L⊏l' L∈Γ₁ t∈Δ₁) with memberᴴ-≅ L∈Γ L∈Γ₁
... | refl with memberᴱ-≅ᵀ τ∈π t∈Δ t∈Δ₁
... | refl = refl
determinism⟼ Hole Hole = refl
