module Sequential.Determinism where

open import Sequential.Calculus
open import Sequential.Semantics
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

open import Types

-- not# : ∀ {τ₁ τ₂} -> Cont τ₁ τ₂ -> Set
-- not# (# x∈π) = ⊥
-- not# c = ⊤

-- notStack# : ∀ {τ τ' l} -> Stack l τ τ' -> Set
-- notStack# [] = ⊤
-- notStack# (c ∷ S) = not# c
-- notStack# ∙ = ⊤

-- redexNotVal : ∀ {Γ τ τ' l n} {π : Context n} {S : Stack l τ τ'} {t : Term π τ} {s₂} -> {{¬# : notStack# S}} -> ⟨ Γ , t , S ⟩ ⇝ s₂ -> ¬ (Value t)
-- redexNotVal = {!!}

determinism : ∀ {l τ} {s₁ s₂ s₃ : State l τ} -> s₁ ⇝ s₂ -> s₁ ⇝ s₃ -> s₂ ≡ s₃
determinism (App₁ M∈Γ) (App₁ M∈Γ₁) = ?
determinism (App₁ M∈Γ) (Var₂ M∈Γ₁ x∈π val) = ?
determinism (App₂ y∈π x∈π) (App₂ y∈π₁ .x∈π) = ?
determinism (Var₁ M∈Γ x∈π t∈M ¬val) (Var₁ M∈Γ₁ .x∈π t∈M₁ ¬val₁) = ?
determinism (Var₁ M∈Γ x∈π t∈M ¬val) (Var₁' M∈Γ₁ .x∈π v∈M val) = ?
determinism (Var₁ M∈Γ x∈π t∈M ¬val) (Var₂ M∈Γ₁ x∈π₁ val) = ?
determinism (Var₁' M∈Γ x∈π v∈M val) (Var₁ M∈Γ₁ .x∈π t∈M ¬val) = ?
determinism (Var₁' M∈Γ x∈π v∈M val) (Var₁' M∈Γ₁ .x∈π v∈M₁ val₁) = ?
determinism (Var₁' M∈Γ x∈π v∈M val) (Var₂ M∈Γ₁ x∈π₁ val₁) = ?
determinism (Var₂ M∈Γ x∈π val) (App₁ M∈Γ₁) = ?
determinism (Var₂ M∈Γ x∈π val) (Var₁ M∈Γ₁ x∈π₁ t∈M ¬val) = ?
determinism (Var₂ M∈Γ x∈π val) (Var₁' M∈Γ₁ x∈π₁ v∈M val₁) = ?
determinism (Var₂ M∈Γ x∈π val) (Var₂ M∈Γ₁ .x∈π val₁) = ?
determinism (Var₂ M∈Γ x∈π val) If = ?
determinism (Var₂ M∈Γ x∈π val) Return = ?
determinism (Var₂ M∈Γ x∈π val) Bind₁ = ?
determinism (Var₂ M∈Γ x∈π val) (Label' p) = ?
determinism (Var₂ M∈Γ x∈π val) (Unlabel₁ p) = ?
determinism (Var₂ M∈Γ x∈π val) UnId₁ = ?
determinism (Var₂ M∈Γ x∈π val) (Fork p) = ?
determinism If (Var₂ M∈Γ x∈π val) = ?
determinism If If = ?
determinism IfTrue IfTrue = ?
determinism IfFalse IfFalse = ?
determinism Return (Var₂ M∈Γ x∈π val) = ?
determinism Return Return = ?
determinism Bind₁ (Var₂ M∈Γ x∈π val) = ?
determinism Bind₁ Bind₁ = ?
determinism Bind₂ Bind₂ = ?
determinism (Label' p) (Var₂ M∈Γ x∈π val) = ?
determinism (Label' p) (Label' .p) = ?
determinism (Unlabel₁ p) (Var₂ M∈Γ x∈π val) = ?
determinism (Unlabel₁ p) (Unlabel₁ .p) = ?
determinism (Unlabel₂ p) (Unlabel₂ .p) = ?
determinism UnId₁ (Var₂ M∈Γ x∈π val) = ?
determinism UnId₁ UnId₁ = ?
determinism UnId₂ UnId₂ = ?
determinism (Fork p) (Var₂ M∈Γ x∈π val) = ?
determinism (Fork p) (Fork .p) = ?
determinism Hole Hole = ?
