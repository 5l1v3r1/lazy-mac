module Sequential.Determinism where

open import Sequential.Calculus
open import Sequential.Semantics
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

open import Types

determinism : ∀ {l τ} {s₁ s₂ s₃ : State l τ} -> s₁ ⇝ s₂ -> s₁ ⇝ s₃ -> s₂ ≡ s₃
determinism (App₁ x x₁) (App₁ x₂ x₃) = ?
determinism (App₁ x x₁) (Var₂ x∈π val x₂) = ?
determinism (App₂ y∈π x∈π) (App₂ y∈π₁ .x∈π) = ?
determinism (Var₁ x x∈π t∈M ¬val x₁) (Var₁ x₂ .x∈π t∈M₁ ¬val₁ x₃) = ?
determinism (Var₁ x x∈π t∈M ¬val x₁) (Var₁' x₂ .x∈π val v∈M) = ?
determinism (Var₁ x x∈π t∈M ¬val x₁) (Var₂ x∈π₁ val x₂) = ?
determinism (Var₁' x x∈π val v∈M) (Var₁ x₁ .x∈π t∈M ¬val x₂) = ?
determinism (Var₁' x x∈π val v∈M) (Var₁' x₁ .x∈π val₁ v∈M₁) = ?
determinism (Var₁' x x∈π val v∈M) (Var₂ x∈π₁ val₁ x₁) = ?
determinism (Var₂ x∈π val x) (App₁ x₁ x₂) = ?
determinism (Var₂ x∈π val x₁) (Var₁ x x∈π₁ t∈M ¬val x₂) = ?
determinism (Var₂ x∈π val x₁) (Var₁' x x∈π₁ val₁ v∈M) = ?
determinism (Var₂ x∈π val x) (Var₂ .x∈π val₁ x₁) = ?
determinism (Var₂ x∈π val x) If = ?
determinism (Var₂ x∈π val x) Return = ?
determinism (Var₂ x∈π val x) Bind₁ = ?
determinism (Var₂ x∈π val x) (Label' p) = ?
determinism (Var₂ x∈π val x) (Unlabel₁ p) = ?
determinism (Var₂ x∈π val x) UnId₁ = ?
determinism (Var₂ x∈π val x) (Fork p) = ?
determinism If (Var₂ x∈π val x) = ?
determinism If If = ?
determinism IfTrue IfTrue = ?
determinism IfFalse IfFalse = ?
determinism Return (Var₂ x∈π val x) = ?
determinism Return Return = ?
determinism Bind₁ (Var₂ x∈π val x) = ?
determinism Bind₁ Bind₁ = ?
determinism Bind₂ Bind₂ = ?
determinism (Label' p) (Var₂ x∈π val x) = ?
determinism (Label' p) (Label' .p) = ?
determinism (Unlabel₁ p) (Var₂ x∈π val x) = ?
determinism (Unlabel₁ p) (Unlabel₁ .p) = ?
determinism (Unlabel₂ p) (Unlabel₂ .p) = ?
determinism UnId₁ (Var₂ x∈π val x) = ?
determinism UnId₁ UnId₁ = ?
determinism UnId₂ UnId₂ = ?
determinism (Fork p) (Var₂ x∈π val x) = ?
determinism (Fork p) (Fork .p) = ?
determinism Hole Hole = ?
