module Sequential.Determinism where

open import Sequential.Calculus
open import Sequential.Semantics
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

determinism : ∀ {l τ} {s₁ s₂ s₃ : State l τ} -> s₁ ⇝ s₂ -> s₁ ⇝ s₃ -> s₂ ≡ s₃
determinism App₁ step₂ = {!!}
determinism (App₂ y∈π x∈π) step₂ = {!!}
determinism (Var₁ x∈π x₁ x₂) step₂ = {!!}
determinism (Var₁' x∈π x₁ x₂) step₂ = {!!}
determinism (Var₂ x₁) step₂ = {!!}
determinism If (Var₂ ())
determinism If If = refl
determinism IfTrue IfTrue = refl
determinism IfFalse IfFalse = refl
determinism Return step₂ = {!!}
determinism Bind₁ step₂ = {!!}
determinism Bind₂ Bind₂ = refl
determinism (Label' p) step₂ = {!!}
determinism (Unlabel₁ p) step₂ = {!!}
determinism (Unlabel₂ p) (Unlabel₂ .p) = refl
determinism UnId₁ (Var₂ ())
determinism UnId₁ UnId₁ = refl
determinism UnId₂ UnId₂ = refl
determinism (Fork p) step₂ = {!!}
determinism Hole Hole = {!refl!}
