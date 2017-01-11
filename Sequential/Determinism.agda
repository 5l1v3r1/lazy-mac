module Sequential.Determinism where

open import Sequential.Calculus
open import Sequential.Semantics
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

open import Types

↦-≡ : ∀ {n n' l τ} {π : Context n'} {E : Env l π} {t₁ t₂ : Term π τ} -> n ↦ t₁ ∈ E -> n ↦ t₂ ∈ E -> t₁ ≡ t₂
↦-≡ {n} {E = RE Δ} x y with Δ n
↦-≡ {n} {_} {l} {.proj₁} {π} {RE Δ} refl refl | proj₁ , ._ = refl

determinism : ∀ {l τ} {s₁ s₂ s₃ : State l τ} -> s₁ ⇝ s₂ -> s₁ ⇝ s₃ -> s₂ ≡ s₃
determinism (App₁ refl) (App₁ refl) = refl
determinism (App₁ Δ∈Γ) (Var₂ Δ∈Γ₁ x∈π ())
determinism (App₂ y∈π x∈π) (App₂ y∈π₁ .x∈π) = refl
determinism (Var₁ refl x∈π t∈Δ ¬val) (Var₁ refl .x∈π t∈Δ₁ ¬val₁) rewrite ↦-≡ t∈Δ t∈Δ₁ = refl
determinism (Var₁ refl x∈π t∈Δ ¬val) (Var₁' refl .x∈π v∈Δ val) rewrite ↦-≡ t∈Δ v∈Δ = ⊥-elim (¬val val)
determinism (Var₁ Δ∈Γ x∈π t∈Δ ¬val) (Var₂ Δ∈Γ₁ x∈π₁ ())
determinism (Var₁' refl x∈π v∈Δ val) (Var₁ refl .x∈π t∈Δ ¬val) rewrite ↦-≡ t∈Δ v∈Δ = ⊥-elim (¬val val)
determinism (Var₁' refl x∈π v∈Δ val) (Var₁' refl .x∈π v∈Δ₁ val₁) rewrite ↦-≡ v∈Δ v∈Δ₁ = refl
determinism (Var₁' Δ∈Γ x∈π v∈Δ val) (Var₂ Δ∈Γ₁ x∈π₁ ())
determinism (Var₂ Δ∈Γ x∈π ()) (App₁ Δ∈Γ₁)
determinism (Var₂ Δ∈Γ x∈π ()) (Var₁ Δ∈Γ₁ x∈π₁ t∈Δ ¬val)
determinism (Var₂ Δ∈Γ x∈π ()) (Var₁' Δ∈Γ₁ x∈π₁ v∈Δ val₁)
determinism (Var₂ refl x∈π val) (Var₂ refl .x∈π val₁) = refl
determinism (Var₂ Δ∈Γ x∈π ()) If 
determinism (Var₂ Δ∈Γ x∈π ()) Return 
determinism (Var₂ Δ∈Γ x∈π ()) Bind₁ 
determinism (Var₂ Δ∈Γ x∈π ()) (Label' p) 
determinism (Var₂ Δ∈Γ x∈π ()) (Unlabel₁ p)
determinism (Var₂ Δ∈Γ x∈π ()) UnId₁ 
determinism (Var₂ Δ∈Γ x∈π ()) (Fork p)
determinism If (Var₂ Δ∈Γ x∈π ())
determinism If If = refl
determinism IfTrue IfTrue = refl
determinism IfFalse IfFalse = refl
determinism Return (Var₂ Δ∈Γ x∈π ())
determinism Return Return = refl
determinism Bind₁ (Var₂ Δ∈Γ x∈π ())
determinism Bind₁ Bind₁ = refl
determinism Bind₂ Bind₂ = refl
determinism (Label' p) (Var₂ Δ∈Γ x∈π ())
determinism (Label' p) (Label' .p) = refl
determinism (Unlabel₁ p) (Var₂ Δ∈Γ x∈π ())
determinism (Unlabel₁ p) (Unlabel₁ .p) = refl
determinism (Unlabel₂ p) (Unlabel₂ .p) = refl
determinism UnId₁ (Var₂ Δ∈Γ x∈π ())
determinism UnId₁ UnId₁ = refl
determinism UnId₂ UnId₂ = refl
determinism (Fork p) (Var₂ Δ∈Γ x∈π ())
determinism (Fork p) (Fork .p) = refl
-- Morally they are the same, however the context π is chosen non deterministically
-- I wonder if this can be made to work using π = ∙ or if it is pushing it too much.
determinism Hole Hole = {!refl!} -- π₁ ≠ π₂
