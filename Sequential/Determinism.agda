module Sequential.Determinism where

open import Types
open import Sequential.Calculus
open import Sequential.Semantics
open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

open Variable renaming (lbl to l ; num to n)

-- It should be used as rewrite x∈Γ x∈Γ₁, but rewriting
-- does not work well with functions, therefore we have to
-- explicity perform the lookup in Γ, e.g. Γ x
∈-≡ : ∀ {Γ x t₁ t₂} -> x ↦ t₁ ∈ Γ -> x ↦ t₂ ∈ Γ -> t₁ ≡ t₂
∈-≡ refl refl = refl

determinism : ∀ {l Γ₁ t₁ S₁ Γ₂ t₂ S₂ Γ₃ t₃ S₃} ->
              let s₁ = ⟨ Γ₁ , t₁ , S₁ ⟩
                  s₂ = ⟨ Γ₂ , t₂ , S₂ ⟩
                  s₃ = ⟨ Γ₃ , t₃ , S₃ ⟩ in _⇝_ {l} s₁ s₂ -> s₁ ⇝ s₃ -> s₂ ≡ s₃      
determinism App₁ App₁ = {!!} -- Deterministic Fresh
determinism App₁ (Var₂ ())
determinism (App₂ x) (App₂ x₁) = {!!}  -- Determinisic sub
determinism (Var₁ {Γ} {x = x} x∈Γ ¬val) (Var₁ x∈Γ₁ ¬val₁) with Γ x
determinism (Var₁ refl ¬val) (Var₁ refl ¬val₁) | just x = refl
determinism (Var₁ () ¬val) (Var₁ x∈Γ₁ ¬val₁) | nothing
determinism (Var₁ {Γ} {x} x∈Γ ¬val) (Var₁' val x∈Γ₁) with Γ x
determinism (Var₁ refl ¬val) (Var₁' val refl) | just x = ⊥-elim (¬val val)
determinism (Var₁ () ¬val) (Var₁' val x∈Γ₁) | nothing
determinism (Var₁ x∈Γ ¬val) (Var₂ ())
determinism (Var₁' {Γ} {x} val x∈Γ) (Var₁ x∈Γ₁ ¬val) with Γ x
determinism (Var₁' val refl) (Var₁ refl ¬val) | just x = ⊥-elim (¬val val)
determinism (Var₁' val ()) (Var₁ x∈Γ₁ ¬val) | nothing
determinism (Var₁' {Γ} {x} val x∈Γ) (Var₁' val₁ x∈Γ₁) with Γ x
determinism (Var₁' val refl) (Var₁' val₁ refl) | just x = refl
determinism (Var₁' val ()) (Var₁' val₁ x∈Γ₁) | nothing
determinism (Var₁' val x∈Γ) (Var₂ ())
determinism (Var₂ ()) App₁
determinism (Var₂ ()) (Var₁ x∈Γ ¬val)
determinism (Var₂ ()) (Var₁' val₁ x∈Γ)
determinism (Var₂ val) (Var₂ val₁) = refl
determinism (Var₂ ()) If
determinism (Var₂ ()) Return
determinism (Var₂ ()) Bind₁
determinism (Var₂ ()) (Label' p)
determinism (Var₂ ()) (Unlabel₁ p)
determinism (Var₂ ()) UnId₁
determinism (Var₂ ()) (Fork p)
determinism (Var₂ ()) Hole
determinism If (Var₂ ())
determinism If If = refl
determinism IfTrue IfTrue = refl
determinism IfFalse IfFalse = refl
determinism Return (Var₂ ())
determinism Return Return = refl
determinism Bind₁ (Var₂ ())
determinism Bind₁ Bind₁ = refl
determinism Bind₂ Bind₂ = refl
determinism (Label' p) (Var₂ ())
determinism (Label' p) (Label' .p) = refl
determinism (Unlabel₁ p) (Var₂ ())
determinism (Unlabel₁ p) (Unlabel₁ .p) = refl
determinism (Unlabel₂ p) (Unlabel₂ .p) = refl
determinism UnId₁ (Var₂ ())
determinism UnId₁ UnId₁ = refl
determinism UnId₂ UnId₂ = refl
determinism (Fork p) (Var₂ ())
determinism (Fork p) (Fork .p) = refl
determinism Hole (Var₂ ())
determinism Hole Hole = refl
