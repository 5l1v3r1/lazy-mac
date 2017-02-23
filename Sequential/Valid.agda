import Lattice as L

module Sequential.Valid (𝓛 : L.Lattice) where

open import Types 𝓛

import Sequential.Calculus as S
open S 𝓛

open import Data.Nat using (_<_)
open import Data.Empty
open import Data.Product using (_×_ ; Σ)
open import Data.Maybe

-- A valid term contains only valid references, that contain a valid
-- address and no free-variables, i.e. variables unbounded in the
-- heap.

-- data Valid {l : Label} : ∀ {τ : Ty} -> State l τ -> Set where



validAddr : ∀ {l ls} -> l ∈ ls -> Heaps ls -> ℕ -> Set
validAddr here (⟨ M , Δ ⟩ ∷ Γ) n = n < lengthᴹ M
validAddr here (∙ ∷ _) n = ⊥
validAddr (there l∈ls) (_ S.∷ Γ) n = validAddr l∈ls Γ n

validᵀ : ∀ {ls τ π} -> Heaps ls -> Term π τ -> Set
validᵀ Γ S.（） = ⊤
validᵀ Γ S.True = ⊤
validᵀ Γ S.False = ⊤
validᵀ Γ (S.Id t) = validᵀ Γ t
validᵀ Γ (S.unId t) = validᵀ Γ t
validᵀ Γ (S.Var τ∈π) = ⊤
validᵀ Γ (S.Abs t) = validᵀ Γ t
validᵀ Γ (S.App t t₁) = validᵀ Γ t × validᵀ Γ t₁
validᵀ Γ (S.If t Then t₁ Else t₂) = (validᵀ Γ t) × (validᵀ Γ t₁) × validᵀ Γ t₂
validᵀ Γ (S.Return l t) = validᵀ Γ t
validᵀ Γ (t S.>>= t₁) = (validᵀ Γ t) × (validᵀ Γ t₁)
validᵀ Γ (S.Mac l t) = validᵀ Γ t
validᵀ {ls} {τ = Res .l Addr} Γ (S.Res l S.#[ t ]) = Σ (l ∈ ls) (λ l∈ls -> validAddr l∈ls Γ t )
validᵀ {ls} {τ = Res .l Addr} Γ (S.Res l S.#[ t ]ᴰ) = Σ (l ∈ ls) (λ l∈ls -> validAddr l∈ls Γ t )
validᵀ {ls} Γ (S.Res l t) = validᵀ Γ t
validᵀ Γ (S.label l⊑h t) = validᵀ Γ t
validᵀ Γ (S.label∙ l⊑h t) = ⊥
validᵀ Γ (S.unlabel l⊑h t) = validᵀ Γ t
validᵀ Γ (S.read x t) = validᵀ Γ t
validᵀ Γ (S.write x t t₁) = (validᵀ Γ t) × (validᵀ Γ t₁)
validᵀ Γ (S.write∙ x t t₁) = ⊥
validᵀ Γ (S.new x t) = validᵀ Γ t
validᵀ Γ (S.new∙ x t) = ⊥
validᵀ Γ S.#[ x ] = ⊤
validᵀ Γ S.#[ x ]ᴰ = ⊤
validᵀ Γ (S.fork l⊑h t) = validᵀ Γ t
validᵀ Γ (S.fork∙ l⊑h t) = ⊥
validᵀ Γ (S.deepDup t) = validᵀ Γ t
validᵀ Γ S.∙ = ⊥

-- Should I impose validity of variables as well?
-- It does not seem necessary at the moment
validᶜ : ∀ {l ls τ₁ τ₂} -> Heaps ls -> Cont l τ₁ τ₂ -> Set
validᶜ Γ (S.Var τ∈π) = ⊤
validᶜ Γ (S.# τ∈π) = ⊤
validᶜ Γ (S.Then x Else x₁) = (validᵀ Γ x) × validᵀ Γ x₁
validᶜ Γ (S.Bind x) = validᵀ Γ x
validᶜ Γ (S.unlabel p) = ⊤
validᶜ Γ S.unId = ⊤
validᶜ Γ (S.write x τ∈π) = ⊤
validᶜ Γ (S.write∙ x τ∈π) = ⊥
validᶜ Γ (S.read x) = ⊤

validˢ : ∀ {l ls τ₁ τ₂} -> Heaps ls -> Stack l τ₁ τ₂ -> Set
validˢ Γ S.[] = ⊤
validˢ Γ (C S.∷ S) = validᶜ Γ C × validˢ Γ S
validˢ Γ S.∙ = ⊥

validᴱ : ∀ {l π ls} -> Heaps ls -> Env l π -> Set
validᴱ Γ S.[] = ⊤
validᴱ Γ (just t S.∷ Δ) = validᵀ Γ t × validᴱ Γ Δ
validᴱ Γ (nothing S.∷ Δ) = validᴱ Γ Δ
validᴱ Γ S.∙ = ⊥

validᴴ : ∀ {ls₁ ls₂} -> Heaps ls₁ -> Heaps ls₂ -> Set
validᴴ Γ₁ S.[] = ⊤
validᴴ Γ₁ (S.⟨ M , Δ ⟩ S.∷ Γ₂) = validᴱ Γ₁ Δ × validᴴ Γ₁ Γ₂
validᴴ Γ₁ (S.∙ S.∷ Γ₂) = ⊥

validᴾ : ∀ {l ls τ} -> Program l ls τ -> Set
validᴾ S.⟨ Γ , t , S ⟩ = validᴴ Γ Γ × (validᵀ Γ t) × (validˢ Γ S)
validᴾ S.∙ = ⊥
