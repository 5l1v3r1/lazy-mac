import Lattice

module Sequential.Erasure where

open import Types -- using (Label ; Ty ; _⋤_)
open import Sequential.Calculus
open import Sequential.Semantics
open import Data.Sum

-- A view over sensitive (secret) types.
-- lᴬ is the attacker's security level
data Secret (lᴬ : Label) : Ty -> Set where
  Mac : ∀ {τ h} -> (h⋤l : h ⋤ lᴬ) -> Secret lᴬ (Mac h τ)
  Res : ∀ {τ h} -> (h⋤l : h ⋤ lᴬ) -> Secret lᴬ (Res h τ)

Public : Label -> Ty -> Set
Public lᴬ τ = ¬ (Secret lᴬ τ)

publicMac : ∀ {lᴬ l τ} -> l ⊑ lᴬ ->  Public lᴬ (Mac l τ)
publicMac l⊑lᴬ (Mac h⋤lᴬ) = h⋤lᴬ l⊑lᴬ

publicRes : ∀ {lᴬ l τ} -> l ⊑ lᴬ ->  Public lᴬ (Res l τ)
publicRes l⊑lᴬ (Res h⋤lᴬ) = h⋤lᴬ l⊑lᴬ

funᴸ : ∀ {α β} -> (lᴬ : Label) -> Public lᴬ (α => β)
funᴸ _ = λ ()

Idᴸ : ∀ {τ} -> (lᴬ : Label) -> Public lᴬ (Id τ)
Idᴸ lᴬ = λ ()

-- Determines wheter a type is sensitive or not
isSecret? : (lᴬ : Label) (τ : Ty) -> (Secret lᴬ τ) ⊎ (Public lᴬ τ)
isSecret? lᴬ （） = inj₂ (λ ())
isSecret? lᴬ Bool = inj₂ (λ ())
isSecret? lᴬ (τ => τ₁) = inj₂ (λ ())
isSecret? lᴬ (Mac l τ) with l ⊑? lᴬ
isSecret? lᴬ (Mac l τ) | yes p = inj₂ (publicMac p)
isSecret? lᴬ (Mac l τ) | no ¬p = inj₁ (Mac ¬p)
isSecret? lᴬ (Res l τ) with l ⊑? lᴬ
isSecret? lᴬ (Res l τ) | yes p = inj₂ (publicRes p)
isSecret? lᴬ (Res l τ) | no ¬p = inj₁ (Res ¬p)
isSecret? lᴬ (Id τ) = inj₂ (λ ())

-- Erasure Function (entry-point)
ε : ∀ {n τ} {π : Context n} -> (lᴬ : Label) -> Term π τ -> Term π τ

εᴴ : ∀ {n τ lᴬ} {π : Context n} -> Secret lᴬ τ -> Term π τ -> Term π τ
εᴴ s t = {!!} 

εᴸ : ∀ {lᴬ n τ} {π : Context n} -> Public lᴬ τ -> Term π τ -> Term π τ
εᴸ p （） = （）
εᴸ p True = True
εᴸ p False = True
εᴸ {l} p (Id t) = Id (ε l t)
εᴸ {l} p (unId t) = unId (εᴸ (Idᴸ l) t)
εᴸ p (Var x∈π) = Var x∈π
εᴸ {l} p (Abs x t) = Abs x (ε l t)
εᴸ {l} p (App t t₁) = App (εᴸ (funᴸ l) t) (ε l t₁)
εᴸ {l} p (If t Then t₁ Else t₂) = If (εᴸ {l} (λ ()) t) Then εᴸ p t₁ Else εᴸ p t₂
εᴸ p (Return l t) = Return l (ε l t)
εᴸ p (t >>= t₁) = (εᴸ {!!} t) >>= {!!}
εᴸ p (Mac l t) = {!!}
εᴸ p (Res l t) = {!!}
εᴸ p (label x t) = {!!}
εᴸ p (label∙ x t) = {!!}
εᴸ p (unlabel x t) = {!!}
εᴸ p (fork x t) = {!!}
εᴸ p (deepDup x) = {!!}
εᴸ p ∙ = {!!} 


ε lᴬ t = {!!}
