import Lattice 

module Sequential.Erasure where

open import Types
open import Sequential.Calculus
open import Sequential.Semantics
open import Data.Sum

-- A view over sensitive (secret) types.
-- lᴬ is the attacker's security level
data Secret (lᴬ : Label) : Ty -> Set where
  Macᴴ : ∀ {h τ} -> (h⋤lᴬ : h ⋤ lᴬ) -> Secret lᴬ (Mac h τ)
  Resᴴ : ∀ {h τ} -> (h⋤lᴬ : h ⋤ lᴬ) -> Secret lᴬ (Res h τ)

-- A view over insensitive (public) types.
-- lᴬ is the attacker's security level
data Public (lᴬ : Label) : Ty -> Set where
  Macᴸ : ∀ {τ l} -> (l⊑lᴬ : l ⊑ lᴬ) -> Public lᴬ (Mac l τ)
  Resᴸ : ∀ {τ l} -> (l⊑lᴬ : l ⊑ lᴬ) -> Public lᴬ (Res l τ)
  （） : Public lᴬ （）
  Bool : Public lᴬ Bool
  Id : ∀ {τ} ->  Public lᴬ (Id τ)
  Fun : ∀ {α β} -> Public lᴬ (α => β)

-- Secret and insensitive are mutually exclusive
secretNotPublic : ∀ {τ lᴬ} -> Secret lᴬ τ -> Public lᴬ τ -> ⊥
secretNotPublic (Macᴴ ¬p) (Macᴸ p) = ¬p p
secretNotPublic (Resᴴ ¬p) (Resᴸ p) = ¬p p

isSecret? : (lᴬ : Label) (τ : Ty) -> (Secret lᴬ τ) ⊎ (Public lᴬ τ)
isSecret? lᴬ （） = inj₂ （）
isSecret? lᴬ Bool = inj₂ Bool
isSecret? lᴬ (τ => τ₁) = inj₂ Fun
isSecret? lᴬ (Mac l τ) with l ⊑? lᴬ
isSecret? lᴬ (Mac l τ) | yes p = inj₂ (Macᴸ p)
isSecret? lᴬ (Mac l τ) | no ¬p = inj₁ (Macᴴ ¬p)
isSecret? lᴬ (Res l τ) with l ⊑? lᴬ
isSecret? lᴬ (Res l τ) | yes p = inj₂ (Resᴸ p)
isSecret? lᴬ (Res l τ) | no ¬p = inj₁ (Resᴴ ¬p)
isSecret? lᴬ (Id τ) = inj₂ Id

-- Erasure Function (entry-point)
ε : ∀ {n τ} {π : Context n} -> (lᴬ : Label) -> Term π τ -> Term π τ

εᴴ : ∀ {n τ lᴬ} {π : Context n} -> Secret lᴬ τ -> Term π τ -> Term π τ
εᴴ (Macᴴ h⋤lᴬ) t = ∙    -- I want to try to kill also the variables  and see how that goes.
εᴴ (Resᴴ h⋤lᴬ) t = {!!} -- Since only Res need to be erased I want to put it as public type

εᴸ : ∀ {lᴬ n τ} {π : Context n} -> Public lᴬ τ -> Term π τ -> Term π τ
εᴸ p （） = （）
εᴸ p True = True
εᴸ p False = True
εᴸ {l} p (Id t) = Id (ε l t)
εᴸ {l} p (unId t) = unId (εᴸ {l} Id t)
εᴸ p (Var x∈π) = Var x∈π
εᴸ {l} p (Abs x t) = Abs x (ε l t)
εᴸ {l} p (App t t₁) = App (εᴸ {l} Fun t) (ε l t₁)
εᴸ {l} p (If t Then t₁ Else t₂) = If (εᴸ {l} Bool t) Then εᴸ p t₁ Else εᴸ p t₂
εᴸ p (Return l t) = Return l (ε l t)
εᴸ {lᴬ} (Macᴸ l⊑lᴬ) (t >>= t₁) = (εᴸ (Macᴸ l⊑lᴬ) t) >>= εᴸ {lᴬ} Fun t₁
εᴸ {lᴬ} p (Mac l t) = Mac l (ε lᴬ t)
εᴸ {lᴬ} p (Res l t) = Res l (ε lᴬ t)
εᴸ {lᴬ} p (label {l} {h} l⊑h t) with h ⊑? lᴬ
εᴸ {lᴬ} p₁ (label l⊑h t) | yes p = label l⊑h (ε lᴬ t)
εᴸ {lᴬ} p (label l⊑h t) | no ¬p = label∙ l⊑h (ε lᴬ t)
εᴸ {lᴬ} p (label∙ l⊑h t) = label∙ l⊑h (ε lᴬ t)
εᴸ {lᴬ} (Macᴸ l⊑lᴬ) (unlabel {l} {h} l⊑h t) = unlabel l⊑h (εᴸ (Resᴸ (trans-⊑ l⊑h l⊑lᴬ)) t)
εᴸ {lᴬ} p (fork l⊑h t) = fork l⊑h (ε lᴬ t)
εᴸ p (deepDup x) = deepDup x
εᴸ p ∙ = ∙ 


ε lᴬ t = {!!}
