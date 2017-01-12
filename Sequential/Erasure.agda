import Lattice

module Sequential.Erasure where

open import Types
open import Sequential.Calculus
open import Sequential.Semantics
open import Data.Sum

-- A view over sensitive (secret) computation types.
-- lᴬ is the attacker's security level
data Secret (lᴬ : Label) : Ty -> Set where
  Macᴴ : ∀ {h τ} -> (h⋤lᴬ : h ⋤ lᴬ) -> Secret lᴬ (Mac h τ)
  -- Resᴴ is not here because it is always erased homomorphically
  -- like Public types, except for the constructor Res.


-- A view over insensitive (public) types.
-- lᴬ is the attacker's security level
data Public (lᴬ : Label) : Ty -> Set where
  Macᴸ : ∀ {τ l} -> (l⊑lᴬ : l ⊑ lᴬ) -> Public lᴬ (Mac l τ)
  Res : ∀ {τ l} -> (l⊑?lᴬ : Dec (l ⊑ lᴬ)) -> Public lᴬ (Res l τ)
  （） : Public lᴬ （）
  Bool : Public lᴬ Bool
  Id : ∀ {τ} ->  Public lᴬ (Id τ)
  Fun : ∀ {α β} -> Public lᴬ (α => β)

-- Secret and insensitive are mutually exclusive
secretNotPublic : ∀ {τ lᴬ} -> Secret lᴬ τ -> Public lᴬ τ -> ⊥
secretNotPublic (Macᴴ ¬p) (Macᴸ p) = ¬p p

Level : Label -> Ty -> Set
Level lᴬ τ = (Secret lᴬ τ) ⊎ (Public lᴬ τ)

isSecret? : (lᴬ : Label) (τ : Ty) -> Level lᴬ τ
isSecret? lᴬ （） = inj₂ （）
isSecret? lᴬ Bool = inj₂ Bool
isSecret? lᴬ (τ => τ₁) = inj₂ Fun
isSecret? lᴬ (Mac l τ) with l ⊑? lᴬ
isSecret? lᴬ (Mac l τ) | yes p = inj₂ (Macᴸ p)
isSecret? lᴬ (Mac l τ) | no ¬p = inj₁ (Macᴴ ¬p)
isSecret? lᴬ (Res l τ) = inj₂ (Res (l ⊑? lᴬ))
isSecret? lᴬ (Id τ) = inj₂ Id

-- Erasure Function (entry-point)
εᵀ : ∀ {τ n} {π : Context n} -> (lᴬ : Label) -> Term π τ -> Term π τ
εᴴ : ∀ {lᴬ n τ} {π : Context n} -> Secret lᴬ τ -> Term π τ -> Term π τ
εᴸ : ∀ {lᴬ n τ} {π : Context n} -> Public lᴬ τ -> Term π τ -> Term π τ


εᴴ {lᴬ} (Macᴴ h⋤lᴬ) (unId t) = unId (εᴸ {lᴬ} Id t)
εᴴ (Macᴴ h⋤lᴬ) (Var x∈π) = Var x∈π
εᴴ (Macᴴ h⋤lᴬ) (App t t₁) = ∙
εᴴ {lᴬ} (Macᴴ h⋤lᴬ) (If t Then t₁ Else t₂) = If (εᴸ {lᴬ} Bool t) Then (εᴴ (Macᴴ h⋤lᴬ) t₁) Else (εᴴ (Macᴴ h⋤lᴬ) t₂)
εᴴ (Macᴴ h⋤lᴬ) (Return l t) = ∙
εᴴ (Macᴴ h⋤lᴬ) (t >>= t₁) = ∙
εᴴ (Macᴴ h⋤lᴬ) (Mac l t) = ∙
εᴴ (Macᴴ h⋤lᴬ) (label l⊑h t) = ∙
εᴴ (Macᴴ h⋤lᴬ) (label∙ l⊑h t) = ∙
εᴴ {lᴬ} (Macᴴ h⋤lᴬ) (unlabel l⊑h t) = unlabel l⊑h (εᵀ lᴬ t)
εᴴ (Macᴴ h⋤lᴬ) (fork l⊑h t) = ∙
εᴴ (Macᴴ h⋤lᴬ) (deepDup x) = ∙
εᴴ (Macᴴ h⋤lᴬ) ∙ = ∙

εᴸ p （） = （）
εᴸ p True = True
εᴸ p False = True
εᴸ {l} p (Id t) = Id (εᵀ l t)
εᴸ {l} p (unId t) = unId (εᴸ {l} Id t)
εᴸ p (Var x∈π) = Var x∈π
εᴸ {l} p (Abs x t) = Abs x (εᵀ l t)
εᴸ {l} p (App t t₁) = App (εᴸ {l} Fun t) (εᵀ l t₁)
εᴸ {l} p (If t Then t₁ Else t₂) = If (εᴸ {l} Bool t) Then εᴸ p t₁ Else εᴸ p t₂
εᴸ {lᴬ} p (Return l t) = Return l (εᵀ lᴬ t)
εᴸ {lᴬ} (Macᴸ l⊑lᴬ) (t >>= t₁) = (εᴸ (Macᴸ l⊑lᴬ) t) >>= εᴸ {lᴬ} Fun t₁
εᴸ {lᴬ} p (Mac l t) = Mac l (εᵀ lᴬ t)
εᴸ {lᴬ} (Res (yes p)) (Res l t) = Res l (εᵀ lᴬ t)
εᴸ (Res (no ¬p)) (Res l t) = Res l ∙
εᴸ {lᴬ} p (label {l} {h} l⊑h t) with h ⊑? lᴬ
εᴸ {lᴬ} p₁ (label l⊑h t) | yes p = label l⊑h (εᵀ lᴬ t)
εᴸ {lᴬ} p (label l⊑h t) | no ¬p = label∙ l⊑h (εᵀ lᴬ t)
εᴸ {lᴬ} p (label∙ l⊑h t) = label∙ l⊑h (εᵀ lᴬ t)
εᴸ {lᴬ} (Macᴸ l⊑lᴬ) (unlabel {l} {h} l⊑h t) = unlabel l⊑h (εᴸ (Res (yes (trans-⊑ l⊑h l⊑lᴬ))) t)
εᴸ {lᴬ} p (fork l⊑h t) = fork l⊑h (εᵀ lᴬ t)
εᴸ p (deepDup x) = deepDup x
εᴸ p ∙ = ∙

εᵗ : ∀ {lᴬ τ n} {π : Context n} -> (Secret lᴬ τ) ⊎ (Public lᴬ τ) -> Term π τ -> Term π τ
εᵗ (inj₁ x) t = εᴴ x t
εᵗ (inj₂ y) t = εᴸ y t

εᵀ {τ} lᴬ t = εᵗ (isSecret? lᴬ τ) t

--------------------------------------------------------------------------------

open import Data.Product as P
open import Data.Maybe as M
open import Function

-- Point-wise erasure of a RawEnv
εᴿ : ∀ {n} {π : Context n} -> Label -> RawEnv π -> RawEnv π
εᴿ lᴬ M n = P.map id (M.map (εᵀ lᴬ)) (M n)

-- Constant mapping to ∙ (it can be modified and this is a problem)
-- We need the old environment for the type
∙ᴿ : ∀ {n} {π : Context n} -> RawEnv π -> RawEnv π
∙ᴿ M n = proj₁ (M n) , just ∙

εᴱ : ∀ {l lᴬ n} {π : Context n} -> Dec (l ⊑ lᴬ) ->  Env l π -> Env l π
εᴱ {_} {lᴬ} (yes p) (RE x) = RE (εᴿ lᴬ x)
εᴱ (no ¬p) (RE x) = RE (∙ᴿ x)  -- Here I should have a different Env that is not updateable

-- Heap Erasure Function
εʰ : (lᴬ : Label) -> Heap -> Heap
εʰ lᴬ Γ l with Γ l
εʰ lᴬ Γ l | n , π , Δ = n , π , εᴱ (l ⊑? lᴬ) Δ

--------------------------------------------------------------------------------

εᶜ : ∀ {τ₁ τ₂} -> (lᴬ : Label) -> Cont τ₁ τ₂ -> Cont τ₁ τ₂
εᶜ lᴬ (Var x∈π) = Var x∈π
εᶜ lᴬ (# x∈π) = # x∈π
εᶜ lᴬ (Then t₁ Else t₂) = Then (εᵀ lᴬ t₁) Else εᵀ lᴬ t₂
εᶜ lᴬ (Bind t) = Bind (εᵀ lᴬ t)
εᶜ lᴬ (unlabel p) = unlabel p
εᶜ lᴬ unId = unId

εˢ : ∀ {τ₁ τ₂ l} -> (lᴬ : Label) -> Stack l τ₁ τ₂ -> Stack l τ₁ τ₂

εᵏ : ∀ {τ₁ τ₂ l lᴬ} -> (Secret lᴬ τ₁) ⊎ (Public lᴬ τ₁) -> Stack l τ₁ τ₂ -> Stack l τ₁ τ₂
εᵏ (inj₁ x) S = ∙
εᵏ (inj₂ y) [] = []
εᵏ {lᴬ = lᴬ} (inj₂ y) (x ∷ S) = εᶜ lᴬ x ∷ εᵏ (isSecret? lᴬ _) S
εᵏ (inj₂ y) ∙ = ∙

εˢ {τ₁} lᴬ S = εᵏ (isSecret? lᴬ τ₁) S


--------------------------------------------------------------------------------

ε : ∀ {l τ} (lᴬ : Label) -> State l τ -> State l τ
ε lᴬ ⟨ Γ , t , S ⟩ = ⟨ εʰ lᴬ Γ , εᵗ (isSecret? lᴬ _) t , εᵏ (isSecret? lᴬ _) S ⟩

--------------------------------------------------------------------------------

{-

Homomorphic erasure function for MAC H and stack does works for Bind₁ but not for Bind₂

Bind₁:
(Γ , t₁ >>= t₂ , S) → (Γ , t₁ , >>= t₂ : S)

(ε(Γ) , ε(t₁) >>= ε(t₂) , ε(S)) → (ε(Γ) , ε(t₁) , >>= ε(t₂) : ε(S))

Bind₂:
(Γ , Mac t₁ , >>= t₂ : S) → (Γ , t₂ t₁ , S)

(ε(Γ) , Mac ∙ , >>= ε(t₂) : ε(S)) ↛ (ε(Γ) , ε(t₂) ε(t₁) , ε(S))  -- t₁ ≠ ∙

-}

-- Simulation Property
ε-sim' : ∀ {l lᴬ τ₁ τ₁' τ₂ n n' Γ Γ'} {S : Stack l τ₁ τ₂} {S' : Stack l τ₁' τ₂} {π : Context n} {π' : Context n'} {t : Term π τ₁} {t' : Term π' τ₁'} ->
         (x : Level lᴬ τ₁) (y : Level lᴬ τ₁') ->
           ⟨ Γ , t , S ⟩ ⇝ ⟨ Γ' , t' , S' ⟩ -> ⟨ (εʰ lᴬ Γ) , (εᵗ x t) , (εᵏ x S) ⟩ ⇝ ⟨ (εʰ lᴬ Γ') , (εᵗ y t') , (εᵏ y S') ⟩
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) y (App₁ Δ∈Γ) = {!!}
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) y (Var₁ Δ∈Γ x∈π t∈Δ ¬val) = {!!}
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) y (Var₁' Δ∈Γ x∈π v∈Δ val) = {!!}
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) y (Var₂ Δ∈Γ x∈π val) = {!!}
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) (inj₁ ()) If
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) (inj₂ Bool) If = {!!} -- :( ?
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) (inj₁ (Macᴴ h⋤lᴬ₁)) Return = Hole
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) (inj₂ (Macᴸ l⊑lᴬ)) Return = ⊥-elim (h⋤lᴬ l⊑lᴬ)
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) (inj₁ (Macᴴ h⋤lᴬ₁)) Bind₁ = {!Hole!} -- Does not commute anymore
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) (inj₂ (Macᴸ l⊑lᴬ)) Bind₁ = ⊥-elim (h⋤lᴬ l⊑lᴬ)
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) (inj₁ (Macᴴ h⋤lᴬ₁)) Bind₂ = {!Hole!} -- Idem
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) (inj₂ (Macᴸ l⊑lᴬ)) Bind₂ = ⊥-elim (h⋤lᴬ l⊑lᴬ)
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) (inj₁ (Macᴴ h⋤lᴬ₁)) (Label' p) = Hole
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) (inj₂ (Macᴸ l⊑lᴬ)) (Label' p) = ⊥-elim (h⋤lᴬ l⊑lᴬ)
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) (inj₁ ()) (Unlabel₁ p)
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) (inj₂ (Res x)) (Unlabel₁ p₁) = {!unlabel p₁ ∷ S!} -- :(
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) (inj₁ ()) UnId₁
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) (inj₂ Id) UnId₁ = {!!} -- :(
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) (inj₁ (Macᴴ h⋤lᴬ₁)) (Fork p) = Hole
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) (inj₂ (Macᴸ l⊑lᴬ)) (Fork p) = ⊥-elim (h⋤lᴬ l⊑lᴬ)
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) (inj₁ (Macᴴ h⋤lᴬ₁)) Hole = Hole
ε-sim' (inj₁ (Macᴴ h⋤lᴬ)) (inj₂ y) Hole = Hole
ε-sim' (inj₂ y) y₁ (App₁ Δ∈Γ) = {!!}
ε-sim' (inj₂ y) y₁ (App₂ y∈π x∈π) = {!!}
ε-sim' (inj₂ y) y₁ (Var₁ Δ∈Γ x∈π t∈Δ ¬val) = {!!}
ε-sim' (inj₂ y) y₁ (Var₁' Δ∈Γ x∈π v∈Δ val) = {!!}
ε-sim' (inj₂ y) y₁ (Var₂ Δ∈Γ x∈π val) = {!!}
ε-sim' (inj₂ y) (inj₁ ()) If
ε-sim' (inj₂ y) (inj₂ Bool) If = {!If!} -- Lemma
ε-sim' (inj₂ y) (inj₁ (Macᴴ h⋤lᴬ)) IfTrue = {!!} -- Lemma
ε-sim' (inj₂ y) (inj₂ y₁) IfTrue = {!!}
ε-sim' (inj₂ y) y₁ IfFalse = {!!}
ε-sim' (inj₂ (Macᴸ l⊑lᴬ)) (inj₁ (Macᴴ h⋤lᴬ)) Return = ⊥-elim (h⋤lᴬ l⊑lᴬ)
ε-sim' (inj₂ (Macᴸ l⊑lᴬ)) (inj₂ (Macᴸ l⊑lᴬ₁)) Return = {!Return!} -- Lemma
ε-sim' (inj₂ (Macᴸ l⊑lᴬ)) (inj₁ (Macᴴ h⋤lᴬ)) Bind₁ = ⊥-elim (h⋤lᴬ l⊑lᴬ)
ε-sim' (inj₂ (Macᴸ l⊑lᴬ)) (inj₂ (Macᴸ l⊑lᴬ₁)) Bind₁ = {!Bind₁!} -- Lemma
ε-sim' (inj₂ (Macᴸ l⊑lᴬ)) (inj₁ (Macᴴ h⋤lᴬ)) Bind₂ = ⊥-elim (h⋤lᴬ l⊑lᴬ)
ε-sim' (inj₂ (Macᴸ l⊑lᴬ)) (inj₂ (Macᴸ l⊑lᴬ₁)) Bind₂ = {!!} -- Lemma
ε-sim' (inj₂ y) y₁ (Label' p) = {!!}
ε-sim' (inj₂ y) y₁ (Unlabel₁ p) = {!!}
ε-sim' (inj₂ y) y₁ (Unlabel₂ p) = {!!}
ε-sim' (inj₂ y) (inj₁ ()) UnId₁
ε-sim' (inj₂ y) (inj₂ Id) UnId₁ = {!UnId₁!}
ε-sim' (inj₂ y) (inj₁ (Macᴴ h⋤lᴬ)) UnId₂ = {!!}
ε-sim' (inj₂ y) (inj₂ y₁) UnId₂ = {!!}
ε-sim' (inj₂ (Macᴸ l⊑lᴬ)) (inj₁ (Macᴴ h⋤lᴬ)) (Fork p) = ⊥-elim (h⋤lᴬ l⊑lᴬ)
ε-sim' (inj₂ y) (inj₂ y₁) (Fork p) = {!!}
ε-sim' (inj₂ y) (inj₁ (Macᴴ h⋤lᴬ)) Hole = Hole
ε-sim' (inj₂ y) (inj₂ y₁) Hole = Hole

ε-sim : ∀ {l τ} {s₁ s₂ : State l τ} -> (lᴬ : Label) -> s₁ ⇝ s₂ -> ε lᴬ s₁ ⇝ ε lᴬ s₂
ε-sim {s₁ = ⟨ x , x₁ , x₂ ⟩} {⟨ x₃ , x₄ , x₅ ⟩} lᴬ step = ε-sim' (isSecret? lᴬ _) (isSecret? lᴬ _) step
