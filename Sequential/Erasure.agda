--import Lattice

module Sequential.Erasure where

open import Types
import Lattice
open Lattice.Lattice 𝓛 renaming (_≟_ to _≟ᴸ_)

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


εᴴ (Macᴴ h⋤lᴬ) t = ∙

εᴸ p （） = （）
εᴸ p True = True
εᴸ p False = False
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

ε' : ∀ {lᴬ l τ₂} -> Level lᴬ τ₂  -> State l τ₂ -> State l τ₂
ε' {lᴬ} (inj₁ x) (⟨_,_,_⟩ {τ} {π = π} Γ t S) = ⟨ εʰ lᴬ Γ , ∙ {π = π} {{τ}} , ∙ ⟩
ε' {lᴬ} (inj₂ y) ⟨ Γ , t , S ⟩ = ⟨ εʰ lᴬ Γ , εᵗ (isSecret? lᴬ _) t , εᵏ (isSecret? lᴬ _) S ⟩


ε : ∀ {l τ} (lᴬ : Label) -> State l τ -> State l τ
ε lᴬ ⟨ Γ , t , S ⟩ = ⟨ εʰ lᴬ Γ , εᵗ (isSecret? lᴬ _) t , εᵏ (isSecret? lᴬ _) S ⟩

--------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality

{-

Homomorphic erasure function for MAC H and stack does works for Bind₁ but not for Bind₂

Bind₁:
(Γ , t₁ >>= t₂ , S) → (Γ , t₁ , >>= t₂ : S)

(ε(Γ) , ε(t₁) >>= ε(t₂) , ε(S)) → (ε(Γ) , ε(t₁) , >>= ε(t₂) : ε(S))

Bind₂:
(Γ , Mac t₁ , >>= t₂ : S) → (Γ , t₂ t₁ , S)

(ε(Γ) , Mac ∙ , >>= ε(t₂) : ε(S)) ↛ (ε(Γ) , ε(t₂) ε(t₁) , ε(S))  -- t₁ ≠ ∙

-}
--ε∙≡∙ : ∀ {τ

-- Simulation Property
ε-sim : ∀ {lᴬ l τ} {s₁ s₂ : State l τ} -> (x : Level lᴬ τ) -> s₁ ⇝ s₂ -> ε' x s₁ ⇝ ε' x s₂
-- If l is H then ok, but in general l could be L. In this case Hole does not apply because Γ changes.
-- I think that Γ = ∙ could work
ε-sim (inj₁ (Macᴴ h⋤lᴬ)) (App₁ Δ∈Γ) = {!!}
ε-sim (inj₁ x) (App₂ y∈π x∈π) = Hole
ε-sim (inj₁ x) (Var₁ Δ∈Γ x∈π t∈Δ ¬val) = {!!} -- Must show that lᴬ ⋤ l'
ε-sim (inj₁ x) (Var₁' Δ∈Γ x∈π v∈Δ val) = Hole
ε-sim (inj₁ x) (Var₂ Δ∈Γ x∈π val) = {!!} -- Must show that lᴬ ⋤ l'
ε-sim (inj₁ x) If = Hole
ε-sim (inj₁ x) IfTrue = Hole
ε-sim (inj₁ x) IfFalse = Hole
ε-sim (inj₁ x) Return = Hole
ε-sim (inj₁ x) Bind₁ = Hole
ε-sim (inj₁ x) Bind₂ = Hole
ε-sim (inj₁ x) (Label' p) = Hole
ε-sim (inj₁ x) (Unlabel₁ p) = Hole
ε-sim (inj₁ x) (Unlabel₂ p) = Hole
ε-sim (inj₁ x) UnId₁ = Hole
ε-sim (inj₁ x) UnId₂ = Hole
ε-sim (inj₁ x) (Fork p) = Hole
ε-sim (inj₁ x) Hole = Hole
ε-sim (inj₂ y) (App₁ Δ∈Γ) = {!!}
ε-sim (inj₂ y) (App₂ y∈π x∈π) = {!!}
ε-sim (inj₂ y) (Var₁ Δ∈Γ x∈π t∈Δ ¬val) = {!!}
ε-sim (inj₂ y) (Var₁' Δ∈Γ x∈π v∈Δ val) = {!!}
ε-sim (inj₂ y) (Var₂ Δ∈Γ x∈π val) = {!!}
ε-sim (inj₂ y) If = {!y!}  -- :|
ε-sim (inj₂ y) IfTrue = IfTrue
ε-sim (inj₂ y) IfFalse = IfFalse
ε-sim {lᴬ = lᴬ} {l} (inj₂ y) Return with l ⊑? lᴬ
ε-sim (inj₂ y) Return | yes p = Return
ε-sim (inj₂ y) Return | no ¬p = Hole
ε-sim {lᴬ = lᴬ} {l} (inj₂ y) Bind₁ with l ⊑? lᴬ
ε-sim {lᴬ = lᴬ} {l} (inj₂ y) Bind₁ | yes p with l ⊑? lᴬ
ε-sim (inj₂ y) Bind₁ | yes p₁ | yes p = {!Bind₁!} -- Lemma, proof irrelevance for ⊑
ε-sim (inj₂ y) Bind₁ | yes p | no ¬p = ⊥-elim (¬p p)
ε-sim (inj₂ y) Bind₁ | no ¬p = Hole
ε-sim {lᴬ = lᴬ} {l} (inj₂ y) Bind₂ with l ⊑? lᴬ
ε-sim {lᴬ = lᴬ} {l} (inj₂ y) Bind₂ | yes p with l ⊑? lᴬ
ε-sim (inj₂ y) Bind₂ | yes p₁ | yes p = {!Bind₂!} -- Lemma, proof irrelevance for ⊑
ε-sim (inj₂ y) Bind₂ | yes p | no ¬p = ⊥-elim (¬p p)
ε-sim (inj₂ y) Bind₂ | no ¬p = Hole
ε-sim {lᴬ = lᴬ} {l} (inj₂ y) (Label' p) with l ⊑? lᴬ
ε-sim {lᴬ = lᴬ} (inj₂ y) (Label' {h = h} p₁) | yes p with h ⊑? lᴬ
ε-sim (inj₂ y) (Label' p₂) | yes p₁ | yes p = Label' p₂
ε-sim (inj₂ y) (Label' p₁) | yes p | no ¬p = {!!} -- Add Label∙ step: label∙ t ⇝ return (Res ∙)
ε-sim (inj₂ y) (Label' p) | no ¬p = Hole
ε-sim {lᴬ = lᴬ} {l} (inj₂ y) (Unlabel₁ p) with l ⊑? lᴬ
ε-sim (inj₂ y) (Unlabel₁ p₁) | yes p = {!Unlabel₁ ?!} -- Lemma
ε-sim {lᴬ = lᴬ} (inj₂ y) (Unlabel₁ {l' = l'} p) | no ¬p = {!!} -- :|
ε-sim {lᴬ = lᴬ} {l} (inj₂ y) (Unlabel₂ p) with l ⊑? lᴬ
ε-sim {lᴬ = lᴬ} (inj₂ y) (Unlabel₂ {l' = l'} p₁) | yes p with l' ⊑? lᴬ
ε-sim (inj₂ y) (Unlabel₂ p₂) | yes p₁ | yes p = {!!} -- :|
ε-sim (inj₂ y) (Unlabel₂ p₁) | yes p | no ¬p = ⊥-elim (¬p (trans-⊑ p₁ p))
ε-sim {lᴬ = lᴬ} (inj₂ y) (Unlabel₂ {l' = l'} p) | no ¬p with l' ⊑? lᴬ
ε-sim (inj₂ y) (Unlabel₂ p₁) | no ¬p | yes p = {!!} -- Unlabel∙
ε-sim (inj₂ y) (Unlabel₂ p) | no ¬p₁ | no ¬p = {!Unlabel₂ ?!} -- Unlabel∙ : (Res t , Unlabel∙ ∷ S) →  (∙ , ∙)
ε-sim (inj₂ y) UnId₁ = {!UnId₁!} -- :|
ε-sim (inj₂ y) UnId₂ = UnId₂
ε-sim {lᴬ = lᴬ} {l} (inj₂ y) (Fork p) with l ⊑? lᴬ
ε-sim (inj₂ y) (Fork p₁) | yes p = Fork p₁
ε-sim (inj₂ y) (Fork p) | no ¬p = Hole
ε-sim {lᴬ = lᴬ} (inj₂ y) (Hole {τ₁ = τ₁} {τ₂} {π₁ = π₁} {π₂}) with isSecret? lᴬ τ₁ | isSecret? lᴬ τ₂
ε-sim (inj₂ y) Hole | inj₁ (Macᴴ h⋤lᴬ) | inj₁ (Macᴴ h⋤lᴬ₁) = Hole
ε-sim (inj₂ y₁) Hole | inj₁ (Macᴴ h⋤lᴬ) | inj₂ y = Hole
ε-sim (inj₂ y₁) Hole | inj₂ y | inj₁ (Macᴴ h⋤lᴬ) = Hole
ε-sim (inj₂ y₂) Hole | inj₂ y | inj₂ y₁ = Hole
