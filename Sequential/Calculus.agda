--import Lattice

module Sequential.Calculus {- (𝓛 : Lattice) -} where

open import Types
import Lattice
open Lattice.Lattice 𝓛 renaming (_≟_ to _≟ᴸ_)

open import Relation.Binary.PropositionalEquality hiding ([_] ; subst)
open import Data.Nat using (ℕ ; zero ; suc ; _+_) public
open import Data.Nat renaming ( _≟_ to  _≟ᴺ_ )

open import Data.Product
open import Function

-- The basic Term π τ is a term that has type τ in the context π
data Term (π : Context) : Ty -> Set where
  （） : Term π （）

  True : Term π Bool
  False : Term π Bool

  Id : ∀ {τ} -> Term π τ -> Term π (Id τ)
  unId : ∀ {τ} -> Term π (Id τ) -> Term π τ

  Var : ∀ {τ} -> (τ∈π : τ ∈ π) -> Term π τ
  Abs : ∀ {α β} -> Term (α ∷ π) β -> Term π (α => β)
  App : ∀ {α β} -> Term π (α => β) -> Term π α -> Term π β

  If_Then_Else_ : ∀ {α} -> Term π Bool -> Term π α -> Term π α -> Term π α

  Return : ∀ {α} -> (l : Label) -> Term π α -> Term π (Mac l α)
  _>>=_ : ∀ {l} {α β} -> Term π (Mac l α) -> Term π (α => Mac l β) -> Term π (Mac l β)

  Mac : ∀ {α} -> (l : Label) -> Term π α -> Term π (Mac l α)

  Res : ∀ {α} -> (l : Label) -> Term π α -> Term π (Res l α)

  label : ∀ {l h α} -> (l⊑h : l ⊑ h) -> Term π α -> Term π (Mac l (Labeled h α))
  label∙ : ∀ {l h α} -> (l⊑h : l ⊑ h) -> Term π α -> Term π (Mac l (Labeled h α))

  unlabel : ∀ {l h α} -> (l⊑h : l ⊑ h) -> Term π (Labeled l α) -> Term π (Mac h α)
  unlabel∙ : ∀ {l h α} -> (l⊑h : l ⊑ h) -> Term π (Labeled l α) -> Term π (Mac h α)

  -- read : ∀ {α l h} -> l ⊑ h -> Term π (Ref l α) -> Term π (Mac h α)
  -- write : ∀ {α l h} -> l ⊑ h -> Term π (Ref h α) -> Term π α -> Term π (Mac l （）)
  -- new : ∀ {α l h} -> l ⊑ h -> Term π α -> Term π (Mac l (Ref h α))

  -- Concurrency
  fork : ∀ {l h} -> (l⊑h : l ⊑ h) -> Term π (Mac h  （）) -> Term π (Mac l  （）)

  deepDup : ∀ {τ} -> Term π τ -> Term π τ

  -- Represent sensitive information that has been erased.
  ∙ : ∀ {{τ}} -> Term π τ

-- The proof that a certain term is a value
data Value {π : Context} : ∀ {τ} -> Term π τ -> Set where
  （） : Value （）
  True : Value True
  False : Value False
  Abs : ∀ {α β} (t : Term (α ∷ π) β) -> Value (Abs t)
  Id : ∀ {τ} (t : Term π τ) -> Value (Id t)
  Mac : ∀ {l : Label} {τ} (t : Term π τ) -> Value (Mac l t)
  Res : ∀ {l : Label} {τ} (t : Term π τ) -> Value (Res l t)

--------------------------------------------------------------------------------

-- The context of a term can be extended without harm
wken : ∀ {τ} {Δ₁ : Context} {Δ₂ : Context} -> Term Δ₁ τ -> Δ₁ ⊆ˡ Δ₂ -> Term Δ₂ τ
wken （） p = （）
wken True p = True
wken False p = False
wken (Id t) p = Id (wken t p)
wken (unId t) p = unId (wken t p)
wken (Var x) p = Var (wken-∈ p x)
wken (Abs t) p = Abs (wken t (cons p))
wken (App t t₁) p = App (wken t p) (wken t₁ p)
wken (If t Then t₁ Else t₂) p = If (wken t p) Then (wken t₁ p) Else (wken t₂ p)
wken (Return l t) p = Return l (wken t p)
wken (t >>= t₁) p = (wken t p) >>= (wken t₁ p)
wken (Mac l t) p = Mac l (wken t p)
wken (Res l t) p = Res l (wken t p)
wken (label x t) p = label x (wken t p)
wken (label∙ x t) p = label∙ x (wken t p)
wken (unlabel x t) p = unlabel x (wken t p)
wken (unlabel∙ x t) p = unlabel∙ x (wken t p)
-- wken (read x t) p = read x (wken t p)
-- wken (write x t t₁) p = write x (wken t p) (wken t₁ p)
-- wken (new x t) p = new x (wken t p)
wken (fork x t) p = fork x (wken t p)
wken (deepDup x) p = deepDup (wken x p)
wken ∙ p = ∙

_↑¹ : ∀ {α β} {Δ : Context} -> Term Δ α -> Term (β ∷ Δ) α
t ↑¹ = wken t (drop refl-⊆ˡ)

-- Performs the variable-term substitution.
var-subst : ∀ {α β} (Δ₁ : Context) (Δ₂ : Context)
            -> Term Δ₂ β -> α ∈ (Δ₁ ++ [ β ] ++ Δ₂) -> Term (Δ₁ ++ Δ₂) α
var-subst [] Δ₂ v here = v
var-subst [] Δ₂ v (there p) = Var p
var-subst (._ ∷ Δ₁) Δ₂ v here = Var here
var-subst (x ∷ Δ₁) Δ₂ v (there p) = (var-subst Δ₁ Δ₂ v p) ↑¹

tm-subst : ∀ {τ α} (Δ₁ : Context) (Δ₂ : Context)-> Term Δ₂ α -> Term (Δ₁ ++ [ α ] ++ Δ₂) τ -> Term (Δ₁ ++ Δ₂) τ
tm-subst Δ₁ Δ₂ v （） = （）
tm-subst Δ₁ Δ₂ v True = True
tm-subst Δ₁ Δ₂ v False = False
tm-subst Δ₁ Δ₂ v (Id t) = Id (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (unId t) = unId (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (Var y∈π) = var-subst Δ₁ Δ₂ v y∈π
tm-subst Δ₁ Δ₂ v (Abs t) = Abs (tm-subst (_ ∷ Δ₁) Δ₂ v t)
tm-subst Δ₁ Δ₂ v (App t t₁) = App (tm-subst Δ₁ Δ₂ v t) (tm-subst Δ₁ Δ₂ v t₁)
tm-subst Δ₁ Δ₂ v (If t Then t₁ Else t₂) = If (tm-subst Δ₁ Δ₂ v t) Then (tm-subst Δ₁ Δ₂ v t₁) Else (tm-subst Δ₁ Δ₂ v t₂)
tm-subst Δ₁ Δ₂ v (Return l t) = Return l (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (t >>= t₁) = (tm-subst Δ₁ Δ₂ v t) >>= (tm-subst Δ₁ Δ₂ v t₁)
tm-subst Δ₁ Δ₂ v (Mac l t) = Mac l (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (Res l t) = Res l (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (label x t) = label x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (label∙ x t) = label∙ x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (unlabel x t) = unlabel x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (unlabel∙ x t) = unlabel∙ x (tm-subst Δ₁ Δ₂ v t)
-- tm-subst Δ₁ Δ₂ v (read x t) = read x (tm-subst Δ₁ Δ₂ v t)
-- tm-subst Δ₁ Δ₂ v (write x t t₁) = write x (tm-subst Δ₁ Δ₂ v t) (tm-subst Δ₁ Δ₂ v t₁)
-- tm-subst Δ₁ Δ₂ v (new x t) = new x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (fork x t) = fork x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (deepDup x) = deepDup (tm-subst Δ₁ Δ₂ v x)
tm-subst Δ₁ Δ₂ v ∙ = ∙

subst : ∀ {α β} {Δ : Context} -> Term Δ α -> Term (α ∷ Δ) β -> Term Δ β
subst {Δ = Δ} v t = tm-subst [] Δ v t

-- TypedIx τ n π τ∈π is the proof that the n-th element of π is of type τ
-- turning it into the corresponding proof object τ∈π
-- We need this indirection because we keep track of
-- **unguarded** free variables.
data TypedIx (τ : Ty) : ℕ -> (π : Context) -> τ ∈ π -> Set where
  here : ∀ {π} -> TypedIx τ 0 (τ ∷ π) here
  there : ∀ {τ' n π} {τ∈π : τ ∈ π} -> TypedIx τ n π τ∈π -> TypedIx τ (suc n) (τ' ∷ π) (there τ∈π)

--------------------------------------------------------------------------------

-- A Well-Typed continuation (Cont), contains well-typed terms and
-- transform the input type (first indexed) in the output type (second
-- index).
data Cont (l : Label) : Ty -> Ty -> Set where
 Var : ∀ {τ₁ τ₂} {π : Context} -> (τ∈π : τ₁ ∈ π) -> Cont l (τ₁ => τ₂) τ₂
 # : ∀ {τ} {π : Context} -> (τ∈π : τ ∈ π)  -> Cont l τ τ
 Then_Else_ : ∀ {τ} {π : Context} -> Term π τ -> Term π τ -> Cont l Bool τ
 Bind :  ∀ {τ₁ τ₂} {π : Context} -> Term π (τ₁ => Mac l τ₂) -> Cont l (Mac l τ₁) (Mac l τ₂)
 unlabel : ∀ {l' τ} (p : l' ⊑ l) -> Cont l (Labeled l' τ) (Mac l τ)
 unlabel∙ : ∀ {l' τ} (p : l' ⊑ l) -> Cont l (Labeled l' τ) (Mac l τ) -- For simulation
 unId : ∀ {τ} -> Cont l (Id τ) τ

-- A Well-typed stack (Stack) contains well-typed terms and is indexed
-- by an input type and an output type.
-- It transforms the former in the latter according to the continuations.
data Stack (l : Label) : Ty -> Ty -> Set where
 [] : ∀ {τ} -> Stack l τ τ
 _∷_ : ∀ {τ₁ τ₂ τ₃} -> Cont l τ₁ τ₂ -> Stack l τ₂ τ₃ -> Stack l τ₁ τ₃
 ∙ : ∀ {τ₁ τ₂} -> Stack l τ₁ τ₂

--------------------------------------------------------------------------------

-- Note: at the moment in Env l π, π contains only variables labeled with l.
-- however in Term π, context π may contain variables with different labels.
-- I think this is still fine, because those variables are not mapped in
-- this environment (⟨ n , τ, l ⟩ ↦ nothing), but in their own.
data Env (l : Label) : Context -> Set where
  [] : Env l []
  _∷_ : ∀ {π τ} -> (t : Maybe (Term π τ)) -> Env l π -> Env l (τ ∷ π)
  ∙ : ∀ {π} -> Env l π

data Updateᴱ {l π τ} (mt : Maybe (Term π τ)) : ∀ {π'} -> τ ∈ π' -> Env l π' -> Env l π' -> Set where
  here : ∀ {Δ : Env l π} {mt' : Maybe (Term _ τ)} -> Updateᴱ mt here (mt' ∷ Δ) (mt ∷ Δ)
  there : ∀ {π' τ'} {τ∈π' : τ ∈ π'} {Δ Δ' : Env l π'} {mt' : Maybe (Term _ τ')} -> Updateᴱ mt τ∈π' Δ Δ' -> Updateᴱ mt (there τ∈π') (mt' ∷ Δ) (mt' ∷ Δ')
  ∙ : ∀ {π'} {τ∈π' : τ ∈ π'} -> Updateᴱ mt τ∈π' ∙ ∙

_≔_[_↦_]ᴱ : ∀ {l τ} {π π' : Context} -> Env l π' -> Env l π' -> τ ∈ π' -> Term π τ -> Set
Δ' ≔ Δ [ τ∈π' ↦ t ]ᴱ = Updateᴱ (just t) τ∈π' Δ Δ'

-- Syntatic sugar for removing a term from the environment.
-- The term is used only to fix its context π and avoid unsolved metas.
_≔_[_↛_]ᴱ : ∀ {l τ} {π π' : Context} -> Env l π' -> Env l π' -> τ ∈ π' -> Term π τ -> Set
_≔_[_↛_]ᴱ {π = π} Δ' Δ x t = Updateᴱ {π = π} nothing x Δ Δ'

data Memberᴱ {l π τ} (mt : Maybe (Term π τ)) : ∀ {π'} -> τ ∈ π' -> Env l π' -> Set where
  here : ∀ {Δ : Env l π} -> Memberᴱ mt here (mt ∷ Δ)
  there : ∀ {π' τ'} {τ∈π' : τ ∈ π'} {Δ : Env l π'} {mt' : Maybe (Term _ τ')} -> Memberᴱ mt τ∈π' Δ -> Memberᴱ mt (there τ∈π') (mt' ∷ Δ)
  -- TODO add x ↦ just ∙ ∈ ∙

_↦_∈ᴱ_ : ∀ {l τ} {π π' : Context} -> τ ∈ π' -> Term π τ -> Env l π' -> Set
x ↦ t ∈ᴱ Δ = Memberᴱ (just t) x Δ

-- Extends the environment with a new binding
insert : ∀ {l τ π} -> Term π τ -> Env l π -> Env l (τ ∷ π)
insert t ∙ = ∙
insert t Δ = just t ∷ Δ

--------------------------------------------------------------------------------

open import Data.List.All

Unique : Label -> List Label -> Set
Unique l₁ ls = All (λ l₂ → ¬ (l₁ ≡ l₂)) ls

∈-not-unique : ∀ {l ls} -> l ∈ ls -> Unique l ls -> ⊥
∈-not-unique here (px ∷ q) = ⊥-elim (px refl)
∈-not-unique (there p) (px ∷ q) = ∈-not-unique p q

data Heap : List Label -> Set where
  [] : Heap []
  _∷_ : ∀ {l ls π} {{u : Unique l ls}} -> Env l π -> Heap ls -> Heap (l ∷ ls)

data Member {l} {π} (Δ : Env l π) : ∀ {ls} -> Heap ls -> Set where
  here : ∀ {ls} {u : Unique l ls} {Γ : Heap ls} -> Member Δ (Δ ∷ Γ)
  there : ∀ {ls l' π'} {u : Unique l' ls} {Γ : Heap ls} {Δ' : Env l' π'} -> Member Δ Γ -> Member Δ (Δ' ∷ Γ)

_↦_∈ᴴ_ : ∀ {ls π} -> (l : Label) -> Env l π -> Heap ls -> Set
l ↦ Δ ∈ᴴ Γ = Member Δ Γ

data Update {l} {π} (Δ : Env l π) : ∀ {ls} -> Heap ls -> Heap ls -> Set where
  here : ∀ {ls π'} {u : Unique l ls} {Γ : Heap ls} {Δ' : Env l π'} -> Update Δ (Δ' ∷ Γ) (Δ ∷ Γ)
  there : ∀ {ls l' π'} {u : Unique l' ls} {Γ Γ' : Heap ls} {Δ' : Env l' π'} -> Update Δ Γ Γ' -> Update Δ (Δ' ∷ Γ) (Δ' ∷ Γ')

_≔_[_↦_]ᴴ : ∀ {π ls} -> Heap ls -> Heap ls -> (l : Label) -> Env l π -> Set
Γ' ≔ Γ [ l ↦ Δ ]ᴴ = Update Δ Γ Γ'

--------------------------------------------------------------------------------

-- Sestoft's Abstract Lazy Machine State
-- The state is labeled to keep track of the security level of the
-- term (thread) executed.

data State (ls : List Label) (l : Label) : Ty -> Set where
  ⟨_,_,_⟩ : ∀ {τ₁ τ₂} {π : Context} -> Heap ls -> Term π τ₁ -> Stack l τ₁ τ₂ -> State ls l τ₂

--------------------------------------------------------------------------------

-- A list of variables bound in context π
data Vars (π : Context) : Set where
  [] : Vars π
  _∷_ : ∀ {τ : Ty} -> (τ∈π : τ ∈ π) -> Vars π -> Vars π

_+++_ : ∀ {π} -> Vars π -> Vars π -> Vars π
[] +++ ys = ys
(τ∈π ∷ xs) +++ ys = τ∈π ∷ (xs +++ ys)

infixr 3 _+++_

-- Removes variables τ ∈ (τ ∷ π)
dropⱽ : ∀ {τ π} -> Vars (τ ∷ π) -> Vars π
dropⱽ [] = []
dropⱽ (here ∷ vs) = dropⱽ vs
dropⱽ (there τ∈π ∷ vs) = τ∈π ∷ dropⱽ vs

ufv : ∀ {τ π} -> Term π τ -> Vars π
ufv （） = []
ufv True = []
ufv False = []
ufv (Id t) = ufv t
ufv (unId t) = ufv t
ufv (Var τ∈π) = τ∈π ∷ []
ufv (Abs t) = dropⱽ (ufv t)
ufv (App t t₁) = ufv t +++ ufv t₁ -- In theory it should be ∪ to avoid duplicates, but I don't have sets :-(
ufv (If t Then t₁ Else t₂) = ufv t +++ ufv t₁ +++ ufv t₂
ufv (Return l t) = ufv t
ufv (t >>= t₁) = ufv t +++ ufv t₁
ufv (Mac l t) = ufv t
ufv (Res l t) = ufv t
ufv (label l⊑h t) = ufv t
ufv (label∙ l⊑h t) = ufv t
ufv (unlabel l⊑h t) = ufv t
ufv (unlabel∙ l⊑h t) = ufv t
ufv (fork l⊑h t) = ufv t
ufv (deepDup n) = [] -- Unguarded
ufv ∙ = []

tys : ∀ {π} -> Vars π -> Context
tys [] = []
tys (_∷_ {τ} τ∈π vs) = τ ∷ (tys vs)

prefix-⊆ˡ : ∀ {π₁} -> (π₂ : Context)  -> π₁ ⊆ˡ π₂ ++ π₁
prefix-⊆ˡ [] = refl-⊆ˡ
prefix-⊆ˡ (x ∷ π) = drop (prefix-⊆ˡ π)

dups : ∀ {π l} -> (vs : Vars π) -> Env l π -> Env l (tys vs ++ π)
dups [] Δ = Δ
dups (τ∈π ∷ vs) Δ = (just (deepDup (Var (wken-∈ (prefix-⊆ˡ (tys vs)) τ∈π)))) ∷ (dups vs Δ)
