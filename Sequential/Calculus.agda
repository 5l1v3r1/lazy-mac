--import Lattice

module Sequential.Calculus {- (𝓛 : Lattice) -} where

open import Types
import Lattice
open Lattice.Lattice 𝓛 renaming (_≟_ to _≟ᴸ_)

open import Relation.Binary.PropositionalEquality hiding ([_] ; subst)
open import Data.Nat using (ℕ ; zero ; suc ; _+_) public
open import Data.Nat renaming ( _≟_ to  _≟ᴺ_ )

open import Data.Maybe
open import Data.Product
open import Function

-- The basic Term π τ is a term that has type τ in the context π
-- π is extended by lambda abstractions, which add the type and name of their argument to it.
--
-- π can be considered in general as a superset of the unguarded free variables
data Term {n : ℕ} (π : Context n) (l : Label) : Ty -> Set where
  （） : Term π l （）

  True : Term π l Bool
  False : Term π l Bool

  Id : ∀ {τ} -> Term π l τ -> Term π l (Id τ)
  unId : ∀ {τ} -> Term π l (Id τ) -> Term π l τ

  Var : ∀ {n τ} -> (x∈π : ⟪ n , τ , l ⟫ ∈ π) -> Term π l τ
  -- The argument of a function can have any label, e.g. Mac L () -> Mac H ()
  Abs : ∀ {β} -> (x : Variable) -> Term (x ∷ π) l β -> Term π l (ty x => β)
  -- The label comes from the function and it's based on the resulting type.
  App : ∀ {α β l'} -> Term π l (α => β) -> Term π l' α -> Term π l β

  If_Then_Else_ : ∀ {α} -> Term π l Bool -> Term π l α -> Term π l α -> Term π l α

  Return : ∀ {α} -> Term π l α -> Term π l (Mac l α)
  _>>=_ : ∀ {α β} -> Term π l (Mac l α) -> Term π l (α => Mac l β) -> Term π l (Mac l β)

  Mac : ∀ {α} -> Term π l α -> Term π l (Mac l α)

  Res : ∀ {α} -> Term π l α -> Term π l (Res l α)

  label : ∀ {h α} -> (l⊑h : l ⊑ h) -> Term π l α -> Term π l (Mac l (Labeled h α))
  label∙ : ∀ {h α} -> (l⊑h : l ⊑ h) -> Term π l α -> Term π l (Mac l (Labeled h α))

  unlabel : ∀ {l' α} -> (l⊑h : l' ⊑ l) -> Term π l' (Labeled l' α) -> Term π l (Mac l α)

  -- read : ∀ {α l h} -> l ⊑ h -> Term π (Ref l α) -> Term π (Mac h α)
  -- write : ∀ {α l h} -> l ⊑ h -> Term π (Ref h α) -> Term π α -> Term π (Mac l （）)
  -- new : ∀ {α l h} -> l ⊑ h -> Term π α -> Term π (Mac l (Ref h α))

  -- Concurrency
  fork : ∀ {h} -> (l⊑h : l ⊑ h) -> Term π h (Mac h  （）) -> Term π l (Mac l  （）)

  deepDup : ∀ {τ} -> ℕ -> Term π l τ  -- This variable is unguarded

  -- Represent sensitive information that has been erased.
  ∙ : ∀ {{τ}} -> Term π l τ

-- The proof that a certain term is a value
data Value {n} {π : Context n} {l} : ∀ {τ} -> Term π l τ -> Set where
  （） : Value （）
  True : Value True
  False : Value False
  Abs : ∀ {β} (x : Variable) (t : Term (x ∷ π) l β) -> Value (Abs x t)
  Id : ∀ {τ} (t : Term π l τ) -> Value (Id t)
  Mac : ∀ {τ} (t : Term π l τ) -> Value (Mac t)
  Res : ∀ {τ} (t : Term π l τ) -> Value (Res t)

--------------------------------------------------------------------------------

-- The context of a term can be extended without harm
wken : ∀ {τ l n₁ n₂} {Δ₁ : Context n₁} {Δ₂ : Context n₂} -> Term Δ₁ l τ -> Δ₁ ⊆ˡ Δ₂ -> Term Δ₂ l τ
wken （） p = （）
wken True p = True
wken False p = False
wken (Id t) p = Id (wken t p)
wken (unId t) p = unId (wken t p)
wken (Var x) p = Var (wken-∈ p x)
wken (Abs n t) p = Abs n (wken t (cons p))
wken (App t t₁) p = App (wken t p) (wken t₁ p)
wken (If t Then t₁ Else t₂) p = If (wken t p) Then (wken t₁ p) Else (wken t₂ p)
wken (Return t) p = Return (wken t p)
wken (t >>= t₁) p = (wken t p) >>= (wken t₁ p)
wken (Mac t) p = Mac (wken t p)
wken (Res t) p = Res (wken t p)
wken (label x t) p = label x (wken t p)
wken (label∙ x t) p = label∙ x (wken t p)
wken (unlabel x t) p = unlabel x (wken t p)
-- wken (read x t) p = read x (wken t p)
-- wken (write x t t₁) p = write x (wken t p) (wken t₁ p)
-- wken (new x t) p = new x (wken t p)
wken (fork x t) p = fork x (wken t p)
wken (deepDup x) p = deepDup x
wken ∙ p = ∙

_↑¹ : ∀ {l α β n} {Δ : Context n} -> Term Δ l α -> Term (β ∷ Δ) l α
t ↑¹ = wken t (drop refl-⊆ˡ)

-- Performs the variable-term substitution.
var-subst : ∀ {n₁ n₂} {x y : Variable} (Δ₁ : Context n₁) (Δ₂ : Context n₂)
            -> Term Δ₂ (lbl x) (ty x) -> y ∈ (Δ₁ ++ [ x ] ++ Δ₂) -> Term (Δ₁ ++ Δ₂) (lbl y) (ty y)
var-subst [] Δ₂ v here = v
var-subst [] Δ₂ v (there p) = Var p
var-subst (._ ∷ Δ₁) Δ₂ v here = Var here
var-subst (x ∷ Δ₁) Δ₂ v (there p) = (var-subst Δ₁ Δ₂ v p) ↑¹

tm-subst : ∀ {τ n₁ n₂ l} {x : Variable} (Δ₁ : Context n₁) (Δ₂ : Context n₂)-> Term Δ₂ (lbl x) (ty x) -> Term (Δ₁ ++ [ x ] ++ Δ₂) l τ -> Term (Δ₁ ++ Δ₂) l τ
tm-subst Δ₁ Δ₂ v （） = （）
tm-subst Δ₁ Δ₂ v True = True
tm-subst Δ₁ Δ₂ v False = False
tm-subst Δ₁ Δ₂ v (Id t) = Id (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (unId t) = unId (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (Var y∈π) = var-subst Δ₁ Δ₂ v y∈π
tm-subst Δ₁ Δ₂ v (Abs n' t) = Abs n' (tm-subst (_ ∷ Δ₁) Δ₂ v t)
tm-subst Δ₁ Δ₂ v (App t t₁) = App (tm-subst Δ₁ Δ₂ v t) (tm-subst Δ₁ Δ₂ v t₁)
tm-subst Δ₁ Δ₂ v (If t Then t₁ Else t₂) = If (tm-subst Δ₁ Δ₂ v t) Then (tm-subst Δ₁ Δ₂ v t₁) Else (tm-subst Δ₁ Δ₂ v t₂)
tm-subst Δ₁ Δ₂ v (Return t) = Return (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (t >>= t₁) = (tm-subst Δ₁ Δ₂ v t) >>= (tm-subst Δ₁ Δ₂ v t₁)
tm-subst Δ₁ Δ₂ v (Mac t) = Mac (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (Res t) = Res (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (label x t) = label x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (label∙ x t) = label∙ x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (unlabel x t) = unlabel x (tm-subst Δ₁ Δ₂ v t)
-- tm-subst Δ₁ Δ₂ v (read x t) = read x (tm-subst Δ₁ Δ₂ v t)
-- tm-subst Δ₁ Δ₂ v (write x t t₁) = write x (tm-subst Δ₁ Δ₂ v t) (tm-subst Δ₁ Δ₂ v t₁)
-- tm-subst Δ₁ Δ₂ v (new x t) = new x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (fork x t) = fork x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (deepDup x) = deepDup x  -- x is free
tm-subst Δ₁ Δ₂ v ∙ = ∙

subst : ∀ {β n l} {Δ : Context n} {x : Variable}-> Term Δ (lbl x) (ty x) -> Term (x ∷ Δ) l β -> Term Δ l β
subst {Δ = Δ} v t = tm-subst [] Δ v t

-- -- Substs t ns ns' t' applies the substitution t [ n / Var n' ] consecutively
-- -- for every n ∈ ns and n' ∈ ns' and returns the resulting term t'
-- data Substs (t₁ : Term) : List ℕ -> List ℕ -> Term -> Set where
--   [] : Substs t₁ [] [] t₁
--   _∷_ : ∀ {t₂ t₃ n n' ns ns'} -> Subst n (Var n') t₁ t₂ -> Substs t₂ ns ns' t₃
--                               -> Substs t₁ (n ∷ ns) (n' ∷ ns') t₃

-- --------------------------------------------------------------------------------

-- A Well-Typed continuation (Cont), contains well-typed terms and
-- transform the input type (first indexed) in the output type (second
-- index).
data Cont (l : Label) : Ty -> Ty -> Set where
 Var : ∀ {τ₂ n} {π : Context n} {x : Variable} -> (x∈π : x ∈ π) -> Cont l (ty x => τ₂) τ₂
 # : ∀ {n τ n'} {π : Context n} -> (x∈π : ⟪ n' , τ , l ⟫ ∈ π)  -> Cont l τ τ
 Then_Else_ : ∀ {τ n} {π : Context n} -> Term π l τ -> Term π l τ -> Cont l Bool τ
 Bind :  ∀ {τ₁ τ₂ n} {π : Context n} -> Term π l (τ₁ => Mac l τ₂) -> Cont l (Mac l τ₁) (Mac l τ₂)
 unlabel : ∀ {l' τ} (p : l' ⊑ l) -> Cont l (Labeled l' τ) (Mac l τ)
 unId : ∀ {τ} -> Cont l (Id τ) τ

-- A Well-typed stack (Stack) contains well-typed terms and is indexed
-- by an input type and an output type.
-- It transforms the former in the latter according to the continuations.
-- TODO can we remove the label if we State is already labeled?
data Stack (l : Label) : Ty -> Ty -> Set where
 [] : ∀ {τ} -> Stack l τ τ
 _∷_ : ∀ {τ₁ τ₂ τ₃} -> Cont l τ₁ τ₂ -> Stack l τ₂ τ₃ -> Stack l τ₁ τ₃
 ∙ : ∀ {τ₁ τ₂} -> Stack l τ₁ τ₂

--------------------------------------------------------------------------------

RawEnv : {n : ℕ} -> (π : Context n) -> Label -> Set
RawEnv π l = (n : ℕ) -> ∃ (λ τ -> Maybe (Term π l τ))

updateᴿ  : ∀ {τ l n} {π : Context n} -> RawEnv π l -> ℕ -> Maybe (Term π l τ) -> RawEnv π l
updateᴿ  M n₁ mt n₂ with n₁ ≟ᴺ n₂
updateᴿ  M n₁ mt .n₁ | yes refl = _ , mt
updateᴿ  M n₁ mt n₂ | no ¬p = M n₂

data Env {n : ℕ} (l : Label) (π : Context n) : Set where
  RE : RawEnv π l -> Env l π

-- Since you can read and write from the environment the label must be the same.
_[_↦_] : ∀ {τ l n} {π : Context n} -> Env l π -> ℕ -> Term π l τ -> Env l π
_[_↦_] (RE M) n t = RE (updateᴿ M n (just t))

-- Syntatic sugar for remove without unsolved metas about τ
_[_↛_] : ∀ {τ l n} {π : Context n} -> Env l π -> ℕ -> (Term π l τ) -> Env l π
_[_↛_] {τ} {l} (RE M) n _ = RE (updateᴿ {τ} {l} M n nothing)


_↦_∈_ : ∀ {τ l n} {π : Context n} -> ℕ -> Term π l τ -> Env l π -> Set
_↦_∈_ {τ} n t (RE M) = M n ≡  (τ , just t)

--------------------------------------------------------------------------------

-- Exists Context, (hides index n)
∃ᶜ : (P : ∀ {n} -> Context n -> Set) -> Set
∃ᶜ P = ∃ (λ n -> Σ (Context n) P)

Heap : Set
Heap = (l : Label) -> ∃ᶜ (λ π -> Env l π)

-- Update
_[_↦_]ᴴ : ∀ {n} {π : Context n} -> Heap -> (l : Label) -> Env l π -> Heap
_[_↦_]ᴴ Γ l₁ M l₂ with l₁ ≟ᴸ l₂
_[_↦_]ᴴ Γ l₁ M .l₁ | yes refl = _ , _ , M
_[_↦_]ᴴ Γ l₁ M l₂ | no ¬p = Γ l₂


_↦_∈ᴴ_ : ∀ {n} {π : Context n} -> (l : Label) -> Env l π -> Heap -> Set -- {τ l n} {π : Context n} -> ℕ -> Term π τ -> Env l π -> Set
_↦_∈ᴴ_ {n} {π} l M Γ = (Γ l) ≡ (n , (π , M))

--------------------------------------------------------------------------------

-- Sestoft's Abstract Lazy Machine State
-- The state is labeled to keep track of the security level of the
-- term (thread) executed.

data State (l : Label) : Ty -> Set where
  ⟨_,_,_⟩ : ∀ {τ₁ τ₂ n} {π : Context n} -> Heap -> Term π l τ₁ -> Stack l τ₁ τ₂ -> State l τ₂

--------------------------------------------------------------------------------
