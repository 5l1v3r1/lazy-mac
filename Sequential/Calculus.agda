import Lattice

module Sequential.Calculus {- (𝓛 : Lattice) -} where

open import Types renaming (_≟_ to _≟ᴸ_)
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
data Term {n : ℕ} (π : Context n) : Ty -> Set where
  （） : Term π （）

  True : Term π Bool 
  False : Term π Bool

  Id : ∀ {τ} -> Term π τ -> Term π (Id τ)
  unId : ∀ {τ} -> Term π (Id τ) -> Term π τ

  -- TODO: This unifies only when ty x is universally quantified, existentially quantify the type of the var.
  Var : ∀ {x} -> (x∈π : x ∈ π) -> Term π (ty x) 
  Abs : ∀ {β} -> (x : Variable) -> Term (x ∷ π) β -> Term π (ty x => β)
  App : ∀ {α β} -> Term π (α => β) -> Term π α -> Term π β

  If_Then_Else_ : ∀ {α} -> Term π Bool -> Term π α -> Term π α -> Term π α

  Return : ∀ {α} -> (l : Label) -> Term π α -> Term π (Mac l α)
  _>>=_ : ∀ {l} {α β} -> Term π (Mac l α) -> Term π (α => Mac l β) -> Term π (Mac l β)

  Mac : ∀ {α} -> (l : Label) -> Term π α -> Term π (Mac l α)

  Res : ∀ {α} -> (l : Label) -> Term π α -> Term π (Res l α)

  label : ∀ {l h α} -> (l⊑h : l ⊑ h) -> Term π α -> Term π (Mac l (Labeled h α))
  label∙ : ∀ {l h α} -> (l⊑h : l ⊑ h) -> Term π α -> Term π (Mac l (Labeled h α))

  unlabel : ∀ {l h α} -> (l⊑h : l ⊑ h) -> Term π (Labeled l α) -> Term π (Mac h α)

  -- read : ∀ {α l h} -> l ⊑ h -> Term π (Ref l α) -> Term π (Mac h α)
  -- write : ∀ {α l h} -> l ⊑ h -> Term π (Ref h α) -> Term π α -> Term π (Mac l （）)
  -- new : ∀ {α l h} -> l ⊑ h -> Term π α -> Term π (Mac l (Ref h α))

  -- Concurrency
  fork : ∀ {l h} -> (l⊑h : l ⊑ h) -> Term π (Mac h  （）) -> Term π (Mac l  （）)

  deepDup : (x : Variable) -> Term π (ty x)  -- This variable is unguarded

  -- Represent sensitive information that has been erased.
  ∙ : ∀ {{τ}} -> Term π τ

-- The proof that a certain term is a value
data Value {n} {π : Context n} : ∀ {τ} -> Term π τ -> Set where
  （） : Value （）
  True : Value True
  False : Value False
  Abs : ∀ {β} (x : Variable) (t : Term (x ∷ π) β) -> Value (Abs x t)
  Id : ∀ {τ} (t : Term π τ) -> Value (Id t) 
  Mac : ∀ {l : Label} {τ} (t : Term π τ) -> Value (Mac l t)
  Res : ∀ {l : Label} {τ} (t : Term π τ) -> Value (Res l t)

--------------------------------------------------------------------------------

-- -- The context of a term can be extended without harm
wken : ∀ {τ n₁ n₂} {Δ₁ : Context n₁} {Δ₂ : Context n₂} -> Term Δ₁ τ -> Δ₁ ⊆ˡ Δ₂ -> Term Δ₂ τ
wken （） p = （）
wken True p = True
wken False p = False
wken (Id t) p = Id (wken t p)
wken (unId t) p = unId (wken t p)
wken (Var x) p = Var (wken-∈ p x)
wken (Abs n t) p = Abs n (wken t (cons p))
wken (App t t₁) p = App (wken t p) (wken t₁ p)
wken (If t Then t₁ Else t₂) p = If (wken t p) Then (wken t₁ p) Else (wken t₂ p)
wken (Return l t) p = Return l (wken t p)
wken (t >>= t₁) p = (wken t p) >>= (wken t₁ p)
wken (Mac l t) p = Mac l (wken t p)
wken (Res l t) p = Res l (wken t p)
wken (label x t) p = label x (wken t p)
wken (label∙ x t) p = label∙ x (wken t p)
wken (unlabel x t) p = unlabel x (wken t p)
-- wken (read x t) p = read x (wken t p)
-- wken (write x t t₁) p = write x (wken t p) (wken t₁ p)
-- wken (new x t) p = new x (wken t p)
wken (fork x t) p = fork x (wken t p)
wken (deepDup x) p = deepDup x
wken ∙ p = ∙

_↑¹ : ∀ {α β n} {Δ : Context n} -> Term Δ α -> Term (β ∷ Δ) α
t ↑¹ = wken t (drop refl-⊆ˡ)

-- Performs the variable-term substitution.
var-subst : ∀ {n₁ n₂} {x y : Variable} (Δ₁ : Context n₁) (Δ₂ : Context n₂)
            -> Term Δ₂ (ty x) -> y ∈ (Δ₁ ++ [ x ] ++ Δ₂) -> Term (Δ₁ ++ Δ₂) (ty y)
var-subst [] Δ₂ v here = v
var-subst [] Δ₂ v (there p) = Var p
var-subst (._ ∷ Δ₁) Δ₂ v here = Var here
var-subst (x ∷ Δ₁) Δ₂ v (there p) = (var-subst Δ₁ Δ₂ v p) ↑¹

tm-subst : ∀ {τ n₁ n₂} {x : Variable} (Δ₁ : Context n₁) (Δ₂ : Context n₂)-> Term Δ₂ (ty x) -> Term (Δ₁ ++ [ x ] ++ Δ₂) τ -> Term (Δ₁ ++ Δ₂) τ
tm-subst Δ₁ Δ₂ v （） = （）
tm-subst Δ₁ Δ₂ v True = True
tm-subst Δ₁ Δ₂ v False = False
tm-subst Δ₁ Δ₂ v (Id t) = Id (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (unId t) = unId (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (Var y∈π) = var-subst Δ₁ Δ₂ v y∈π
tm-subst Δ₁ Δ₂ v (Abs n' t) = Abs n' (tm-subst (_ ∷ Δ₁) Δ₂ v t)
tm-subst Δ₁ Δ₂ v (App t t₁) = App (tm-subst Δ₁ Δ₂ v t) (tm-subst Δ₁ Δ₂ v t₁)
tm-subst Δ₁ Δ₂ v (If t Then t₁ Else t₂) = If (tm-subst Δ₁ Δ₂ v t) Then (tm-subst Δ₁ Δ₂ v t₁) Else (tm-subst Δ₁ Δ₂ v t₂)
tm-subst Δ₁ Δ₂ v (Return l t) = Return l (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (t >>= t₁) = (tm-subst Δ₁ Δ₂ v t) >>= (tm-subst Δ₁ Δ₂ v t₁)
tm-subst Δ₁ Δ₂ v (Mac l t) = Mac l (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (Res l t) = Res l (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (label x t) = label x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (label∙ x t) = label∙ x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (unlabel x t) = unlabel x (tm-subst Δ₁ Δ₂ v t)
-- tm-subst Δ₁ Δ₂ v (read x t) = read x (tm-subst Δ₁ Δ₂ v t)
-- tm-subst Δ₁ Δ₂ v (write x t t₁) = write x (tm-subst Δ₁ Δ₂ v t) (tm-subst Δ₁ Δ₂ v t₁)
-- tm-subst Δ₁ Δ₂ v (new x t) = new x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (fork x t) = fork x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (deepDup x) = deepDup x  -- x is free
tm-subst Δ₁ Δ₂ v ∙ = ∙

subst : ∀ {β n} {Δ : Context n} {x : Variable}-> Term Δ (ty x) -> Term (x ∷ Δ) β -> Term Δ β
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
data Cont : Ty -> Ty -> Set where
 Var : ∀ {τ₂ n} {π : Context n} {x : Variable} -> (x∈π : x ∈ π) -> Cont (ty x => τ₂) τ₂
 # : ∀ {n} {π : Context n} {x : Variable} -> (x∈π : x ∈ π)  -> Cont (ty x) (ty x) -- TODO maybe here we'd need x ∈ π ?
 Then_Else_ : ∀ {τ n} {π : Context n} -> Term π τ -> Term π τ -> Cont Bool τ
 Bind :  ∀ {τ₁ τ₂ l n} {π : Context n} -> Term π (τ₁ => Mac l τ₂) -> Cont (Mac l τ₁) (Mac l τ₂)
 unlabel : ∀ {l h τ} (p : l ⊑ h) -> Cont (Labeled l τ) (Mac h τ)
 unId : ∀ {τ} -> Cont (Id τ) τ

-- A Well-typed stack (Stack) contains well-typed terms and is indexed
-- by an input type and an output type.
-- It transforms the former in the latter according to the continuations.
-- TODO can we remove the label if we State is already labeled?
data Stack (l : Label) : Ty -> Ty -> Set where
 [] : ∀ {τ} -> Stack l τ τ
 _∷_ : ∀ {τ₁ τ₂ τ₃} -> Cont τ₁ τ₂ -> Stack l τ₂ τ₃ -> Stack l τ₁ τ₃
 ∙ : ∀ {τ₁ τ₂} -> Stack l τ₁ τ₂

--------------------------------------------------------------------------------

RawEnv : {n : ℕ} -> (π : Context n) -> Set
RawEnv π = (n : ℕ) -> ∃ (λ τ -> Maybe (Term π τ))

updateᴿ  : ∀ {τ n} {π : Context n} -> RawEnv π -> ℕ -> Maybe (Term π τ) -> RawEnv π
updateᴿ  M n₁ mt n₂ with n₁ ≟ᴺ n₂
updateᴿ  M n₁ mt .n₁ | yes refl = _ , mt
updateᴿ  M n₁ mt n₂ | no ¬p = M n₂

data Env {n : ℕ} (l : Label) (π : Context n) : Set where
  RE : RawEnv π -> Env l π

_[_↦_] : ∀ {τ l n} {π : Context n} -> Env l π -> ℕ -> Term π τ -> Env l π
_[_↦_] (RE M) n t = RE (updateᴿ M n (just t))

-- Syntatic sugar for remove without unsolved metas about τ
_[_↛_] : ∀ {τ l n} {π : Context n} -> Env l π -> ℕ -> (Term π τ) -> Env l π
_[_↛_] {τ} (RE M) n _ = RE (updateᴿ {τ} M n nothing)


_↦_∈_ : ∀ {τ l n} {π : Context n} -> ℕ -> Term π τ -> Env l π -> Set
_↦_∈_ {τ} n t (RE M) = M n ≡ (τ , just t)

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
  ⟨_,_,_⟩ : ∀ {τ₁ τ₂ n} {π : Context n} -> Heap -> Term π τ₁ -> Stack l τ₁ τ₂ -> State l τ₂

--------------------------------------------------------------------------------
