open import Lattice

module Sequential.Calculus {- (𝓛 : Lattice) -} where

open import Types
open import Relation.Binary.PropositionalEquality hiding ([_] ; subst)
open import Data.List.All
open import Data.Nat using (ℕ ; zero ; suc ; _≟_) public
import Data.List as L
open import Data.Maybe
open import Data.Product

-- The basic Term π τ is a term that has type τ in the context π
-- π is extended by lambda abstractions, which add the type and name of their argument to it.
-- I am still using names (ℕ) for variables, even though they are isomorphic to a membership proof
-- object, e.g. x ∈ xs, because it does not require an extra parameter (xs).
-- π can be considered in general as a superset of the unguarded free variables
data Term (π : Context) : Ty -> Set where
  （） : Term π （）

  True : Term π Bool 
  False : Term π Bool

  Id : ∀ {τ} -> Term π τ -> Term π (Id τ)
  unId : ∀ {τ} -> Term π (Id τ) -> Term π τ

  Var : ∀ {n τ} -> (l : Label) -> (n , τ) ∈ π -> Term π τ
  Abs : ∀ {α β} -> (n : ℕ) -> Term ((n , α) ∷ π) β -> Term π (α => β)
  App : ∀ {α β} -> Term π (α => β) -> Term π α -> Term π β

  If_Then_Else_ : ∀ {α} -> Term π Bool -> Term π α -> Term π α -> Term π α

  Return : ∀ {α} -> (l : Label) -> Term π α -> Term π (Mac l α)
  _>>=_ : ∀ {l} {α β} -> Term π (Mac l α) -> Term π (α => Mac l β) -> Term π (Mac l β)

  Mac : ∀ {α} -> (l : Label) -> Term π α -> Term π (Mac l α)

  Res : ∀ {α} -> (l : Label) -> Term π α -> Term π (Res l α)

  label : ∀ {l h α} -> l ⊑ h -> Term π α -> Term π (Mac l (Labeled h α))
  label∙ : ∀ {l h α} -> l ⊑ h -> Term π α -> Term π (Mac l (Labeled h α))

  unlabel : ∀ {l h α} -> l ⊑ h -> Term π (Labeled l α) -> Term π (Mac h α)

  -- read : ∀ {α l h} -> l ⊑ h -> Term π (Ref l α) -> Term π (Mac h α)
  -- write : ∀ {α l h} -> l ⊑ h -> Term π (Ref h α) -> Term π α -> Term π (Mac l （）)
  -- new : ∀ {α l h} -> l ⊑ h -> Term π α -> Term π (Mac l (Ref h α))

  -- Concurrency
  fork : ∀ {l h} -> l ⊑ h -> Term π (Mac h  （）) -> Term π (Mac l  （）)

  deepDup : ∀ {τ} -> ℕ -> Term π τ  -- The variable here could be free

  -- Represent sensitive information that has been erased.
  ∙ : ∀ {{τ}} -> Term π τ

-- The proof that a certain term is a value
data Value {π : Context} : ∀ {τ} -> Term π τ -> Set where
  （） : Value （）
  True : Value True
  False : Value False
  Abs : ∀ {α β} (n : ℕ) (t : Term ((n , α) ∷ π) β) -> Value (Abs n t)
  Id : ∀ {τ} (t : Term π τ) -> Value (Id t) 
  Mac : ∀ {l : Label} {τ} (t : Term π τ) -> Value (Mac l t)
  Res : ∀ {l : Label} {τ} (t : Term π τ) -> Value (Res l t)

--------------------------------------------------------------------------------

-- The context of a term can be extended without harm
wken : ∀ {τ Δ₁ Δ₂} -> Term Δ₁ τ -> Δ₁ ⊆ˡ Δ₂ -> Term Δ₂ τ
wken （） p = （）
wken True p = True
wken False p = False
wken (Id t) p = Id (wken t p)
wken (unId t) p = unId (wken t p)
wken (Var l x) p = Var l (wken-∈ x p)
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

_↑¹ : ∀ {α β Δ} -> Term Δ α -> Term (β ∷ Δ) α
t ↑¹ = wken t (drop refl-⊆ˡ)

-- Performs the variable-term substitution.
var-subst : ∀ {α β n m} (l : Label) (Δ₁ Δ₂ : Context) -> Term Δ₂ α -> (n , β) ∈ (Δ₁ ++ L.[ (m , α) ] ++ Δ₂) -> Term (Δ₁ ++ Δ₂) β
var-subst l [] Δ₂ t Here = t
var-subst l [] Δ t (There p) = Var l p
var-subst l (β ∷ Δ₁) Δ₂ t Here = Var l Here
var-subst l (x ∷ Δ₁) Δ₂ t (There p) = (var-subst l Δ₁ Δ₂ t p) ↑¹

tm-subst : ∀ {α n τ} (Δ₁ Δ₂ : Context)-> Term Δ₂ α -> Term (Δ₁ ++ L.[ (n , α ) ] ++ Δ₂) τ -> Term (Δ₁ ++ Δ₂) τ
tm-subst Δ₁ Δ₂ v （） = （）
tm-subst Δ₁ Δ₂ v True = True
tm-subst Δ₁ Δ₂ v False = False
tm-subst Δ₁ Δ₂ v (Id t) = Id (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (unId t) = unId (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (Var l x) = var-subst l Δ₁ Δ₂ v x
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

subst : ∀ {Δ α β n} -> Term Δ α -> Term ((n , α) ∷ Δ) β -> Term Δ β
subst {Δ} v t = tm-subst [] Δ v t

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
data Cont (π : Context) : Ty -> Ty -> Set where
 Var : ∀ {n τ₁ τ₂} -> (n , τ₁) ∈ π -> Cont π (τ₁ => τ₂) τ₂
 # : ∀ {τ} -> Label -> ℕ -> Cont π τ τ
 Then_Else_ : ∀ {τ} -> Term π τ -> Term π τ -> Cont π Bool τ
 Bind :  ∀ {τ₁ τ₂ l} -> Term π (τ₁ => Mac l τ₂) -> Cont π (Mac l τ₁) (Mac l τ₂)
 unlabel : ∀ {l h τ} (p : l ⊑ h) -> Cont π (Res l τ) (Mac h τ)
 unId : ∀ {τ} -> Cont π (Id τ) τ

-- A Well-typed stack (Stack) contains well-typed terms and is indexed
-- by an input type and an output type.
-- It transforms the former in the latter according to the continuations.
data Stack (l : Label) (π : Context) : Ty -> Ty -> Set where
 [] : ∀ {τ} -> Stack l π τ τ
 _∷_ : ∀ {τ₁ τ₂ τ₃} -> Cont π τ₁ τ₂ -> Stack l π τ₂ τ₃ -> Stack l π τ₁ τ₃
 ∙ : ∀ {τ₁ τ₂} -> Stack l π τ₁ τ₂

--------------------------------------------------------------------------------

data Map (l : Label) : Context -> Set where
  [] : Map l []
  _∷_ : ∀ {π τ} -> (nt : ℕ × Maybe (Term π τ)) -> Map l π -> Map l ((proj₁ nt , τ) ∷ π)
  ∙ : ∀ {π} -> Map l π

data Heap (π : Context) : List Label -> Set where
  [] : Heap π []
  _∷_ : ∀ {l ls} -> Map l π -> Heap π ls -> Heap π (l ∷ ls) -- Add unique l

-- Sestoft's Abstract Lazy Machine State
-- The state is labeled to keep track of the security level of the
-- term (thread) executed.

data State (ls : List Label) : Ty -> Set where
  ⟨_,_,_⟩ : ∀ {l π τ₁ τ₂} -> Heap π ls -> Term π τ₁ -> Stack l π τ₁ τ₂ -> State ls τ₂

--------------------------------------------------------------------------------
