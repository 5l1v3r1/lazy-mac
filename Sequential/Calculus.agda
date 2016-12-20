open import Lattice

module Sequential.Calculus (𝓛 : Lattice) where

open import Types 𝓛
open import Relation.Binary.PropositionalEquality hiding ([_] ; subst)
open import Data.List.All
open import Data.Nat using (ℕ ; zero ; suc ; _≟_) public
import Data.List as L
open import Data.Maybe

-- A label-annotated, untyped free term.
-- Variables are represented by numbers.
data Term : Set where
  （） : Term

  True : Term 
  False : Term

  Id : Term -> Term 
  unId : Term -> Term

  Var : ℕ -> Term
  Abs : (n : ℕ) -> Term -> Term  -- n is the name of the variable
  App : Term -> Term -> Term

  If_Then_Else_ : Term -> Term -> Term -> Term

  Return : (l : Label) -> Term -> Term
  Bind : (l : Label) -> Term -> Term -> Term

  Mac : (l : Label) -> Term -> Term
  Res : (l : Label) -> Term -> Term

  label : ∀ {l h} -> (l⊑h : l ⊑ h) -> Term -> Term
  label∙ : ∀ {l h} -> (l⊑h : l ⊑ h) -> Term -> Term

  unlabel : ∀ {l h} -> (l⊑h : l ⊑ h) -> Term -> Term

  -- read : ∀ {α l h} -> l ⊑ h -> Term Δ (Ref l α) -> Term Δ (Mac h α)
  -- write : ∀ {α l h} -> l ⊑ h -> Term Δ (Ref h α) -> Term Δ α -> Term Δ (Mac l （）)
  -- new : ∀ {α l h} -> l ⊑ h -> Term Δ α -> Term Δ (Mac l (Ref h α))

  -- Concurrency
  fork : ∀ {l h} -> (l⊑h : l ⊑ h) -> Term -> Term

  deepDup : ℕ -> Term

  -- Represent sensitive information that has been erased.
  ∙ : Term

_[_/_] : Term -> Term -> ℕ -> Term
（） [ t₂ / x ] = （）
True [ t₂ / x ] = True
False [ t₂ / x ] = False
Id t₁ [ t₂ / x ] = Id (t₁ [ t₂ / x ])
unId t₁ [ t₂ / x ] = unId (t₁ [ t₂ / x ])
Var y [ t₂ / x ] with y ≟ x
Var y [ t₂ / .y ] | yes refl = t₂
Var y [ t₂ / x ] | no ¬p = Var y
-- We assume that variables are distinct so we don't have to care about name clashing and alpha renaming
-- We might instead choose the The Locally Nameless Representation (De Brujin Indexes + Free Variables)
Abs n t₁ [ t₂ / x ] = Abs n (t₁ [ t₂ / x ])
App t₁ t₂ [ t₃ / x ] = App (t₁ [ t₃ / x ]) (t₂ [ t₃ / x ])
(If t₁ Then t₂ Else t₃) [ t₄ / x ] = If (t₁ [ t₄ / x ]) Then (t₂ [ t₄ / x ]) Else (t₃ [ t₄ / x ])
Return l t₁ [ t₂ / x ] = Return l (t₁ [ t₂ / x ])
Bind l t₁ t₂ [ t₃ / x ] = Bind l (t₁ [ t₃ / x ]) (t₂ [ t₃ / x ])
Mac l t₁ [ t₂ / x ] = Mac l (t₁ [ t₂ / x ])
Res l t₁ [ t₂ / x ] = Res l (t₁ [ t₂ / x ])
label x t₁ [ t₂ / x₁ ] = label x (t₁ [ t₂ / x₁ ])
label∙ x t₁ [ t₂ / x₁ ] = label∙ x (t₁ [ t₂ / x₁ ])
unlabel x t₁ [ t₂ / x₁ ] = unlabel x (t₁ [ t₂ / x₁ ])
fork x t₁ [ t₂ / x₁ ] = fork x (t₁ [ t₂ / x₁ ])
deepDup y [ t₂ / x ] = deepDup y
∙ [ t₂ / x ] = ∙


-- A partial mapping from number (position) to terms.
data Heap : Set where
 [] : Heap
 _∷_ : Maybe Term -> Heap -> Heap

-- Continuation 
data Cont : Set where
 Var : ℕ -> Cont
 # : Label -> ℕ -> Cont
 Then_Else_ : Term -> Term -> Cont
 Bind : Label -> Term -> Cont
 unlabel : ∀ {l h} -> l ⊑ h -> Cont
 unId : Term -> Cont

Stack : Set
Stack = List Cont

--------------------------------------------------------------------------------

-- The proof that a certain term is a value
data IsValue : Term -> Set where
  （） : IsValue （）
  True : IsValue True
  False : IsValue False
  Abs : (n : ℕ) (t : Term) -> IsValue (Abs n t)
  Id : (t : Term) -> IsValue (Id t) 
  Mac : ∀ {l : Label} (t : Term) -> IsValue (Mac l t)
  Res : ∀ {l : Label} (t : Term) -> IsValue (Res l t)

--------------------------------------------------------------------------------

-- Selstof's Abstract Lazy Machine State
record State : Set where
 constructor _,_,_
 field
   heap : Heap
   term : Term
   stack : Stack

open State

-- data Fresh : Heap -> ℕ -> Set where
--  [] : Fresh [] 0
--  _∷_ : ∀ {Γ n mt} -> Fresh Γ n -> Fresh (mt ∷ Γ) (suc n)

-- Extend a heap with a new binding
data Add (t : Term) : Heap -> ℕ -> Heap -> Set where
  [] : Add t [] 0 ((just t) ∷ [])
  _∷_ : ∀ {mt n Γ Γ'} -> Add t Γ n Γ' -> Add t (mt ∷ Γ) (suc n) (mt ∷ Γ')
  
_≔_[_↦_] : Heap -> Heap -> ℕ -> Term -> Set
Γ₂ ≔ Γ₁ [ n ↦ t ] = Add t Γ₁ n Γ₂

data _⇝_ : State -> State -> Set where
 App₁ : ∀ {Γ Γ' S t₁ t₂ n} -> Γ' ≔ Γ [ n ↦ t₂ ] -> (Γ , App t₁ t₂ , S) ⇝ (Γ' , t₁ , ((Var n) ∷ S))
 App₂ : ∀ {Γ n m t S} -> (Γ , (Abs m t) , (Var n ∷ S)) ⇝ (Γ , (t [ (Var n) / m ]) , S)
 Var₁ : ∀ {Γ n m t S} -> (Γ , (Var n) , S) ⇝ ({!!} , t , ((# {!!} {!!}) ∷ S))
