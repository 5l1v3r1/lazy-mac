open import Lattice

module Sequential.Calculus (𝓛 : Lattice) where

open import Types 𝓛
open import Relation.Binary.PropositionalEquality hiding ([_] ; subst)
open import Data.List.All
open import Data.Nat using (ℕ ; zero ; suc ; _≟_) public
import Data.List as L
open import Data.Maybe
open import Data.Product

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


-- The proof that a certain term is a value
data Value : Term -> Set where
  （） : Value （）
  True : Value True
  False : Value False
  Abs : (n : ℕ) (t : Term) -> Value (Abs n t)
  Id : (t : Term) -> Value (Id t) 
  Mac : ∀ {l : Label} (t : Term) -> Value (Mac l t)
  Res : ∀ {l : Label} (t : Term) -> Value (Res l t)

--------------------------------------------------------------------------------

-- Term substitution (as a function)
-- TODO Remove
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


-- Substs n t t₁ t₁' corresponds to t₁ [n / t] ≡ t₁' with the assumption that there are no name clashes.
data Subst (n : ℕ) (t : Term) : Term -> Term -> Set where

  （） : Subst n t （） （）

  True : Subst n t True True

  False : Subst n t False False

  Id : ∀ {t₁ t₁'} -> Subst n t t₁ t₁' -> Subst n t (Id t₁) (Id t₁')

  unId : ∀ {t₁ t₁'} -> Subst n t t₁ t₁' -> Subst n t (unId t₁) (unId t₁')

  Var : Subst n t (Var n) t
  
  Var' : ∀ {m} -> n ≢ m -> Subst n t (Var m) (Var m)
  
  Abs : ∀ {m t₁ t₁'} -> n ≢ m -> Subst n t t₁ t₁'
                              -> Subst n t (Abs m t₁) (Abs m t₁')
  
  App : ∀ {t₁ t₁' t₂ t₂'} -> Subst n t t₁ t₁' -> Subst n t t₂ t₂'
                          -> Subst n t (App t₁ t₂) (App t₁ t₂')
                                                
  If_Then_Else_ : ∀ {t₁ t₁' t₂ t₂' t₃ t₃'} -> Subst n t t₁ t₁'
                                           -> Subst n t t₂ t₂'
                                           -> Subst n t t₃ t₃'
                                           -> Subst n t (If t₁ Then t₂ Else t₃) (If t₁' Then t₂' Else t₃')
  Return : ∀ {t₁ t₁' l} -> Subst n t t₁ t₁'
                        -> Subst n t (Return l t₁) (Return l t₁')

  Bind : ∀ {t₁ t₁' t₂ t₂' l} -> Subst n t t₁ t₁' -> Subst n t t₂ t₂'
                             -> Subst n t (Bind l t₁ t₂) (Bind l t₂ t₂')

  Mac : ∀ {t₁ t₁' l} -> Subst n t t₁ t₁' -> Subst n t (Mac l t₁) (Mac l t₁')

  Res : ∀ {t₁ t₁' l} -> Subst n t t₁ t₁' -> Subst n t (Res l t₁) (Res l t₁')
  
  label : ∀ {t₁ t₁' l h} {p : l ⊑ h} -> Subst n t t₁ t₁'
                                     -> Subst n t (label p t₁) (label p t₁')

  label∙ : ∀ {t₁ t₁' l h} {p : l ⊑ h} -> Subst n t t₁ t₁'
                                      -> Subst n t (label∙ p t₁) (label∙ p t₁')

  unlabel : ∀ {t₁ t₁' l h} {p : l ⊑ h} -> Subst n t t₁ t₁'
                                       -> Subst n t (unlabel p t₁) (unlabel p t₁')

  fork :  ∀ {t₁ t₁' l h} {p : l ⊑ h} -> Subst n t t₁ t₁'
                                     -> Subst n t (fork p t₁) (fork p t₁')

  deepDup : ∀ {m} -> Subst n t (deepDup m) (deepDup m) -- m is free

  ∙ : Subst n t ∙ ∙

-- Substs t ns ns' t' applies the substitution t [ n / Var n' ] consecutively
-- for every n ∈ ns and n' ∈ ns' and returns the resulting term t'
data Substs (t₁ : Term) : List ℕ -> List ℕ -> Term -> Set where
  [] : Substs t₁ [] [] t₁
  _∷_ : ∀ {t₂ t₃ n n' ns ns'} -> Subst n (Var n') t₁ t₂ -> Substs t₂ ns ns' t₃
                              -> Substs t₁ (n ∷ ns) (n' ∷ ns') t₃ 

--------------------------------------------------------------------------------

-- A heap is a partial mapping from number (position) to terms.
data Heap : Set where
 [] : Heap
 _∷_ : Maybe (Label × Term) -> Heap -> Heap

-- Continuation 
data Cont : Set where
 Var : ℕ -> Cont
 # : Label -> ℕ -> Cont
 Then_Else_ : Term -> Term -> Cont
 Bind : Label -> Term -> Cont
 unlabel : ∀ {l h} -> l ⊑ h -> Cont
 unId : Cont

-- Just a list of continuation with a fixed label
data Stack (l : Label) : Set where
 [] : Stack l
 _∷_ : Cont -> Stack l -> Stack l

--------------------------------------------------------------------------------

-- Selstof's Abstract Lazy Machine State
-- The state is labeled to keep track of the security level of the
-- term (thread) executed.
record State (l : Label) : Set where
 constructor ⟨_,_,_⟩
 field
   heap : Heap
   term : Term
   stack : Stack l

open State
