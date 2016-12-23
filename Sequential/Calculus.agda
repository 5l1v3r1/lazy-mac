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

-- Term substitution
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

-- Selstof's Abstract Lazy Machine State
record State (l : Label) : Set where
 constructor ⟨_,_,_⟩
 field
   heap : Heap
   term : Term
   stack : Stack l

open State

--------------------------------------------------------------------------------
-- Operations on the heap (defined for ease of reasoning as data-types)

-- data Fresh : Heap -> ℕ -> Set where
--  [] : Fresh [] 0
--  _∷_ : ∀ {Γ n mt} -> Fresh Γ n -> Fresh (mt ∷ Γ) (suc n)

-- Extend a heap with a new binding
data Add (l : Label) (t : Term) : Heap -> ℕ -> Heap -> Set where
  here : Add l t [] 0 (just (l , t) ∷ [])
  next : ∀ {mt n Γ Γ'} -> Add l t Γ n Γ' -> Add l t (mt ∷ Γ) (suc n) (mt ∷ Γ')
  
_≔ᴬ_[_↦_] : Heap -> Heap -> ℕ -> (Label × Term) -> Set
Γ₂ ≔ᴬ Γ₁ [ n ↦ (l , t) ] = Add l t Γ₁ n Γ₂

data Remove (l : Label) (t : Term) : Heap -> ℕ -> Heap -> Set where
  here : ∀ {Γ} -> Remove l t (just (l , t) ∷ Γ) 0 (nothing ∷ Γ)
  next : ∀ {Γ Γ' mt n} -> Remove l t Γ n Γ' -> Remove l t (mt ∷ Γ) (suc n) (mt ∷ Γ')

_≔ᴿ_[_↦_]  : Heap -> Heap -> ℕ -> Label × Term -> Set
Γ ≔ᴿ Γ' [ n ↦ (l , t) ] = Remove l t Γ' n Γ 

-- Writes to an empty position
data Put (l : Label) (t : Term) : Heap -> ℕ -> Heap -> Set where
  here : ∀ {Γ} -> Put l t (nothing ∷ Γ) 0 ((just (l , t)) ∷ Γ)
  next : ∀ {Γ Γ' mt n} -> Put l t Γ n Γ' -> Put l t (mt ∷ Γ) (suc n) (mt ∷ Γ')

_≔ᴾ_[_↦_] : Heap -> Heap -> ℕ -> Label × Term -> Set
Γ' ≔ᴾ Γ [ n ↦ (l , t) ] = Put l t Γ n Γ'

data Member (l : Label) (t : Term) : ℕ -> Heap -> Set where
  here : ∀ {Γ} -> Member l t 0 ((just (l , t)) ∷ Γ)
  next : ∀ {Γ mt n} -> Member l t n Γ -> Member l t (suc n) (mt ∷ Γ)

_↦_∈_ : ℕ -> (Label × Term) -> Heap -> Set
n ↦ (l , t) ∈ Γ = Member l t n Γ

--------------------------------------------------------------------------------
-- DeepDup helper functions and data types

open import Data.Bool using (not)
open import Data.List using (filter)
open import Relation.Nullary.Decidable using (⌊_⌋)

ufv : Term -> List ℕ
ufv （） = []
ufv True = []
ufv False = []
ufv (Id t) = ufv t
ufv (unId t) = ufv t
ufv (Var x) = x ∷ []
ufv (Abs n t) = filter (λ m → not ⌊ n ≟ m ⌋) (ufv t)
ufv (App t t₁) = ufv t ++ ufv t₁
ufv (If t Then t₁ Else t₂) = ufv t ++ ufv t₁ ++ ufv t₂
ufv (Return l t) = ufv t
ufv (Bind l t t₁) = ufv t ++ ufv t₁
ufv (Mac l t) = ufv t
ufv (Res l t) = ufv t
ufv (label l⊑h t) = ufv t
ufv (label∙ l⊑h t) = ufv t
ufv (unlabel l⊑h t) = ufv t
ufv (fork l⊑h t) = ufv t
ufv (deepDup x) = [] -- Unguarded
ufv ∙ = []

-- Unguareded Free Variables (we might need this as a data type)
data UFV : Term -> List ℕ -> Set where


-- Extends the heap with x ↦ deepDup x' for each variable
data DeepDupHeap (l : Label) : Heap -> List ℕ -> List ℕ -> Heap -> Set where
  done : ∀ {Γ} -> DeepDupHeap l Γ [] [] Γ
  addNext : ∀ {Γ₁ Γ₂ Γ₃ n n' ns ns'} -> Γ₂ ≔ᴬ Γ₁ [ n' ↦ (l , deepDup n) ]
                                     -> DeepDupHeap l Γ₂ ns ns' Γ₃
                                     -> DeepDupHeap l Γ₁ (n ∷ ns) (n' ∷ ns') Γ₃

_≔ᴰ_[_↦_] : Heap -> Heap -> List ℕ -> Label × List ℕ -> Set
Γ' ≔ᴰ Γ [ ns' ↦ (l , ns) ] = DeepDupHeap l Γ ns ns' Γ'

-- Corresponds _[_/_] with the assumption that there are no name clashes in Abs.
data Subst (n : ℕ) (t : Term) : Term -> Term -> Set where
  （） : Subst n t （） （）
  True : Subst n t True True
  False : Subst n t False False
  Id : ∀ {t₁ t₁'} -> Subst n t t₁ t₁' -> Subst n t (Id t₁) (Id t₁')
  unId : ∀ {t₁ t₁'} -> Subst n t t₁ t₁' -> Subst n t (unId t₁) (unId t₁')
  Var : Subst n t (Var n) t
  Var' : ∀ {m} -> n ≢ m -> Subst n t (Var m) (Var m)
  Abs : ∀ {m t₁ t₁'} -> n ≢ m -> Subst n t t₁ t₁' -> Subst n t (Abs m t₁) (Abs m t₁')
  App : ∀ {t₁ t₁' t₂ t₂'} -> Subst n t t₁ t₁' -> Subst n t t₂ t₂' -> Subst n t (App t₁ t₂) (App t₁ t₂')
  If_Then_Else_ : ∀ {t₁ t₁' t₂ t₂' t₃ t₃'} -> Subst n t t₁ t₁'
                                           -> Subst n t t₂ t₂'
                                           -> Subst n t t₃ t₃'
                                           -> Subst n t (If t₁ Then t₂ Else t₃) (If t₁' Then t₂' Else t₃')
  Return : ∀ {t₁ t₁' l} -> Subst n t t₁ t₁' -> Subst n t (Return l t₁) (Return l t₁')
  Bind : ∀ {t₁ t₁' t₂ t₂' l} -> Subst n t t₁ t₁' -> Subst n t t₂ t₂' -> Subst n t (Bind l t₁ t₂) (Bind l t₂ t₂')
  Mac : ∀ {t₁ t₁' l} -> Subst n t t₁ t₁' -> Subst n t (Mac l t₁) (Mac l t₁')
  Res : ∀ {t₁ t₁' l} -> Subst n t t₁ t₁' -> Subst n t (Res l t₁) (Res l t₁')
  label : ∀ {t₁ t₁' l h} {p : l ⊑ h} -> Subst n t t₁ t₁' -> Subst n t (label p t₁) (label p t₁')
  label∙ : ∀ {t₁ t₁' l h} {p : l ⊑ h} -> Subst n t t₁ t₁' -> Subst n t (label∙ p t₁) (label∙ p t₁')
  unlabel : ∀ {t₁ t₁' l h} {p : l ⊑ h} -> Subst n t t₁ t₁' -> Subst n t (unlabel p t₁) (unlabel p t₁')
  fork :  ∀ {t₁ t₁' l h} {p : l ⊑ h} -> Subst n t t₁ t₁' -> Subst n t (fork p t₁) (fork p t₁')
  deepDup : ∀ {m} -> Subst n t (deepDup m) (deepDup m) -- m is free
  ∙ : Subst n t ∙ ∙

-- Multiple substitutions
data Substs (t₁ : Term) : List ℕ -> List ℕ -> Term -> Set where
  [] : Substs t₁ [] [] t₁
  _∷_ : ∀ {t₂ t₃ n n' ns ns'} -> Subst n (Var n') t₁ t₂ -> Substs t₂ ns ns' t₃ -> Substs t₁ (n ∷ ns) (n' ∷ ns') t₃ 

--------------------------------------------------------------------------------

data _⇝_ {l : Label} : State l -> State l -> Set where
 App₁ : ∀ {Γ Γ' S t₁ t₂ n} -> Γ' ≔ᴬ Γ [ n ↦ (l , t₂) ]
                           -> ⟨ Γ , App t₁ t₂ , S ⟩ ⇝ ⟨ Γ' , t₁ , Var n ∷ S ⟩

 App₂ : ∀ {Γ n m t t' S} -> Subst m (Var n) t t' -> ⟨ Γ , Abs m t , Var n ∷ S ⟩ ⇝ ⟨ Γ , t' , S ⟩
 
 Var₁ : ∀ {Γ Γ' n t S l'} -> ¬ (Value t)
                          -> Γ ≔ᴿ Γ' [ n ↦ (l' , t) ]
                          -> ⟨ Γ' , Var n , S ⟩ ⇝ ⟨ Γ , t , (# l n) ∷ S ⟩

 Var₁' : ∀ {Γ Γ' n v S l'} -> Value v
                           -> n ↦ (l' , v) ∈ Γ
                           -> ⟨ Γ' , Var n , S ⟩ ⇝ ⟨ Γ , v , S ⟩

 Var₂ : ∀ {Γ Γ' n v S} -> Γ' ≔ᴾ Γ [ n ↦ (l , v) ]
                       -> Value v
                       -> ⟨ Γ , v , (# l n) ∷ S ⟩ ⇝ ⟨ Γ' , v , S ⟩

 If : ∀ {Γ t₁ t₂ t₃ S} -> ⟨ Γ , (If t₁ Then t₂ Else t₃) , S ⟩ ⇝ ⟨ Γ , t₁ , (Then t₂ Else t₃) ∷ S ⟩
 IfTrue : ∀ {Γ t₂ t₃ S} -> ⟨ Γ , True , (Then t₂ Else t₃) ∷ S ⟩ ⇝ ⟨ Γ , t₂ , S ⟩
 IfFalse : ∀ {Γ t₂ t₃ S} -> ⟨ Γ , False , (Then t₂ Else t₃) ∷ S ⟩ ⇝ ⟨ Γ , t₃ , S ⟩

 Return : ∀ {Γ t S} -> ⟨ Γ , Return l t , S ⟩ ⇝ ⟨ Γ , Mac l t , S ⟩
 Bind₁ : ∀ {Γ t₁ t₂ S} -> ⟨ Γ , Bind l t₁ t₂ , S ⟩ ⇝ ⟨ Γ , t₁ , (Bind l t₂ ∷ S ) ⟩
 Bind₂ : ∀ {Γ t₁ t₂ S} -> ⟨ Γ , Mac l t₁ , Bind l t₂ ∷ S ⟩ ⇝ ⟨ Γ , App t₂ t₁ , S  ⟩

 Label' : ∀ {Γ t S h} -> (p : l ⊑ h) -> ⟨ Γ , label p t , S ⟩ ⇝ ⟨ Γ , (Return l (Res h (Id t))) , S ⟩

 Unlabel₁ : ∀ {Γ t S l'} -> (p : l' ⊑ l) -> ⟨ Γ , unlabel p t , S ⟩ ⇝ ⟨ Γ , t , unlabel p ∷ S ⟩
 Unlabel₂ : ∀ {Γ t S l'} -> (p : l' ⊑ l) -> ⟨ Γ , Res l t , unlabel p ∷ S ⟩ ⇝ ⟨ Γ , t , unId ∷ S ⟩

 UnId₁ : ∀ {Γ t S} -> ⟨ Γ , unId t , S ⟩ ⇝ ⟨ Γ , t , unId ∷ S ⟩ 
 UnId₂ : ∀ {Γ t S} -> ⟨ Γ , Id t , unId ∷ S ⟩ ⇝ ⟨ Γ , t , S ⟩ 

 Fork : ∀ {Γ t S h} -> (p : l ⊑ h) -> ⟨ Γ , (fork p t) , S ⟩ ⇝ ⟨ Γ , Return l t , S ⟩ 

 Hole : ∀ {Γ S} -> ⟨ Γ , ∙ , S ⟩ ⇝ ⟨ Γ , ∙ , S ⟩

 DeepDup : ∀ {Γ₁ Γ₂ Γ₃ Γ n n' ns' S l' t t'} -> n ↦ (l' , t) ∈ Γ
                                -> Substs t (ufv t) ns' t'
                                -> Γ₂ ≔ᴰ Γ₁ [ ns' ↦ (l , ufv t) ]
                                -> Γ₃ ≔ᴬ Γ₂ [ n' ↦ (l , t') ]
                                -> ⟨ Γ₁ , (deepDup n) , S ⟩ ⇝ ⟨ Γ₃ , Var n' , S ⟩
