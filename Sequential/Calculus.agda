open import Lattice

module Sequential.Calculus {- (𝓛 : Lattice) -} where

open import Types
open import Relation.Binary.PropositionalEquality hiding ([_] ; subst)
open import Data.List.All
open import Data.Nat using (ℕ ; zero ; suc) public
open import Data.Nat renaming ( _≟_ to _≟ᴺ_) 
import Data.List as L
open import Data.Maybe
open import Data.Product

record Variable : Set where
   constructor _,_
   field lbl : Label
         num : ℕ

open Variable public

open import Data.Sum

aux : ∀ {v₁ v₂ : Variable} -> (lbl v₁) ≢ (lbl v₂) ⊎ (num v₁) ≢ (num v₂) -> v₁ ≢ v₂
aux (inj₁ x) refl = x refl
aux (inj₂ y) refl = y refl

_≟ⱽ_ : (v₁ v₂ : Variable) -> Dec (v₁ ≡ v₂)
(lbl , num) ≟ⱽ (lbl₁ , num₁) with lbl ≟ᴸ lbl₁ | num ≟ᴺ num₁
(lbl , num) ≟ⱽ (.lbl , .num) | yes refl | yes refl = yes refl
(lbl , num) ≟ⱽ (lbl₁ , num₁) | yes p | no ¬p = no (aux (inj₂ ¬p))
(lbl , num) ≟ⱽ (lbl₁ , num₁) | no ¬p | yes p = no (aux (inj₁ ¬p))
(lbl , num) ≟ⱽ (lbl₁ , num₁) | no ¬p | no ¬p₁ = no (aux (inj₁ ¬p))


-- A label-annotated, untyped free term.
-- Variables are represented by numbers.
data Term : Set where
  （） : Term

  True : Term 
  False : Term

  Id : Term -> Term 
  unId : Term -> Term

  Var : Variable -> Term
  Abs : Variable -> Term -> Term  -- n is the name of the variable
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

  deepDup : Variable -> Term

  -- Represent sensitive information that has been erased.
  ∙ : Term


-- The proof that a certain term is a value
data Value : Term -> Set where
  （） : Value （）
  True : Value True
  False : Value False
  Abs : (x : Variable) (t : Term) -> Value (Abs x t)
  Id : (t : Term) -> Value (Id t) 
  Mac : ∀ {l : Label} (t : Term) -> Value (Mac l t)
  Res : ∀ {l : Label} (t : Term) -> Value (Res l t)

--------------------------------------------------------------------------------

-- Term substitution (as a function)
-- TODO Remove
_[_/_] : Term -> Term -> Variable -> Term
（） [ t₂ / x ] = （）
True [ t₂ / x ] = True
False [ t₂ / x ] = False
Id t₁ [ t₂ / x ] = Id (t₁ [ t₂ / x ])
unId t₁ [ t₂ / x ] = unId (t₁ [ t₂ / x ])
Var y [ t₂ / x ] with y ≟ⱽ x
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
data Subst (n : Variable) (t : Term) : Term -> Term -> Set where

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
data Substs (t₁ : Term) : List Variable -> List Variable -> Term -> Set where
  [] : Substs t₁ [] [] t₁
  _∷_ : ∀ {t₂ t₃ n n' ns ns'} -> Subst n (Var n') t₁ t₂ -> Substs t₂ ns ns' t₃
                              -> Substs t₁ (n ∷ ns) (n' ∷ ns') t₃ 

--------------------------------------------------------------------------------

Context : Set
Context = Variable -> Ty

_[_↦_]ᶜ : Context -> Variable -> Ty -> Context
_[_↦_]ᶜ π x τ y with x ≟ⱽ y
_[_↦_]ᶜ π x τ .x | yes refl = τ
_[_↦_]ᶜ π x τ y | no ¬p = π y

_↦_∈ᶜ_  : Variable -> Ty -> Context -> Set
x ↦ τ ∈ᶜ π = π x ≡ τ

-- A heap is a partial mapping from number (position) to terms.
Heap : Set
Heap = Variable -> Maybe Term

_[_↦_] : Heap -> Variable -> Maybe Term -> Heap
_[_↦_] Γ v₁ t v₂ with v₁ ≟ⱽ v₂
_[_↦_] Γ v₁ t .v₁ | yes refl = t
_[_↦_] Γ v₁ t v₂ | no ¬p = Γ v₂

_↦_∈_  : Variable -> Maybe Term -> Heap -> Set
x ↦ mt ∈ Γ = Γ x ≡ mt

fresh : Variable -> Heap -> Set
fresh x Γ = x ↦ nothing ∈ Γ

-- Continuation 
data Cont : Set where
 Var : Variable -> Cont
 # : Variable -> Cont
 Then_Else_ : Term -> Term -> Cont
 Bind : Label -> Term -> Cont
 unlabel : ∀ {l h} -> l ⊑ h -> Cont
 unId : Cont

-- Just a list of continuation with a fixed label
data Stack (l : Label) : Set where
 [] : Stack l
 _∷_ : Cont -> Stack l -> Stack l

--------------------------------------------------------------------------------

-- Sestoft's Abstract Lazy Machine State
-- The state is labeled to keep track of the security level of the
-- term (thread) executed.
record State (l : Label) : Set where
 constructor ⟨_,_,_⟩
 field
   heap : Heap
   term : Term
   stack : Stack l

open State public

--------------------------------------------------------------------------------

-- Typing Judgment

mutual

  data _⊢_∷_ (π : Context) : Term -> Ty -> Set where
    （） : π ⊢ （） ∷ （） 

    True : π ⊢ True ∷ Bool
    False : π ⊢ False ∷ Bool
    
    If_Then_Else_ : ∀ {t₁ t₂ t₃ τ} -> π ⊢ t₁ ∷ Bool
                                   -> π ⊢ t₂ ∷ τ
                                   -> π ⊢ t₃ ∷ τ
                                   -> π ⊢ If t₁ Then t₂ Else t₃ ∷ τ
                                   

    Id : ∀ {τ t} -> π ⊢ t ∷ τ -> π ⊢ Id t ∷ Id τ
    unId : ∀ {τ t} -> π ⊢ t ∷ Id τ -> π ⊢ unId t ∷ τ

    Var : ∀ {τ n} -> n ↦ τ ∈ᶜ π  -> π ⊢ Var n ∷ τ
    Abs : ∀ {n t τ₁ τ₂} -> π [ n ↦ τ₁ ]ᶜ ⊢ t ∷ τ₂ -> π ⊢ Abs n t ∷ (τ₁ => τ₂)    
    App : ∀ {t₁ t₂ τ₁ τ₂} -> π ⊢ t₁ ∷ (τ₁ => τ₂)
                          -> π ⊢ t₂ ∷ τ₁ -> π ⊢ App t₁ t₂ ∷ τ₂

    Mac : ∀ {l t τ} -> π ⊢ t ∷ τ -> π ⊢ Mac l t ∷ Mac l τ
    Return : ∀ {l t τ} -> π ⊢ t ∷ τ -> π ⊢ Return l t ∷ Mac l τ
    Bind : ∀ {l τ₁ τ₂ t₁ t₂} -> π ⊢ t₁ ∷ (Mac l τ₁) -> π ⊢ t₂ ∷ (τ₁ => Mac l τ₂) -> π ⊢ Bind l t₁ t₂ ∷ Mac l τ₂


    Res : ∀ {l t τ} -> π ⊢ t ∷ τ -> π ⊢ Res l t ∷ Res l τ
    label : ∀ {l h t τ} {l⊑h : l ⊑ h} -> π ⊢ t ∷ τ -> π ⊢ label l⊑h t ∷ Mac l (Labeled h τ)
    label∙ : ∀ {l h t τ} {l⊑h : l ⊑ h} -> π ⊢ t ∷ τ -> π ⊢ label∙ l⊑h t ∷ Mac l (Labeled h τ)
    unlabel : ∀ {l h t τ} {l⊑h : l ⊑ h} -> π ⊢ t ∷ Labeled l τ -> π ⊢ unlabel l⊑h t ∷ Mac h τ


    fork : ∀ {l h t} {l⊑h : l ⊑ h} -> π ⊢ t ∷ (Mac h  （） ) -> π ⊢ fork l⊑h t ∷ Mac l  （）

    deepDup : ∀ {τ n} -> n ↦ τ ∈ᶜ π -> π ⊢ deepDup n ∷ τ

    ∙ : ∀ {τ} -> π ⊢ ∙ ∷ τ

  data ⊢ᴴ_∷_ (Γ : Heap) (π : Context) : Set where
    just : ∀ {x t} -> (x∈Γ : x ↦ just t ∈ Γ) -> (t-τ : π ⊢ t ∷ π x) -> ⊢ᴴ Γ ∷ π     
    -- nothing : ∀ {x} -> x ↦ nothing ∈ Γ -> ⊢ᴴ Γ ∷ π    -- Do we need this?

-- A Well-Typed continuation (WCont), contains well-typed terms and
-- transform the input type (first indexed) in the output type (second
-- index).
data WCont (π : Context) : Ty -> Cont -> Ty -> Set where
 unId : ∀ {τ} -> WCont π (Id τ) unId τ
 unlabel : ∀ {l h τ} -> (l⊑h : l ⊑ h) -> WCont π (Labeled l τ) (unlabel l⊑h) (Mac h τ)
 Then_Else_ : ∀ {τ t₂ t₃} -> (wt-t₂ : π ⊢ t₂ ∷ τ)  -> (wt-t₃ : π ⊢ t₃ ∷ τ) ->  WCont π Bool (Then t₂ Else t₃) τ
 Var : ∀ {τ₁ τ₂ n} -> (wt-n : π ⊢ Var n ∷ τ₁) -> WCont π (τ₁ => τ₂) (Var n) τ₂
 # : ∀ {τ x} -> π ⊢ Var x ∷ τ -> WCont π τ (# x) τ 
 Bind : ∀ {l τ₁ τ₂ t₂} -> (wt-t₂ : π ⊢ t₂ ∷ (τ₁ => Mac l τ₂)) ->  WCont π (Mac l τ₁) (Bind l t₂) (Mac l τ₂)

-- A Well-typed stack (WStack) contains well-typed terms and is indexed
-- by an input type and an output type.
-- It transforms the former in the latter according to the continuations.
data WStack {l} (π : Context) : Ty -> Stack l -> Ty -> Set where
 [] : ∀ {τ} -> WStack π τ [] τ
 _∷_ : ∀ {τ₁ τ₂ τ₃ c S} -> (wt-c : WCont π τ₁ c τ₂) (wt-S : WStack π τ₂ S τ₃) -> WStack π τ₁ (c ∷ S) τ₃

data ⊢ˢ_∷_ {l : Label} : State l -> Ty -> Set where
  ⟨_,_,_⟩ : ∀ {π Γ t τ τ' S} -> ⊢ᴴ Γ ∷ π
                             -> π ⊢ t ∷ τ
                             -> WStack π τ S τ' -> ⊢ˢ ⟨ Γ , t , S ⟩ ∷ τ'
