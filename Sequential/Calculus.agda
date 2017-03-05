import Lattice as L

module Sequential.Calculus (𝓛 : L.Lattice) where

open import Types 𝓛

open import Data.Maybe hiding (All)
open import Relation.Binary.PropositionalEquality hiding ([_] ; subst)
open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Data.Nat renaming ( _≟_ to  _≟ᴺ_ )

open import Data.Product
open import Function
open import Data.Empty
open import Relation.Nullary

-- The basic Term π τ is a term that has type τ in the context π
data Term (π : Context) : Ty -> Set where

  （） : Term π （）

  True : Term π Bool
  False : Term π Bool

  Id : ∀ {τ} -> Term π τ -> Term π (Id τ)
  unId : ∀ {τ} -> Term π (Id τ) -> Term π τ

  -- The label represents in which (labeled) environment the variable points to
  -- The user is not supposed to give explicit labels, rather the semantics
  -- takes care of adding them as needed.
  Var : ∀ {l} {τ} ->  (τ∈π : τ ∈⟨ l ⟩ᴿ π) -> Term π τ
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

  read : ∀ {l h τ} -> l ⊑ h -> Term π (Ref l τ) -> Term π (Mac h τ)

  write : ∀ {l h τ} -> l ⊑ h -> Term π (Ref h τ) -> Term π τ -> Term π (Mac l （）)
  write∙ : ∀ {l h τ} -> l ⊑ h -> Term π (Ref h τ) -> Term π τ -> Term π (Mac l （）)

  new : ∀ {l h τ} -> l ⊑ h -> Term π τ -> Term π (Mac l (Ref h τ))
  new∙ : ∀ {l h τ} -> l ⊑ h -> Term π τ -> Term π (Mac l (Ref h τ))

  -- Here terms are supposed to be variables
  -- We use terms to avoid complicating the substitution lemma.
  #[_] :  ∀ {τ} -> ℕ -> Term π (Addr τ)
  #[_]ᴰ : ∀ {τ} -> ℕ -> Term π (Addr τ)  -- Duplicate on read

  -- Concurrency
  fork : ∀ {l h} -> (l⊑h : l ⊑ h) -> Term π (Mac h  （）) -> Term π (Mac l  （）)
  fork∙ : ∀ {l h} -> (l⊑h : l ⊑ h) -> Term π (Mac h  （）) -> Term π (Mac l  （）)

  deepDup : ∀ {τ} -> Term π τ -> Term π τ

  -- Represent sensitive information that has been erased.
  ∙ : ∀ {{τ}} -> Term π τ

infixl 3 #[_]
infixl 3 #[_]ᴰ

-- The proof that a certain term is a value
data Value {π : Context} : ∀ {τ} -> Term π τ -> Set where
  （） : Value （）
  True : Value True
  False : Value False
  Abs : ∀ {α β} (t : Term (α ∷ π) β) -> Value (Abs t)
  Id : ∀ {τ} (t : Term π τ) -> Value (Id t)
  Mac : ∀ {l : Label} {τ} (t : Term π τ) -> Value (Mac l t)
  Res : ∀ {l : Label} {τ} (t : Term π τ) -> Value (Res l t)
  #[_] : ∀ {τ} -> (n : ℕ) -> Value {τ = Addr τ} #[ n ]
  #[_]ᴰ : ∀ {τ} -> (n : ℕ) -> Value {τ = Addr τ} #[ n ]ᴰ

--------------------------------------------------------------------------------

-- The context of a term can be extended without harm
wken : ∀ {τ} {Δ₁ : Context} {Δ₂ : Context} -> Term Δ₁ τ -> Δ₁ ⊆ Δ₂ -> Term Δ₂ τ
wken （） p = （）
wken True p = True
wken False p = False
wken (Id t) p = Id (wken t p)
wken (unId t) p = unId (wken t p)
wken (Var {l = l} ⟪ τ∈π ⟫) p = Var {l = l} ⟪ wken-∈ᴿ p τ∈π ⟫
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
wken (read x t) p = read x (wken t p)
wken (write x t t₁) p = write x (wken t p) (wken t₁ p)
wken (write∙ x t t₁) p = write∙ x (wken t p) (wken t₁ p)
wken (new x t) p = new x (wken t p)
wken (new∙ x t) p = new∙ x (wken t p)
wken (#[ n ]) p = #[ n ]
wken (#[ n ]ᴰ) p = #[ n ]ᴰ
wken (fork x t) p = fork x (wken t p)
wken (fork∙ x t) p = fork∙ x (wken t p)
wken (deepDup x) p = deepDup (wken x p)
wken ∙ p = ∙

_↑¹ : ∀ {α β} {Δ : Context} -> Term Δ α -> Term (β ∷ Δ) α
t ↑¹ = wken t (drop refl-⊆)

-- Performs the variable-term substitution.
var-subst : ∀ {l α β} (Δ₁ : Context) (Δ₂ : Context)
            -> Term Δ₂ β -> α ∈⟨ l ⟩ (Δ₁ ++ [ β ] ++ Δ₂) -> Term (Δ₁ ++ Δ₂) α
var-subst [] Δ₂ v ⟪ here ⟫ = v
var-subst {l} [] Δ₂ v ⟪ there p ⟫ = Var {l = l} ⟪ ∈-∈ᴿ p ⟫
var-subst {l} {α} (._ ∷ Δ₁) Δ₂ v ⟪ here ⟫ = Var {l = l} ⟪ ∈-∈ᴿ {_} {α} {α ∷ Δ₁ ++ Δ₂} here ⟫
var-subst {l} (x ∷ Δ₁) Δ₂ v ⟪ there p ⟫ = (var-subst {l} Δ₁ Δ₂ v ⟪ p ⟫) ↑¹

tm-subst : ∀ {τ α} (Δ₁ : Context) (Δ₂ : Context)-> Term Δ₂ α -> Term (Δ₁ ++ [ α ] ++ Δ₂) τ -> Term (Δ₁ ++ Δ₂) τ
tm-subst Δ₁ Δ₂ v （） = （）
tm-subst Δ₁ Δ₂ v True = True
tm-subst Δ₁ Δ₂ v False = False
tm-subst Δ₁ Δ₂ v (Id t) = Id (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (unId t) = unId (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (Var {l = l} ⟪ y∈π ⟫) = var-subst {l = l} Δ₁ Δ₂ v ⟪ ∈ᴿ-∈ y∈π ⟫
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
tm-subst Δ₁ Δ₂ v (read x t) = read x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (write x t t₁) = write x (tm-subst Δ₁ Δ₂ v t) (tm-subst Δ₁ Δ₂ v t₁)
tm-subst Δ₁ Δ₂ v (write∙ x t t₁) = write∙ x (tm-subst Δ₁ Δ₂ v t) (tm-subst Δ₁ Δ₂ v t₁)
tm-subst Δ₁ Δ₂ v (new x t) = new x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (new∙ x t) = new∙ x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (#[ n ]) = #[ n ]
tm-subst Δ₁ Δ₂ v (#[ n ]ᴰ) = #[ n ]ᴰ
tm-subst Δ₁ Δ₂ v (fork x t) = fork x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (fork∙ x t) = fork∙ x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (deepDup x) = deepDup (tm-subst Δ₁ Δ₂ v x)
tm-subst Δ₁ Δ₂ v ∙ = ∙

subst : ∀ {α β} {Δ : Context} -> Term Δ α -> Term (α ∷ Δ) β -> Term Δ β
subst {Δ = Δ} v t = tm-subst [] Δ v t

--------------------------------------------------------------------------------

-- A Well-Typed continuation (Cont), contains well-typed terms and
-- transform the input type (first indexed) in the output type (second
-- index).
data Cont (l : Label) (π : Context) : Ty -> Ty -> Set where
 Var : ∀ {τ₁ τ₂} -> (τ∈π : τ₁ ∈⟨ l ⟩ᴿ π) -> Cont l π (τ₁ => τ₂) τ₂
 # : ∀ {τ} -> (τ∈π : τ ∈⟨ l ⟩ᴿ π)  -> Cont l π τ τ
 Then_Else_ : ∀ {τ} -> Term π τ -> Term π τ -> Cont l π Bool τ
 Bind :  ∀ {τ₁ τ₂} -> Term π (τ₁ => Mac l τ₂) -> Cont l π (Mac l τ₁) (Mac l τ₂)
 unlabel : ∀ {l' τ} (p : l' ⊑ l) -> Cont l π (Labeled l' τ) (Mac l τ)
 unId : ∀ {τ} -> Cont l π (Id τ) τ
 write : ∀ {τ H} -> l ⊑ H -> (τ∈π : τ ∈⟨ l ⟩ᴿ π) -> Cont l π (Ref H τ) (Mac l （）)
 write∙ : ∀ {τ H} -> l ⊑ H -> (τ∈π : τ ∈⟨ l ⟩ᴿ π) -> Cont l π (Ref H τ) (Mac l （）)
 read : ∀ {τ L} -> L ⊑ l -> Cont l π (Ref L τ) (Mac l τ)

wkenᶜ : ∀ {l π₁ π₂ τ₁ τ₂} -> Cont l π₁ τ₁ τ₂ -> π₁ ⊆ π₂ -> Cont l π₂ τ₁ τ₂
wkenᶜ (Var ⟪ τ∈π ⟫) π₁⊆π₂ = Var ⟪ wken-∈ᴿ π₁⊆π₂ τ∈π ⟫
wkenᶜ (# ⟪ τ∈π ⟫) π₁⊆π₂ = # ⟪ wken-∈ᴿ π₁⊆π₂ τ∈π ⟫
wkenᶜ (Then x Else x₁) π₁⊆π₂ = Then (wken x π₁⊆π₂) Else (wken x₁ π₁⊆π₂)
wkenᶜ (Bind x) π₁⊆π₂ = Bind (wken x π₁⊆π₂)
wkenᶜ (unlabel p) π₁⊆π₂ = unlabel p
wkenᶜ unId π₁⊆π₂ = unId
wkenᶜ (write x ⟪ τ∈π ⟫) π₁⊆π₂ = write x ⟪ wken-∈ᴿ π₁⊆π₂ τ∈π ⟫
wkenᶜ (write∙ x ⟪ τ∈π ⟫) π₁⊆π₂ = write∙ x ⟪ wken-∈ᴿ π₁⊆π₂ τ∈π ⟫
wkenᶜ (read x) π₁⊆π₂ = read x

-- A Well-typed stack (Stack) contains well-typed terms and is indexed
-- by an input type and an output type.
-- It transforms the former in the latter according to the continuations.
-- TODO can parametrize the stack with π? (remember that π only grows)
data Stack (l : Label) (π : Context) : Ty -> Ty -> Set where
 [] : ∀ {τ} -> Stack l π τ τ
 _∷_ : ∀ {τ₁ τ₂ τ₃} -> (C : Cont l π τ₁ τ₂) (S : Stack l π τ₂ τ₃) -> Stack l π τ₁ τ₃
 ∙ : ∀ {τ} -> Stack l π τ τ

wkenˢ : ∀ {l π₁ π₂ τ₁ τ₂} -> Stack l π₁ τ₁ τ₂ -> π₁ ⊆ π₂ -> Stack l π₂ τ₁ τ₂
wkenˢ [] _ = []
wkenˢ (C ∷ S) π₁⊆π₂ = wkenᶜ C π₁⊆π₂ ∷ (wkenˢ S π₁⊆π₂)
wkenˢ ∙ _ = ∙

--------------------------------------------------------------------------------

data Heap (l : Label) : Context -> Set where
  [] : Heap l []
  _∷_ : ∀ {π τ} -> (t : Maybe (Term π τ)) (Δ : Heap l π) -> Heap l (τ ∷ π)
  ∙ : ∀ {{π}} -> Heap l π

wkenᴴ : ∀ {l π₁ π₂} -> Heap l π₁ -> π₁ ⊆ π₂ -> Heap l π₂
wkenᴴ [] base = []
wkenᴴ [] (drop x) = nothing ∷ wkenᴴ [] x
wkenᴴ (just t ∷ Δ) (cons x) = (just (wken t x)) ∷ (wkenᴴ Δ x)
wkenᴴ (nothing ∷ Δ) (cons x) = nothing ∷ wkenᴴ Δ x
wkenᴴ (t ∷ Δ) (drop x) = nothing ∷ wkenᴴ (t ∷ Δ) x
wkenᴴ ∙ x = ∙

data Updateᴴ {l π τ} (mt : Maybe (Term π τ)) : ∀ {π'} -> τ ∈⟨ l ⟩ π' -> Heap l π' -> Heap l π' -> Set where
  here : ∀ {Δ : Heap l π} {mt' : Maybe (Term _ τ)} -> Updateᴴ mt (⟪ here ⟫) (mt' ∷ Δ) (mt ∷ Δ)
  there : ∀ {π' τ'} {τ∈π' : τ ∈ π'} {Δ Δ' : Heap l π'} {mt' : Maybe (Term _ τ')} -> Updateᴴ mt (⟪ τ∈π' ⟫) Δ Δ' ->
            Updateᴴ mt (⟪ there τ∈π' ⟫) (mt' ∷ Δ) (mt' ∷ Δ')

_≔_[_↦_]ᴴ : ∀ {l τ} {π π' : Context} -> Heap l π' -> Heap l π' -> τ ∈⟨ l ⟩ᴿ π' -> Term π τ -> Set
Δ' ≔ Δ [ ⟪ τ∈π' ⟫ ↦ t ]ᴴ = Updateᴴ (just t) (⟪ ∈ᴿ-∈ τ∈π' ⟫) Δ Δ'

-- Syntatic sugar for removing a term from the environment.
-- The term is used only to fix its context π and avoid unsolved metas.
_≔_[_↛_]ᴴ : ∀ {l τ} {π π' : Context} -> Heap l π' -> Heap l π' -> τ ∈⟨ l ⟩ᴿ π' -> Term π τ -> Set
_≔_[_↛_]ᴴ {π = π} Δ' Δ ⟪ x ⟫ t = Updateᴴ {π = π} nothing (⟪ ∈ᴿ-∈ x ⟫) Δ Δ'

data Memberᴴ {l π τ} (mt : Maybe (Term π τ)) : ∀ {π'} -> τ ∈⟨ l ⟩ π' -> Heap l π' -> Set where
  here : ∀ {Δ : Heap l π} -> Memberᴴ mt (⟪ here ⟫) (mt ∷ Δ)
  there : ∀ {π' τ'} {τ∈π' : τ ∈ π'} {Δ : Heap l π'} {mt' : Maybe (Term _ τ')} -> Memberᴴ mt (⟪ τ∈π' ⟫) Δ -> Memberᴴ mt (⟪ there τ∈π' ⟫) (mt' ∷ Δ)

_↦_∈ᴴ_ : ∀ {l τ} {π π' : Context} -> τ ∈⟨ l ⟩ᴿ π' -> Term π τ -> Heap l π' -> Set
⟪ x ⟫ ↦ t ∈ᴴ Δ = Memberᴴ (just t) (⟪ ∈ᴿ-∈ x ⟫) Δ

--------------------------------------------------------------------------------

-- A labeled-typed memory cell, containing a pointer
-- at most at level l
data Cell (l : Label) (τ : Ty) : Set where
  ∥_,_∥  : ∀ {L} {{π}} -> (L⊑l : L ⊑ l) (τ∈π : τ ∈⟨ L ⟩ᴿ π) -> Cell l τ

-- A labeled memory keeps pointer to no more sensitive heaps
data Memory (l : Label) : Set where
  [] : Memory l
  _∷_ : ∀ {τ} -> (cᴸ : Cell l τ) (M : Memory l) -> Memory l
  ∙ : Memory l

data Lookupᴹ {l τ} (cᴸ : Cell l τ) : ℕ -> Memory l -> Set where
  here : ∀ {M} -> Lookupᴹ cᴸ 0 (cᴸ ∷ M)
  there : ∀ {M n τ'} {c₁ᴸ : Cell l τ'} -> Lookupᴹ cᴸ n M -> Lookupᴹ cᴸ (suc n) (c₁ᴸ ∷ M)

_↦_∈ᴹ_ : ∀ {l τ} -> ℕ -> Cell l τ -> Memory l -> Set
_↦_∈ᴹ_ n c M = Lookupᴹ c n M

data Writeᴹ {l τ} (cᴸ : Cell l τ) : ℕ -> Memory l -> Memory l -> Set where
  here : ∀ {M} {c₁ᴸ : Cell l τ} -> Writeᴹ cᴸ 0 (c₁ᴸ ∷ M) (cᴸ ∷  M)
  there : ∀ {M M' τ' n} {c₁ᴸ : Cell l τ'} -> Writeᴹ cᴸ n M M' -> Writeᴹ cᴸ (suc n) (c₁ᴸ ∷ M) (c₁ᴸ ∷ M')

_≔_[_↦_]ᴹ : ∀ {l τ} -> Memory l -> Memory l -> ℕ -> Cell l τ -> Set
_≔_[_↦_]ᴹ M' M n c = Writeᴹ c n M M'

newᴹ : ∀ {l τ} -> Cell l τ -> Memory l -> Memory l
newᴹ x [] = x ∷ []
newᴹ x (x₁ ∷ M) = x₁ ∷ newᴹ x M
newᴹ x ∙ = ∙

lengthᴹ : ∀ {l} -> Memory l -> ℕ
lengthᴹ [] = 0
lengthᴹ (x ∷ M) = suc (lengthᴹ M)
lengthᴹ ∙ = 0  -- We don't care when the memory is collapsed

--------------------------------------------------------------------------------

data Memories : List Label -> Set where
  [] : Memories []
  _∷_ : ∀ {l ls} {{u : Unique l ls}} -> (M : Memory l) (Ms : Memories ls) -> Memories (l ∷ ls)

-- This is defined as a data type rather than as a function to avoid having to existentially quantify π
-- and in order to simplify unification agains semantics rules.
data Memberˢ {l} (x : Memory l) : ∀ {ls} -> Memories ls -> Set where
  here : ∀ {ls} {u : Unique l ls} {Γ : Memories ls} -> Memberˢ x (x ∷ Γ)
  there : ∀ {ls' l'} {u : Unique l' ls'} {Γ : Memories ls'} {y : Memory l'} -> Memberˢ x Γ -> Memberˢ x (y ∷ Γ)

_↦_∈ˢ_ : ∀ {ls} -> (l : Label) -> Memory l -> Memories ls -> Set
l ↦ x ∈ˢ Γ = Memberˢ x Γ

data Updateˢ {l} (x : Memory l) : ∀ {ls} -> Memories ls -> Memories ls -> Set where
  here : ∀ {ls} {u : Unique l ls} {Γ : Memories ls} {x' : Memory l} -> Updateˢ x (x' ∷ Γ) (x ∷ Γ)
  there : ∀ {ls l'} {u : Unique l' ls} {Γ Γ' : Memories ls} {y : Memory l'} -> Updateˢ x Γ Γ' -> Updateˢ x (y ∷ Γ) (y ∷ Γ')

_≔_[_↦_]ˢ : ∀ {ls} -> Memories ls -> Memories ls -> (l : Label) -> Memory l -> Set
Γ' ≔ Γ [ l ↦ x ]ˢ = Updateˢ x Γ Γ'

memberˢ-∈ : ∀ {l ls} {x : Memory l} {Ms : Memories ls} -> l ↦ x ∈ˢ Ms -> l ∈ ls
memberˢ-∈ here = here
memberˢ-∈ (there x) = there (memberˢ-∈ x)

updateˢ-∈ : ∀ {l ls} {x : Memory l} {Ms Ms' : Memories ls} -> Ms' ≔ Ms [ l ↦ x ]ˢ -> l ∈ ls
updateˢ-∈ here = here
updateˢ-∈ (there x) = there (updateˢ-∈ x)

lookupˢ : ∀ {l ls} -> l ∈ ls -> Memories ls -> Memory l
lookupˢ here (M ∷ Ms) = M
lookupˢ (there l∈ls) (M ∷ Ms) = lookupˢ l∈ls Ms

lookup-∈ˢ : ∀ {l ls} -> (l∈ls : l ∈ ls) (Ms : Memories ls) -> l ↦ lookupˢ l∈ls Ms ∈ˢ Ms
lookup-∈ˢ here (M ∷ Ms) = here
lookup-∈ˢ (there x) (_ ∷ Ms) = there (lookup-∈ˢ x Ms)

lookupˢ-memberˢ-≡ : ∀ {l ls} {M : Memory l} {Ms : Memories ls} -> (l∈ls : l ∈ ls) -> l ↦ M ∈ˢ Ms ->  M ≡ lookupˢ l∈ls Ms
lookupˢ-memberˢ-≡ here here = refl
lookupˢ-memberˢ-≡ here (there {u = u} M∈Ms) = ⊥-elim (∈-not-unique (memberˢ-∈ M∈Ms) u)
lookupˢ-memberˢ-≡ (there l∈ls) (here {u = u}) = ⊥-elim (∈-not-unique l∈ls u)
lookupˢ-memberˢ-≡ (there l∈ls) (there M∈Ms) = lookupˢ-memberˢ-≡ l∈ls M∈Ms

lookupˢ-updateˢ-≡ : ∀ {l ls} {M : Memory l} {Ms₁ Ms₂ : Memories ls} -> (l∈ls : l ∈ ls) -> Ms₂ ≔ Ms₁ [ l ↦ M ]ˢ -> M ≡ lookupˢ l∈ls Ms₂
lookupˢ-updateˢ-≡ here here = refl
lookupˢ-updateˢ-≡ here (there {u = u} y₁) = ⊥-elim (∈-not-unique (updateˢ-∈ y₁) u)
lookupˢ-updateˢ-≡ (there x) (here {u = u}) = ⊥-elim (∈-not-unique x u)
lookupˢ-updateˢ-≡ (there x) (there y₁) = lookupˢ-updateˢ-≡ x y₁

--------------------------------------------------------------------------------

data Heap∙ (l : Label) : Set where
  ⟨_⟩ : ∀ {π} -> Heap l π -> Heap∙ l
  ∙ : Heap∙ l

data Heaps : List Label -> Set where
  [] : Heaps []
  _∷_ : ∀ {l ls} {{u : Unique l ls}} -> Heap∙ l -> Heaps ls -> Heaps (l ∷ ls)

-- This is defined as a data type rather than as a function to avoid having to existentially quantify π
-- and in order to simplify unification agains semantics rules.
data Memberᴱ {l} (x : Heap∙ l) : ∀ {ls} -> Heaps ls -> Set where
  here : ∀ {ls} {u : Unique l ls} {Γ : Heaps ls} -> Memberᴱ x (x ∷ Γ)
  there : ∀ {ls l'} {u : Unique l' ls} {Γ : Heaps ls} {y : Heap∙ l'} -> Memberᴱ x Γ -> Memberᴱ x (y ∷ Γ)

_↦_∈ᴱ_ : ∀ {ls} -> (l : Label) -> Heap∙ l -> Heaps ls -> Set
l ↦ x ∈ᴱ Γ = Memberᴱ x Γ

data Updateᴱ {l} (x : Heap∙ l) : ∀ {ls} -> Heaps ls -> Heaps ls -> Set where
  here : ∀ {ls} {u : Unique l ls} {Γ : Heaps ls} {x' : Heap∙ l} -> Updateᴱ x (x' ∷ Γ) (x ∷ Γ)
  there : ∀ {ls l'} {u : Unique l' ls} {Γ Γ' : Heaps ls} {y : Heap∙ l'} -> Updateᴱ x Γ Γ' -> Updateᴱ x (y ∷ Γ) (y ∷ Γ')

_≔_[_↦_]ᴱ : ∀ {ls} -> Heaps ls -> Heaps ls -> (l : Label) -> Heap∙ l -> Set
Γ' ≔ Γ [ l ↦ x ]ᴱ = Updateᴱ x Γ Γ'

memberᴱ-∈ : ∀ {l ls} {x : Heap∙ l} {Γ : Heaps ls} -> l ↦ x ∈ᴱ Γ -> l ∈ ls
memberᴱ-∈ here = here
memberᴱ-∈ (there x) = there (memberᴱ-∈ x)

updateᴱ-∈ : ∀ {l ls} {x : Heap∙ l} {Γ Γ' : Heaps ls} -> Γ' ≔ Γ [ l ↦ x ]ᴱ -> l ∈ ls
updateᴱ-∈ here = here
updateᴱ-∈ (there x) = there (updateᴱ-∈ x)

--------------------------------------------------------------------------------

-- Sestoft's Abstract Lazy Machine State
-- The state is labeled to keep track of the security level of the
-- term (thread) executed.

data State (l : Label) (τ : Ty) : Set where
  ⟨_,_,_⟩ : ∀ {τ'} {π : Context} -> (Δ : Heap l π) (t : Term π τ') (S : Stack l π τ' τ) -> State l τ
  ∙ : State l τ

-- Term + Stack / ∙
data TS∙ (l : Label) (τ : Ty) : Set where
  ⟨_,_⟩ : ∀ {π τ'} -> (t : Term π τ')(S : Stack l π τ' τ) -> TS∙ l τ
  ∙ : TS∙ l τ

-- Adds labeled memory and heap to a term and stack
record Program (l : Label) (ls : List Label) (τ : Ty) : Set where
  constructor ⟨_,_,_⟩
  field Ms : Memories ls
        Γ : Heaps ls
        TS : TS∙ l τ

open Program public

--------------------------------------------------------------------------------
-- DeepDup

-- A list of variables bound in context π
data Vars (π : Context) : Set where
  [] : Vars π
  _∷_ : ∀ {τ : Ty} -> (τ∈π : τ ∈ π) -> Vars π -> Vars π

data _∈ⱽ_ {τ π} (x : τ ∈ π) : Vars π -> Set where
  here : ∀ {vs} -> x ∈ⱽ (x ∷ vs)
  there : ∀ {τ' vs} {y : τ' ∈ π} -> x ∈ⱽ vs -> x ∈ⱽ (y ∷ vs)

data _≅ⱽ_ {π} {τ : Ty} (v : τ ∈ π) : ∀ {τ'} -> τ' ∈ π -> Set where
  refl : v ≅ⱽ v

_≟ⱽ_ : ∀ {π τ₁ τ₂} -> (v₁ : τ₁ ∈ π) (v₂ : τ₂ ∈ π) -> Dec (v₁ ≅ⱽ v₂)
here ≟ⱽ here = yes refl
here ≟ⱽ there y = no (λ ())
there x ≟ⱽ here = no (λ ())
there x ≟ⱽ there y with x ≟ⱽ y
there x ≟ⱽ there .x | yes refl = yes refl
there {τ} x ≟ⱽ there y | no ¬p = no (aux ¬p)
  where aux : ∀ {τ τ' τ'' π} {x : τ ∈ π} {y : τ' ∈ π} -> ¬ x ≅ⱽ y -> ¬ (there {τ' = τ''} x ≅ⱽ there y)
        aux ¬p₁ refl = ¬p₁ refl

memberⱽ : ∀ {τ π} -> (v : τ ∈ π) -> (vs : Vars π) -> Dec (v ∈ⱽ vs)
memberⱽ v [] = no (λ ())
memberⱽ v (v' ∷ vs) with v ≟ⱽ v'
memberⱽ v (.v ∷ vs) | yes refl = yes here
memberⱽ v (v' ∷ vs) | no ¬p with memberⱽ v vs
memberⱽ v (v' ∷ vs) | no ¬p | yes p = yes (there p)
memberⱽ v (v' ∷ vs) | no ¬p₁ | no ¬p = no (aux ¬p ¬p₁)
  where aux : ∀ {τ τ' π} {vs : Vars π} {x : τ ∈ π} {y : τ' ∈ π} -> ¬ (x ∈ⱽ vs) -> ¬ (x ≅ⱽ y) -> ¬ (x ∈ⱽ (y ∷ vs))
        aux x∉vs x≠y here = x≠y refl
        aux x∉vs x≠y (there x∈vs) = x∉vs x∈vs

mapⱽ : ∀ {π π'} -> (∀ {τ} -> τ ∈ π -> τ ∈ π') -> Vars π -> Vars π'
mapⱽ f [] = []
mapⱽ f (τ∈π ∷ vs) = (f τ∈π) ∷ (mapⱽ f vs)

-- dup-ufv vs t duplicates free unguarded variables (ufv), i.e.
-- it puts deepDup x for every free variable x, that is not in the scope of vs.
-- We keep track of the variables introduced by lambda-abstraction.
-- We do not duplicate terms that are already inside a deepDup.
dup-ufv : ∀ {π τ} -> Vars π -> Term π τ -> Term π τ
dup-ufv vs （） = （）
dup-ufv vs True = True
dup-ufv vs False = False
dup-ufv vs (Id t) = Id (dup-ufv vs t)
dup-ufv vs (unId t) = unId (dup-ufv vs t)
dup-ufv vs (Var ⟪ τ∈π ⟫) with memberⱽ (∈ᴿ-∈ τ∈π) vs
dup-ufv vs (Var {l = l} ⟪ τ∈π ⟫) | yes p = Var {l = l} ⟪ τ∈π ⟫  -- In scope
dup-ufv vs (Var {l = l} ⟪ τ∈π ⟫) | no ¬p = deepDup (Var {l = l} ⟪ τ∈π ⟫) -- Free
dup-ufv vs (Abs t) = Abs (dup-ufv (here ∷ mapⱽ there vs) t)
dup-ufv vs (App t t₁) = App (dup-ufv vs t) (dup-ufv vs t₁)
dup-ufv vs (If t Then t₁ Else t₂) = If (dup-ufv vs t) Then (dup-ufv vs t₁) Else (dup-ufv vs t₂)
dup-ufv vs (Return l t) = Return l (dup-ufv vs t)
dup-ufv vs (t >>= t₁) = (dup-ufv vs t) >>= (dup-ufv vs t₁)
dup-ufv vs (Mac l t) = Mac l (dup-ufv vs t)
dup-ufv vs (Res l t) = Res l (dup-ufv vs t)
dup-ufv vs (label l⊑h t) = label l⊑h (dup-ufv vs t)
dup-ufv vs (label∙ l⊑h t) = label∙ l⊑h (dup-ufv vs t)
dup-ufv vs (unlabel l⊑h t) = unlabel l⊑h (dup-ufv vs t)
dup-ufv vs(read l⊑h t) = read l⊑h (dup-ufv vs t)
dup-ufv vs (write l⊑h t₁ t₂) = write l⊑h (dup-ufv vs t₁) (dup-ufv vs t₂)
dup-ufv vs (write∙ l⊑h t₁ t₂) = write∙ l⊑h (dup-ufv vs t₁) (dup-ufv vs t₂)
dup-ufv vs (new l⊑h t) = new l⊑h (dup-ufv vs t)
dup-ufv vs (new∙ l⊑h t) = new∙ l⊑h (dup-ufv vs t)
dup-ufv vs (#[ n ]) = #[ n ]ᴰ  -- Duplicate on read!
dup-ufv vs (#[ n ]ᴰ) = #[ n ]ᴰ
dup-ufv vs (fork l⊑h t) = fork l⊑h (dup-ufv vs t)
dup-ufv vs (fork∙ l⊑h t) = fork∙ l⊑h (dup-ufv vs t)
dup-ufv vs (deepDup t) = deepDup t  -- deepDup (deepDup t) is semantically equal to deepDup t
dup-ufv vs ∙ = ∙

deepDupᵀ : ∀ {τ π} -> Term π τ -> Term π τ
deepDupᵀ t = dup-ufv [] t

-- The proof that a term is a variable
data IsVar {π} {τ} : Term π τ -> Set where
  Var : ∀ {l} -> (τ∈π : τ ∈⟨ l ⟩ᴿ π) -> IsVar (Var τ∈π)

data IsFork {π} : ∀ {τ} -> Term π τ -> Set where
  Fork : ∀ {l h} (p : l ⊑ h) (t : Term π (Mac h _)) -> IsFork (fork p t)
  Fork∙ : ∀ {l h} (p : l ⊑ h) (t : Term π (Mac h _)) -> IsFork (fork∙ p t)

isFork? : ∀ {π τ} (t : Term π τ) -> Dec (IsFork t)
isFork? （） = no (λ ())
isFork? True = no (λ ())
isFork? False = no (λ ())
isFork? (Id t) = no (λ ())
isFork? (unId t) = no (λ ())
isFork? (Var τ∈π) = no (λ ())
isFork? (Abs t) = no (λ ())
isFork? (App t t₁) = no (λ ())
isFork? (If t Then t₁ Else t₂) = no (λ ())
isFork? (Return l t) = no (λ ())
isFork? (t >>= t₁) = no (λ ())
isFork? (Mac l t) = no (λ ())
isFork? (Res l t) = no (λ ())
isFork? (label l⊑h t) = no (λ ())
isFork? (label∙ l⊑h t) = no (λ ())
isFork? (unlabel l⊑h t) = no (λ ())
isFork? (read x t) = no (λ ())
isFork? (write x t t₁) = no (λ ())
isFork? (write∙ x t t₁) = no (λ ())
isFork? (new x t) = no (λ ())
isFork? (new∙ x t) = no (λ ())
isFork? #[ x ] = no (λ ())
isFork? #[ x ]ᴰ = no (λ ())
isFork? (fork l⊑h t) = yes (Fork l⊑h t)
isFork? (fork∙ l⊑h t) = yes (Fork∙ l⊑h t)
isFork? (deepDup t) = no (λ ())
isFork? ∙ = no (λ ())
