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

  -- The label represents in which (labeled) environment the variable points to
  -- The user is not supposed to give explicit labels, rather the semantics
  -- takes care of adding them as needed.
  Var : ∀ {{l}} {τ} ->  (τ∈π : τ ∈⟨ l ⟩ᴿ π) -> Term π τ
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
  #[_] :  ℕ -> Term π Addr
  #[_]ᴰ : ℕ -> Term π Addr  -- Duplicate on read

  -- Concurrency
  fork : ∀ {l h} -> (l⊑h : l ⊑ h) -> Term π (Mac h  （）) -> Term π (Mac l  （）)

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
  #[_] : (n : ℕ) -> Value #[ n ]
  #[_]ᴰ : (n : ℕ) -> Value #[ n ]ᴰ

--------------------------------------------------------------------------------

-- The context of a term can be extended without harm
wken : ∀ {τ} {Δ₁ : Context} {Δ₂ : Context} -> Term Δ₁ τ -> Δ₁ ⊆ˡ Δ₂ -> Term Δ₂ τ
wken （） p = （）
wken True p = True
wken False p = False
wken (Id t) p = Id (wken t p)
wken (unId t) p = unId (wken t p)
wken (Var ⟪ τ∈π ⟫) p = Var ⟪ wken-∈ᴿ p τ∈π ⟫
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
wken (deepDup x) p = deepDup (wken x p)
wken ∙ p = ∙

_↑¹ : ∀ {α β} {Δ : Context} -> Term Δ α -> Term (β ∷ Δ) α
t ↑¹ = wken t (drop refl-⊆ˡ)

-- Performs the variable-term substitution.
var-subst : ∀ {α β} {{l}} (Δ₁ : Context) (Δ₂ : Context)
            -> Term Δ₂ β -> α ∈⟨ l ⟩ (Δ₁ ++ [ β ] ++ Δ₂) -> Term (Δ₁ ++ Δ₂) α
var-subst [] Δ₂ v ⟪ here ⟫ = v
var-subst [] Δ₂ v ⟪ there p ⟫ = Var ⟪ ∈-∈ᴿ p ⟫
var-subst {α} (._ ∷ Δ₁) Δ₂ v ⟪ here ⟫ = Var ⟪ ∈-∈ᴿ {α} {α ∷ Δ₁ ++ Δ₂} here ⟫
var-subst (x ∷ Δ₁) Δ₂ v ⟪ there p ⟫ = (var-subst Δ₁ Δ₂ v ⟪ p ⟫) ↑¹

tm-subst : ∀ {τ α} (Δ₁ : Context) (Δ₂ : Context)-> Term Δ₂ α -> Term (Δ₁ ++ [ α ] ++ Δ₂) τ -> Term (Δ₁ ++ Δ₂) τ
tm-subst Δ₁ Δ₂ v （） = （）
tm-subst Δ₁ Δ₂ v True = True
tm-subst Δ₁ Δ₂ v False = False
tm-subst Δ₁ Δ₂ v (Id t) = Id (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (unId t) = unId (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (Var ⟪ y∈π ⟫) = var-subst Δ₁ Δ₂ v ⟪ ∈ᴿ-∈ y∈π ⟫
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
tm-subst Δ₁ Δ₂ v (deepDup x) = deepDup (tm-subst Δ₁ Δ₂ v x)
tm-subst Δ₁ Δ₂ v ∙ = ∙

subst : ∀ {α β} {Δ : Context} -> Term Δ α -> Term (α ∷ Δ) β -> Term Δ β
subst {Δ = Δ} v t = tm-subst [] Δ v t

--------------------------------------------------------------------------------

-- A Well-Typed continuation (Cont), contains well-typed terms and
-- transform the input type (first indexed) in the output type (second
-- index).
data Cont (l : Label) : Ty -> Ty -> Set where
 Var : ∀ {τ₁ τ₂} {{π : Context}} -> (τ∈π : τ₁ ∈⟨ l ⟩ᴿ π) -> Cont l (τ₁ => τ₂) τ₂
 # : ∀ {τ} {{π : Context}} -> (τ∈π : τ ∈⟨ l ⟩ᴿ π)  -> Cont l τ τ
 Then_Else_ : ∀ {τ} {π : Context} -> Term π τ -> Term π τ -> Cont l Bool τ
 Bind :  ∀ {τ₁ τ₂} {π : Context} -> Term π (τ₁ => Mac l τ₂) -> Cont l (Mac l τ₁) (Mac l τ₂)
 unlabel : ∀ {l' τ} (p : l' ⊑ l) -> Cont l (Labeled l' τ) (Mac l τ)
 unId : ∀ {τ} -> Cont l (Id τ) τ
 write : ∀ {τ H} {{π : Context}} -> l ⊑ H -> (τ∈π : τ ∈⟨ l ⟩ᴿ π) -> Cont l (Ref H τ) (Mac l （）)
 write∙ : ∀ {τ H} {{π : Context}} -> l ⊑ H -> (τ∈π : τ ∈⟨ l ⟩ᴿ π) -> Cont l (Ref H τ) (Mac l （）)
 read : ∀ {τ L} -> L ⊑ l -> Cont l (Ref L τ) (Mac l τ)

-- A Well-typed stack (Stack) contains well-typed terms and is indexed
-- by an input type and an output type.
-- It transforms the former in the latter according to the continuations.
data Stack (l : Label) : Ty -> Ty -> Set where
 [] : ∀ {τ} -> Stack l τ τ
 _∷_ : ∀ {τ₁ τ₂ τ₃} -> Cont l τ₁ τ₂ -> Stack l τ₂ τ₃ -> Stack l τ₁ τ₃
 ∙ : ∀ {τ} -> Stack l τ τ
--------------------------------------------------------------------------------

data Env (l : Label) : Context -> Set where
  [] : Env l []
  _∷_ : ∀ {π τ} -> (t : Maybe (Term π τ)) -> Env l π -> Env l (τ ∷ π)
  ∙ : ∀ {{π}} -> Env l π

data Updateᴱ {l π τ} (mt : Maybe (Term π τ)) : ∀ {π'} -> τ ∈⟨ l ⟩ π' -> Env l π' -> Env l π' -> Set where
  here : ∀ {Δ : Env l π} {mt' : Maybe (Term _ τ)} -> Updateᴱ mt (⟪ here ⟫) (mt' ∷ Δ) (mt ∷ Δ)
  there : ∀ {π' τ'} {τ∈π' : τ ∈ π'} {Δ Δ' : Env l π'} {mt' : Maybe (Term _ τ')} -> Updateᴱ mt (⟪ τ∈π' ⟫) Δ Δ' ->
            Updateᴱ mt (⟪ there τ∈π' ⟫) (mt' ∷ Δ) (mt' ∷ Δ')

_≔_[_↦_]ᴱ : ∀ {l τ} {π π' : Context} -> Env l π' -> Env l π' -> τ ∈⟨ l ⟩ᴿ π' -> Term π τ -> Set
Δ' ≔ Δ [ ⟪ τ∈π' ⟫ ↦ t ]ᴱ = Updateᴱ (just t) (⟪ ∈ᴿ-∈ τ∈π' ⟫) Δ Δ'

-- Syntatic sugar for removing a term from the environment.
-- The term is used only to fix its context π and avoid unsolved metas.
_≔_[_↛_]ᴱ : ∀ {l τ} {π π' : Context} -> Env l π' -> Env l π' -> τ ∈⟨ l ⟩ᴿ π' -> Term π τ -> Set
_≔_[_↛_]ᴱ {π = π} Δ' Δ ⟪ x ⟫ t = Updateᴱ {π = π} nothing (⟪ ∈ᴿ-∈ x ⟫) Δ Δ'

data Memberᴱ {l π τ} (mt : Maybe (Term π τ)) : ∀ {π'} -> τ ∈⟨ l ⟩ π' -> Env l π' -> Set where
  here : ∀ {Δ : Env l π} -> Memberᴱ mt (⟪ here ⟫) (mt ∷ Δ)
  there : ∀ {π' τ'} {τ∈π' : τ ∈ π'} {Δ : Env l π'} {mt' : Maybe (Term _ τ')} -> Memberᴱ mt (⟪ τ∈π' ⟫) Δ -> Memberᴱ mt (⟪ there τ∈π' ⟫) (mt' ∷ Δ)

_↦_∈ᴱ_ : ∀ {l τ} {π π' : Context} -> τ ∈⟨ l ⟩ᴿ π' -> Term π τ -> Env l π' -> Set
⟪ x ⟫ ↦ t ∈ᴱ Δ = Memberᴱ (just t) (⟪ ∈ᴿ-∈ x ⟫) Δ

--------------------------------------------------------------------------------

-- A labeled-typed memory cell, containing a pointer
-- at most at level l
data Cell (l : Label) (τ : Ty) : Set where
  ∥_∥  : ∀ {L} {{π}} -> L ⊑ l × τ ∈⟨ L ⟩ᴿ π -> Cell l τ

-- A labeled memory keeps pointer to no more sensitive heaps
data Memory (l : Label) : Set where
  [] : Memory l
  _∷_ : ∀ {τ} -> (cᴸ : Cell l τ) (M : Memory l) -> Memory l
  ∙ : Memory l

data Memberᴹ {l τ} (cᴸ : Cell l τ) : ℕ -> Memory l -> Set where
  here : ∀ {M} -> Memberᴹ cᴸ 0 (cᴸ ∷ M)
  there : ∀ {M n τ'} {c₁ᴸ : Cell l τ'} -> Memberᴹ cᴸ n M -> Memberᴹ cᴸ (suc n) (c₁ᴸ ∷ M)

_↦_∈ᴹ_ : ∀ {l τ} -> ℕ -> Cell l τ -> Memory l -> Set
_↦_∈ᴹ_ n c M = Memberᴹ c n M

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
-- A heap pairs together labeled memories and environment

open import Data.List.All

Unique : Label -> List Label -> Set
Unique l₁ ls = All (λ l₂ → ¬ (l₁ ≡ l₂)) ls

∈-not-unique : ∀ {l ls} -> l ∈ ls -> Unique l ls -> ⊥
∈-not-unique here (px ∷ q) = ⊥-elim (px refl)
∈-not-unique (there p) (px ∷ q) = ∈-not-unique p q

data Heap : List Label -> Set where
  [] : Heap []
  _∷_ : ∀ {l ls π} {{u : Unique l ls}} -> Memory l × Env l π -> Heap ls -> Heap (l ∷ ls)

data Member {l} {π} (x : Memory l × Env l π) : ∀ {ls} -> Heap ls -> Set where
  here : ∀ {ls} {u : Unique l ls} {Γ : Heap ls} -> Member x (x ∷ Γ)
  there : ∀ {ls l' π'} {u : Unique l' ls} {Γ : Heap ls} {y : Memory l' × Env l' π'} -> Member x Γ -> Member x (y ∷ Γ)

_↦_∈ᴴ_ : ∀ {ls π} -> (l : Label) -> Memory l × Env l π -> Heap ls -> Set
l ↦ x ∈ᴴ Γ = Member x Γ

data Update {l} {π} (x : Memory l × Env l π) : ∀ {ls} -> Heap ls -> Heap ls -> Set where
  here : ∀ {ls π'} {u : Unique l ls} {Γ : Heap ls} {x' : Memory l × Env l π'} -> Update x (x' ∷ Γ) (x ∷ Γ)
  there : ∀ {ls l' π'} {u : Unique l' ls} {Γ Γ' : Heap ls} {y : Memory l' × Env l' π'} -> Update x Γ Γ' -> Update x (y ∷ Γ) (y ∷ Γ')

_≔_[_↦_]ᴴ : ∀ {π ls} -> Heap ls -> Heap ls -> (l : Label) -> Memory l × Env l π -> Set
Γ' ≔ Γ [ l ↦ x ]ᴴ = Update x Γ Γ'

member-∈ : ∀ {l ls π} {x : Memory l × Env l π} {Γ : Heap ls} -> l ↦ x ∈ᴴ Γ -> l ∈ ls
member-∈ here = here
member-∈ (there x) = there (member-∈ x)

update-∈ : ∀ {l ls π} {x : Memory l × Env l π} {Γ Γ' : Heap ls} -> Γ' ≔ Γ [ l ↦ x ]ᴴ -> l ∈ ls
update-∈ here = here
update-∈ (there x) = there (update-∈ x)

--------------------------------------------------------------------------------

-- Sestoft's Abstract Lazy Machine State
-- The state is labeled to keep track of the security level of the
-- term (thread) executed.

data State (l : Label) (τ : Ty) : Set where
  ⟨_,_,_⟩ : ∀ {τ'} {π : Context} -> (Δ : Env l π) (t : Term π τ') (S : Stack l τ' τ) -> State l τ
  ∙ : State l τ

-- Adds labeled memory and heap to a term and stack
data Program (l : Label) (ls : List Label) (τ : Ty) : Set where
  ⟨_,_,_⟩ : ∀ {π} {τ'} -> (Γ : Heap ls) (t : Term π τ') (S : Stack l τ' τ) -> Program l ls τ
  ∙ : Program l ls τ

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
dup-ufv vs (Var ⟪ τ∈π ⟫) | yes p = Var ⟪ τ∈π ⟫  -- In scope
dup-ufv vs (Var ⟪ τ∈π ⟫) | no ¬p = deepDup (Var ⟪ τ∈π ⟫) -- Free
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
dup-ufv vs (deepDup t) = deepDup t  -- deepDup (deepDup t) is semantically equal to deepDup t
dup-ufv vs ∙ = ∙

deepDupᵀ : ∀ {τ π} -> Term π τ -> Term π τ
deepDupᵀ t = dup-ufv [] t

-- The proof that a term is a variable
data IsVar {π} {τ} : Term π τ -> Set where
  Var : ∀ {l} -> (τ∈π : τ ∈⟨ l ⟩ᴿ π) -> IsVar (Var τ∈π)
