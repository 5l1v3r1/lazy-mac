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

  Var : ∀ {τ} -> (τ∈π : τ ∈ᴿ π) -> Term π τ
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
  #[_] : ∀ {τ} -> Term π τ -> Term π (Addr τ)
  #[_]ᴰ : ∀ {τ} -> Term π τ -> Term π (Addr τ)  -- Duplicate on read

  -- Concurrency
  fork : ∀ {l h} -> (l⊑h : l ⊑ h) -> Term π (Mac h  （）) -> Term π (Mac l  （）)

  -- The label represents in which labeled environment
  -- a free variable should be looked up in.
  deepDup : ∀ {τ} -> (l : Label) -> Term π τ -> Term π τ

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
  #[_] : ∀ {τ} -> (t : Term π τ) -> Value #[ t ]
  #[_]ᴰ : ∀ {τ} -> (t : Term π τ) -> Value #[ t ]ᴰ

--------------------------------------------------------------------------------

-- The context of a term can be extended without harm
wken : ∀ {τ} {Δ₁ : Context} {Δ₂ : Context} -> Term Δ₁ τ -> Δ₁ ⊆ˡ Δ₂ -> Term Δ₂ τ
wken （） p = （）
wken True p = True
wken False p = False
wken (Id t) p = Id (wken t p)
wken (unId t) p = unId (wken t p)
wken (Var x) p = Var (wken-∈ᴿ p x)
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
wken (#[ t ]) p = #[ wken t p ]
wken (#[ t ]ᴰ) p = #[ wken t p ]ᴰ
wken (fork x t) p = fork x (wken t p)
wken (deepDup l x) p = deepDup l (wken x p)
wken ∙ p = ∙

_↑¹ : ∀ {α β} {Δ : Context} -> Term Δ α -> Term (β ∷ Δ) α
t ↑¹ = wken t (drop refl-⊆ˡ)

-- Performs the variable-term substitution.
var-subst : ∀ {α β} (Δ₁ : Context) (Δ₂ : Context)
            -> Term Δ₂ β -> α ∈ (Δ₁ ++ [ β ] ++ Δ₂) -> Term (Δ₁ ++ Δ₂) α
var-subst [] Δ₂ v here = v
var-subst [] Δ₂ v (there p) = Var (∈-∈ᴿ p)
var-subst {α} (._ ∷ Δ₁) Δ₂ v here = Var (∈-∈ᴿ {α} {α ∷ Δ₁ ++ Δ₂} here)
var-subst (x ∷ Δ₁) Δ₂ v (there p) = (var-subst Δ₁ Δ₂ v p) ↑¹

tm-subst : ∀ {τ α} (Δ₁ : Context) (Δ₂ : Context)-> Term Δ₂ α -> Term (Δ₁ ++ [ α ] ++ Δ₂) τ -> Term (Δ₁ ++ Δ₂) τ
tm-subst Δ₁ Δ₂ v （） = （）
tm-subst Δ₁ Δ₂ v True = True
tm-subst Δ₁ Δ₂ v False = False
tm-subst Δ₁ Δ₂ v (Id t) = Id (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (unId t) = unId (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (Var y∈π) = var-subst Δ₁ Δ₂ v (∈ᴿ-∈ y∈π)
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
tm-subst Δ₁ Δ₂ v (#[ t ]) = #[ tm-subst Δ₁ Δ₂ v t ]
tm-subst Δ₁ Δ₂ v (#[ t ]ᴰ) = #[ tm-subst Δ₁ Δ₂ v t ]ᴰ
tm-subst Δ₁ Δ₂ v (fork x t) = fork x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (deepDup l x) = deepDup l (tm-subst Δ₁ Δ₂ v x)
tm-subst Δ₁ Δ₂ v ∙ = ∙

subst : ∀ {α β} {Δ : Context} -> Term Δ α -> Term (α ∷ Δ) β -> Term Δ β
subst {Δ = Δ} v t = tm-subst [] Δ v t

--------------------------------------------------------------------------------

-- A Well-Typed continuation (Cont), contains well-typed terms and
-- transform the input type (first indexed) in the output type (second
-- index).
data Cont (l : Label) : Ty -> Ty -> Set where
 Var : ∀ {τ₁ τ₂} {{π : Context}} -> (τ∈π : τ₁ ∈ᴿ π) -> Cont l (τ₁ => τ₂) τ₂
 # : ∀ {τ} {{π : Context}} -> (τ∈π : τ ∈ᴿ π)  -> Cont l τ τ
 Then_Else_ : ∀ {τ} {π : Context} -> Term π τ -> Term π τ -> Cont l Bool τ
 Bind :  ∀ {τ₁ τ₂} {π : Context} -> Term π (τ₁ => Mac l τ₂) -> Cont l (Mac l τ₁) (Mac l τ₂)
 unlabel : ∀ {l' τ} (p : l' ⊑ l) -> Cont l (Labeled l' τ) (Mac l τ)
 unId : ∀ {τ} -> Cont l (Id τ) τ
 write : ∀ {τ H} {{π : Context}} -> l ⊑ H -> (τ∈π : τ ∈ π) -> Cont l (Ref H τ) (Mac l （）)
 write∙ : ∀ {τ H} {{π : Context}} -> l ⊑ H -> (τ∈π : τ ∈ π) -> Cont l (Ref H τ) (Mac l （）)
 read : ∀ {τ L} -> L ⊑ l -> Cont l (Ref L τ) (Mac l τ)

-- A Well-typed stack (Stack) contains well-typed terms and is indexed
-- by an input type and an output type.
-- It transforms the former in the latter according to the continuations.
data Stack (l : Label) : Ty -> Ty -> Set where
 [] : ∀ {τ} -> Stack l τ τ
 _∷_ : ∀ {τ₁ τ₂ τ₃} -> Cont l τ₁ τ₂ -> Stack l τ₂ τ₃ -> Stack l τ₁ τ₃
 ∙ : ∀ {τ} -> Stack l τ τ
--------------------------------------------------------------------------------

-- Note: at the moment in Env l π, π contains only variables labeled with l.
-- however in Term π, context π may contain variables with different labels.
-- I think this is still fine, because those variables are not mapped in
-- this environment (⟨ n , τ, l ⟩ ↦ nothing), but in their own.
data Env (l : Label) : Context -> Set where
  [] : Env l []
  _∷_ : ∀ {π τ} -> (t : Maybe (Term π τ)) -> Env l π -> Env l (τ ∷ π)
  ∙ : Env l []  -- We fix the context to empty to avoid non-determinism issues

data Updateᴱ {l π τ} (mt : Maybe (Term π τ)) : ∀ {π'} -> τ ∈ π' -> Env l π' -> Env l π' -> Set where
  here : ∀ {Δ : Env l π} {mt' : Maybe (Term _ τ)} -> Updateᴱ mt here (mt' ∷ Δ) (mt ∷ Δ)
  there : ∀ {π' τ'} {τ∈π' : τ ∈ π'} {Δ Δ' : Env l π'} {mt' : Maybe (Term _ τ')} -> Updateᴱ mt τ∈π' Δ Δ' -> Updateᴱ mt (there τ∈π') (mt' ∷ Δ) (mt' ∷ Δ')

_≔_[_↦_]ᴱ : ∀ {l τ} {π π' : Context} -> Env l π' -> Env l π' -> τ ∈ᴿ π' -> Term π τ -> Set
Δ' ≔ Δ [ τ∈π' ↦ t ]ᴱ = Updateᴱ (just t) (∈ᴿ-∈ τ∈π') Δ Δ'

-- Syntatic sugar for removing a term from the environment.
-- The term is used only to fix its context π and avoid unsolved metas.
_≔_[_↛_]ᴱ : ∀ {l τ} {π π' : Context} -> Env l π' -> Env l π' -> τ ∈ᴿ π' -> Term π τ -> Set
_≔_[_↛_]ᴱ {π = π} Δ' Δ x t = Updateᴱ {π = π} nothing (∈ᴿ-∈ x) Δ Δ'

data Memberᴱ {l π τ} (mt : Maybe (Term π τ)) : ∀ {π'} -> τ ∈ π' -> Env l π' -> Set where
  here : ∀ {Δ : Env l π} -> Memberᴱ mt here (mt ∷ Δ)
  there : ∀ {π' τ'} {τ∈π' : τ ∈ π'} {Δ : Env l π'} {mt' : Maybe (Term _ τ')} -> Memberᴱ mt τ∈π' Δ -> Memberᴱ mt (there τ∈π') (mt' ∷ Δ)

_↦_∈ᴱ_ : ∀ {l τ} {π π' : Context} -> τ ∈ᴿ π' -> Term π τ -> Env l π' -> Set
x ↦ t ∈ᴱ Δ = Memberᴱ (just t) (∈ᴿ-∈ x) Δ

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

-- I don't think I need to store pointers to the heap (τ ∈ π)
-- if I keep separate the store from the heap
data Memory (l : Label) : Set where
  [] : Memory l
  _∷_ : ∀ {π τ} -> (t : Term π τ) (M : Memory l) -> Memory l
  ∙ : Memory l

data Memberᴹ {l π τ} (t : Term π τ) : ℕ -> Memory l -> Set where
  here : ∀ {M} -> Memberᴹ t 0 (t ∷ M)
  there : ∀ {M n π' τ'} {t' : Term π' τ'} -> Memberᴹ t n M -> Memberᴹ t (suc n) (t' ∷ M)
--  ∙ : ∀ {n} -> Memberᴹ ∙ n ∙ -- Not sure if we will need this.  (then t must be an index)

_↦_∈ᴹ_ : ∀ {π l τ} -> ℕ -> Term π τ -> Memory l -> Set
n ↦ t ∈ᴹ M = Memberᴹ t n M

data Writeᴹ {l π τ} (t : Term π τ) : ℕ -> Memory l -> Memory l -> Set where
  here : ∀ {M π' τ} {t' : Term π' τ} -> Writeᴹ t 0 (t' ∷ M) (t ∷  M)
  there : ∀ {M M' π' τ' n} {t' : Term π' τ'} -> Writeᴹ t n M M' -> Writeᴹ t (suc n) (t' ∷ M) (t' ∷ M')

_≔_[_↦_]ᴹ : ∀ {π l τ} -> Memory l -> Memory l -> ℕ -> Term π τ -> Set
M' ≔ M [ n ↦ t ]ᴹ = Writeᴹ t n M M'

--------------------------------------------------------------------------------

-- Sestoft's Abstract Lazy Machine State
-- The state is labeled to keep track of the security level of the
-- term (thread) executed.

data State (l : Label) (τ : Ty) : Set where
  ⟨_,_,_⟩ : ∀ {τ'} {π : Context} -> (Δ : Env l π) (t : Term π τ') (S : Stack l τ' τ) -> State l τ
  ∙ : State l τ

-- Adds labeled memory and heap to a term and stack
data Program (ls : List Label) (l : Label) (τ : Ty) : Set where
  ⟨_,_,_,_⟩ : ∀ {π τ'} -> {!!} -> Heap ls -> Term π τ -> Stack l τ' τ -> Program ls l τ

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
dup-ufv : ∀ {π τ} -> Label -> Vars π -> Term π τ -> Term π τ
dup-ufv l vs （） = （）
dup-ufv l vs True = True
dup-ufv l vs False = False
dup-ufv l vs (Id t) = Id (dup-ufv l vs t)
dup-ufv l vs (unId t) = unId (dup-ufv l vs t)
dup-ufv l vs (Var τ∈π) with memberⱽ (∈ᴿ-∈ τ∈π) vs
dup-ufv l vs (Var τ∈π) | yes p = Var τ∈π  -- In scope
dup-ufv l vs (Var τ∈π) | no ¬p = deepDup l (Var τ∈π) -- Free
dup-ufv l vs (Abs t) = Abs (dup-ufv l (here ∷ mapⱽ there vs) t)
dup-ufv l vs (App t t₁) = App (dup-ufv l vs t) (dup-ufv l vs t₁)
dup-ufv l vs (If t Then t₁ Else t₂) = If (dup-ufv l vs t) Then (dup-ufv l vs t₁) Else (dup-ufv l vs t₂)
dup-ufv l' vs (Return l t) = Return l (dup-ufv l' vs t)
dup-ufv l vs (t >>= t₁) = (dup-ufv l vs t) >>= (dup-ufv l vs t₁)
dup-ufv l' vs (Mac l t) = Mac l (dup-ufv l' vs t)
dup-ufv l' vs (Res l t) = Res l (dup-ufv l' vs t)
dup-ufv l vs (label l⊑h t) = label l⊑h (dup-ufv l vs t)
dup-ufv l vs (label∙ l⊑h t) = label∙ l⊑h (dup-ufv l vs t)
dup-ufv l vs (unlabel l⊑h t) = unlabel l⊑h (dup-ufv l vs t)
dup-ufv l vs(read l⊑h t) = read l⊑h (dup-ufv l vs t)
dup-ufv l vs (write l⊑h t₁ t₂) = write l⊑h (dup-ufv l vs t₁) (dup-ufv l vs t₂)
dup-ufv l vs (write∙ l⊑h t₁ t₂) = write∙ l⊑h (dup-ufv l vs t₁) (dup-ufv l vs t₂)
dup-ufv l vs (new l⊑h t) = new l⊑h (dup-ufv l vs t)
dup-ufv l vs (new∙ l⊑h t) = new∙ l⊑h (dup-ufv l vs t)
dup-ufv l vs (#[ n ]) = #[ n ]ᴰ  -- Duplicate on read!
dup-ufv l vs (#[ n ]ᴰ) = #[ n ]ᴰ
dup-ufv l vs (fork l⊑h t) = fork l⊑h (dup-ufv l vs t)
-- Note that here the label represents in which environment
-- we will find a variable, in this case we
-- use l' (the lower one).
-- This can happen if a low thread (L) spwans a medium one (M)
-- which spawns a high one (H), if H access a variable defined
-- in L, but not evaluated (yet) in M.
dup-ufv l vs (deepDup l' t) = deepDup l' t  -- deepDup (deepDup t) is semantically equal to deepDup t
dup-ufv l vs ∙ = ∙

deepDupᵀ : ∀ {τ π} -> Label -> Term π τ -> Term π τ
deepDupᵀ l t = dup-ufv l [] t

-- The proof that a term is a variable
data IsVar {π} {τ} : Term π τ -> Set where
  Var : (τ∈π : τ ∈ᴿ π) -> IsVar (Var τ∈π)
