import Lattice

module Types where

open import Relation.Nullary public
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty public

postulate 𝓛 : Lattice.Lattice
open Lattice.Lattice 𝓛
--open Lattice.Lattice 𝓛 public

open import Data.List hiding (drop ; reverse ) public
open import Data.Fin using (Fin ; zero ; suc) public
open import Data.Unit hiding (_≤_ ; _≟_) public
open import Data.Product using (Σ ; _×_ ; _,_)
open import Data.Maybe using (Maybe ; just ; nothing) public

-- Types τ
data Ty : Set where
  （） : Ty
  Bool : Ty
  _=>_ : (τ₁ t₂ : Ty) -> Ty
  Mac : (l : Label) -> Ty -> Ty
  Res : (l : Label) -> Ty -> Ty
  Id : Ty -> Ty
  Addr : Ty -> Ty

infixr 3 _=>_

Labeled : Label -> Ty -> Ty
Labeled l τ = Res l (Id τ)

Ref : Label -> Ty -> Ty
Ref l τ = Res l (Addr τ)

-- I will represents MVar also using integers like references
-- MVar : Label -> Ty -> Ty
-- MVar l τ = Res l Nat

-- A list is a prefix of another
-- data _⊆_ {A : Set} : List A -> List A -> Set where
--   base : ∀ {xs : List A} -> [] ⊆ xs
--   cons : ∀ {xs ys x} -> xs ⊆ ys -> (x ∷ xs) ⊆ (x ∷ ys)

-- refl-⊆ : ∀ {A} {xs : List A} -> xs ⊆ xs
-- refl-⊆ {_} {[]} = base
-- refl-⊆ {_} {x ∷ xs} = cons refl-⊆

-- trans-⊆ : ∀ {A} {xs ys zs : List A} -> xs ⊆ ys -> ys ⊆ zs -> xs ⊆ zs
-- trans-⊆ base q = base
-- trans-⊆ (cons p) (cons q) = cons (trans-⊆ p q)

-- snoc-⊆ : ∀ {A} {xs : List A} {x : A} -> xs ⊆ (xs L.∷ʳ x)
-- snoc-⊆ {_} {[]} = base
-- snoc-⊆ {_} {x₁ ∷ xs} = cons snoc-⊆

-- Transform τ ∈ᵗ π in Fin
-- fin : ∀ {A : Set} {τ : A} {π : List A} -> τ ∈ π -> Fin (L.length π)
-- fin Here = zero
-- fin (There p) = suc (fin p)

-- extend-∈ : ∀ {A : Set} {τ : A} {π₁ π₂ : List A} -> τ ∈ π₁ -> π₁ ⊆ π₂ -> τ ∈ π₂
-- extend-∈ () base
-- extend-∈ Here (cons p) = Here
-- extend-∈ (There x) (cons p) = There (extend-∈ x p)

--------------------------------------------------------------------------------

Context : Set
Context = List Ty

reverse : Context -> Context
reverse [] = []
reverse (x ∷ π) = reverse π ++ [ x ]

-- Reference to a variable, bound during some abstraction.
data _∈_ (τ : Ty) : Context -> Set where
 here : ∀ {π} -> τ ∈ (τ ∷ π)
 there : ∀ {τ' π} -> τ ∈ π -> τ ∈ (τ' ∷ π)

_∈ᴿ_ : Ty -> Context -> Set
τ ∈ᴿ π = τ ∈ (reverse π)

-- data _∈ᴿ_ (τ : Ty) (π : Context) : Set where
--   rev : τ ∈ reverse π -> τ ∈ᴿ π

-- Subset relation
data _⊆ˡ_ : Context -> Context -> Set where
  base : [] ⊆ˡ []
  cons : ∀ {α π₁ π₂} -> π₁ ⊆ˡ π₂ -> (α ∷ π₁) ⊆ˡ (α ∷ π₂)
  drop : ∀ {α π₁ π₂} -> π₁ ⊆ˡ π₂ -> π₁ ⊆ˡ (α ∷ π₂)

infixr 2 _⊆ˡ_

refl-⊆ˡ : {π : Context} -> π ⊆ˡ π
refl-⊆ˡ {[]} = base
refl-⊆ˡ {x ∷ π} = cons refl-⊆ˡ

drop-⊆ : ∀ {π₁} {π₂} -> π₁ ⊆ˡ π₁ ++ π₂
drop-⊆ {[]} {[]} = base
drop-⊆ {[]} {x ∷ π₂} = drop drop-⊆
drop-⊆ {x ∷ π₁} = cons drop-⊆

wken-∈ : ∀ {x} {π₁ : Context} {π₂ : Context} -> π₁ ⊆ˡ π₂ -> x ∈ π₁ -> x ∈ π₂
wken-∈ base ()
wken-∈ (cons p) here = here
wken-∈ (cons p) (there q) = there (wken-∈ p q)
wken-∈ (drop p) q = there (wken-∈ p q)

snoc-∈ : ∀ τ π -> τ ∈ (π ++ [ τ ])
snoc-∈ τ [] = here
snoc-∈ τ (x ∷ π) = there (snoc-∈ τ π)

∈-∈ᴿ : ∀ {τ π} -> τ ∈ π -> τ ∈ᴿ π
∈-∈ᴿ x = aux x
  where aux : ∀ {τ π} -> τ ∈ π -> τ ∈ reverse π
        aux {τ} {.τ ∷ π} here = snoc-∈ τ (reverse π)
        aux {τ} {τ' ∷ π} (there x) = wken-∈ drop-⊆ (aux x)

rev-append-≡ : ∀ {x} -> (π : Context) -> reverse (π ++ [ x ]) ≡ x ∷ reverse π
rev-append-≡ [] = refl
rev-append-≡ {x} (x₁ ∷ π) rewrite rev-append-≡ {x} π = refl

rev-rev-≡ : ∀ π -> reverse (reverse π) ≡ π
rev-rev-≡ [] = refl
rev-rev-≡ (x ∷ π) rewrite rev-append-≡ {x} (reverse π) = cong (_∷_ x) (rev-rev-≡ π)

rev-∈ : ∀ {τ π} -> τ ∈ᴿ π -> τ ∈ π
rev-∈ {τ} {π} x with ∈-∈ᴿ x
... | y rewrite rev-rev-≡ π = y

--------------------------------------------------------------------------------
