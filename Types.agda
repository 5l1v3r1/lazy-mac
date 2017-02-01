{-# OPTIONS --rewriting #-}

import Lattice

module Types where

open import Relation.Nullary public
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty public

postulate 𝓛 : Lattice.Lattice
open Lattice.Lattice 𝓛
--open Lattice.Lattice 𝓛 public

{-# BUILTIN REWRITE _≡_ #-}

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
  Addr : Ty

infixr 3 _=>_

Labeled : Label -> Ty -> Ty
Labeled l τ = Res l (Id τ)

Ref : Label -> Ty -> Ty
Ref l τ = Res l Addr

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

data _∈_ {A : Set} (τ : A) : List A -> Set where
 here : ∀ {π} -> τ ∈ (τ ∷ π)
 there : ∀ {τ' π} -> τ ∈ π -> τ ∈ (τ' ∷ π)

_∈ᴿ_ : Ty -> Context -> Set
τ ∈ᴿ π = τ ∈ (reverse π)

-- Subset relation
data _⊆ˡ_ : Context -> Context -> Set where
  base : [] ⊆ˡ []
  cons : ∀ {α π₁ π₂} -> π₁ ⊆ˡ π₂ -> (α ∷ π₁) ⊆ˡ (α ∷ π₂)
  drop : ∀ {α π₁ π₂} -> π₁ ⊆ˡ π₂ -> π₁ ⊆ˡ (α ∷ π₂)

infixr 2 _⊆ˡ_

refl-⊆ˡ : {π : Context} -> π ⊆ˡ π
refl-⊆ˡ {[]} = base
refl-⊆ˡ {x ∷ π} = cons refl-⊆ˡ

prod-⊆ : ∀ {τ π₁ π₂} -> π₁ ⊆ˡ π₂ -> π₁ ⊆ˡ π₂ ++ [ τ ]
prod-⊆ base = drop base
prod-⊆ (cons x) = cons (prod-⊆ x)
prod-⊆ (drop x) = drop (prod-⊆ x)

snoc-⊆ : ∀ {τ π₁ π₂} -> π₁ ⊆ˡ π₂ -> π₁ ++ [ τ ] ⊆ˡ π₂ ++ [ τ ]
snoc-⊆ base = cons base
snoc-⊆ (cons x) = cons (snoc-⊆ x)
snoc-⊆ (drop x) = drop (snoc-⊆ x)

rev-⊆ˡ : ∀ {π₁ π₂} -> π₁ ⊆ˡ π₂ -> reverse π₁ ⊆ˡ reverse π₂
rev-⊆ˡ base = base
rev-⊆ˡ (cons x) = snoc-⊆ (rev-⊆ˡ x)
rev-⊆ˡ (drop x) = prod-⊆ (rev-⊆ˡ x)

drop-⊆ : ∀ {π₁} {π₂} -> π₁ ⊆ˡ π₁ ++ π₂
drop-⊆ {[]} {[]} = base
drop-⊆ {[]} {x ∷ π₂} = drop drop-⊆
drop-⊆ {x ∷ π₁} = cons drop-⊆

wken-∈ : ∀ {x} {π₁ : Context} {π₂ : Context} -> π₁ ⊆ˡ π₂ -> x ∈ π₁ -> x ∈ π₂
wken-∈ base ()
wken-∈ (cons p) here = here
wken-∈ (cons p) (there q) = there (wken-∈ p q)
wken-∈ (drop p) q = there (wken-∈ p q)

snoc-∈ : ∀ (τ : Ty) (π : Context) -> τ ∈ (π ++ [ τ ])
snoc-∈ τ [] = here
snoc-∈ τ (x ∷ π) = there (snoc-∈ τ π)

∈-∈ᴿ : ∀ {τ π} -> τ ∈ π -> τ ∈ᴿ π
∈-∈ᴿ {τ} {.τ ∷ π} here = snoc-∈ τ (reverse π)
∈-∈ᴿ {τ} {τ' ∷ π} (there x) = wken-∈ drop-⊆ (∈-∈ᴿ x)

rev-append-≡ : ∀ {x} -> (π : Context) -> reverse (π ++ [ x ]) ≡ x ∷ reverse π
rev-append-≡ [] = refl
rev-append-≡ {x} (x₁ ∷ π) rewrite rev-append-≡ {x} π = refl

{-# REWRITE  rev-append-≡ #-}

rev-rev-≡ : ∀ π -> reverse (reverse π) ≡ π
rev-rev-≡ [] = refl
rev-rev-≡ (x ∷ π) = cong (_∷_ x) (rev-rev-≡ π)

{-# REWRITE rev-rev-≡ #-}

∈ᴿ-∈ : ∀ {τ π} -> τ ∈ᴿ π -> τ ∈ π
∈ᴿ-∈ {τ} {π} x = ∈-∈ᴿ x

wken-∈ᴿ : ∀ {x} {π₁ : Context} {π₂ : Context} -> π₁ ⊆ˡ π₂ -> x ∈ᴿ π₁ -> x ∈ᴿ π₂
wken-∈ᴿ x p = wken-∈ (rev-⊆ˡ x) p

hereᴿ : ∀ {{π}} {τ} -> τ ∈ᴿ (τ ∷ π)
hereᴿ {{π}} {τ} = snoc-∈ τ (reverse π)

--------------------------------------------------------------------------------

record _∈⟨_⟩_ (τ : Ty) (l : Label) (π : Context) : Set where
  constructor ⟪_⟫
  field τ∈π : τ ∈ π

infixl 2 ⟪_⟫

_∈⟨_⟩ᴿ_  : Ty -> Label -> Context -> Set
τ ∈⟨ l ⟩ᴿ π = τ ∈⟨ l ⟩ (reverse π)

--------------------------------------------------------------------------------
