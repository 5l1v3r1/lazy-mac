import Lattice

module Types where

open import Relation.Nullary public
open import Relation.Binary.PropositionalEquality
open import Data.Empty public

postulate 𝓛 : Lattice.Lattice
open Lattice.Lattice 𝓛
--open Lattice.Lattice 𝓛 public

open import Data.Vec using (Vec ; [] ; _∷_ ; lookup ; _++_ ; [_] ; _∈_ ; here ; there) public
open import Data.Fin using (Fin ; zero ; suc) public
open import Data.Unit hiding (_≤_ ; _≟_) public
open import Data.Product using (Σ ; _×_ ; _,_)

-- Types τ
data Ty : Set where
  （） : Ty
  Bool : Ty
  _=>_ : (τ₁ t₂ : Ty) -> Ty
  Mac : (l : Label) -> Ty -> Ty
  Res : (l : Label) -> Ty -> Ty
  Id : Ty -> Ty

infixr 3 _=>_

-- Ref : Label -> Ty -> Ty
-- Ref l τ = Res l Nat

Labeled : Label -> Ty -> Ty
Labeled l τ = Res l (Id τ)

-- I will represents MVar also using integers like references
-- MVar : Label -> Ty -> Ty
-- MVar l τ = Res l Nat

-- -- Reference to a variable, bound during some abstraction.
-- data _∈_ {A : Set} : A -> List A -> Set where
--  Here : ∀ {π τ} -> τ ∈ (τ ∷ π)
--  There : ∀ {π α β} -> α ∈ π -> α ∈ (β ∷ π)

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

open import Data.Nat
open import Data.Vec hiding (drop)

record Variable : Set where
  constructor ⟪_,_,_⟫
  field num : ℕ
        ty : Ty
        lbl : Label

open Variable public

Context : ℕ -> Set
Context = Vec Variable

-- Subset relation
data _⊆ˡ_ : ∀ {n m} -> Context n -> Context m -> Set where
  base : [] ⊆ˡ []
  cons : ∀ {α n m} {π₁ : Context n} {π₂ : Context m} -> π₁ ⊆ˡ π₂ -> (α ∷ π₁) ⊆ˡ (α ∷ π₂)
  drop : ∀ {α n m} {π₁ : Context n} {π₂ : Context m} -> π₁ ⊆ˡ π₂ -> π₁ ⊆ˡ (α ∷ π₂)

infixr 2 _⊆ˡ_

refl-⊆ˡ : ∀ {n} {π : Context n} -> π ⊆ˡ π
refl-⊆ˡ {_} {[]} = base
refl-⊆ˡ {_} {x ∷ π} = cons refl-⊆ˡ


wken-∈ : ∀ {n m x} {π₁ : Context n} {π₂ : Context m} -> π₁ ⊆ˡ π₂ -> x ∈ π₁ -> x ∈ π₂
wken-∈ base ()
wken-∈ (cons p) here = here
wken-∈ (cons p) (there q) = there (wken-∈ p q)
wken-∈ (drop p) q = there (wken-∈ p q)

--------------------------------------------------------------------------------
