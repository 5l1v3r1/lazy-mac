open import Lattice

module Types where

postulate 𝓛 : Lattice


open import Relation.Nullary public
open import Relation.Binary.PropositionalEquality
open import Data.Empty public

open Lattice.Lattice 𝓛 public

import Data.List as L
open import Data.List using (List ; [] ; _∷_ ; _++_) public
open import Data.Vec using (Vec ; [] ; _∷_ ; lookup) public
open import Data.Fin using (Fin ; zero ; suc) public
open import Data.Unit hiding (_≤_ ; _≟_) public
open import Data.Product using (_×_ ; _,_)

-- Types τ
data Ty : Set where
  （） : Ty
  Bool : Ty
  _=>_ : (τ₁ t₂ : Ty) -> Ty
  Mac : Label -> Ty -> Ty
  Res : Label -> Ty -> Ty
  Id : Ty -> Ty
  
infixr 3 _=>_

-- Ref : Label -> Ty -> Ty
-- Ref l τ = Res l Nat

Labeled : Label -> Ty -> Ty
Labeled l τ = Res l (Id τ)

-- I will represents MVar also using integers like references
-- MVar : Label -> Ty -> Ty
-- MVar l τ = Res l Nat

-- Reference to a variable, bound during some abstraction.
data _∈_ {A : Set} : A -> List A -> Set where
 Here : ∀ {π τ} -> τ ∈ (τ ∷ π)
 There : ∀ {π α β} -> α ∈ π -> α ∈ (β ∷ π)

-- A list is a prefix of another
data _⊆_ {A : Set} : List A -> List A -> Set where
  base : ∀ {xs : List A} -> [] ⊆ xs
  cons : ∀ {xs ys x} -> xs ⊆ ys -> (x ∷ xs) ⊆ (x ∷ ys)

refl-⊆ : ∀ {A} {xs : List A} -> xs ⊆ xs
refl-⊆ {_} {[]} = base
refl-⊆ {_} {x ∷ xs} = cons refl-⊆

trans-⊆ : ∀ {A} {xs ys zs : List A} -> xs ⊆ ys -> ys ⊆ zs -> xs ⊆ zs
trans-⊆ base q = base
trans-⊆ (cons p) (cons q) = cons (trans-⊆ p q)

snoc-⊆ : ∀ {A} {xs : List A} {x : A} -> xs ⊆ (xs L.∷ʳ x)
snoc-⊆ {_} {[]} = base
snoc-⊆ {_} {x₁ ∷ xs} = cons snoc-⊆

-- Transform τ ∈ᵗ π in Fin
fin : ∀ {A : Set} {τ : A} {π : List A} -> τ ∈ π -> Fin (L.length π)
fin Here = zero
fin (There p) = suc (fin p)

extend-∈ : ∀ {A : Set} {τ : A} {π₁ π₂ : List A} -> τ ∈ π₁ -> π₁ ⊆ π₂ -> τ ∈ π₂
extend-∈ () base
extend-∈ Here (cons p) = Here
extend-∈ (There x) (cons p) = There (extend-∈ x p)

--------------------------------------------------------------------------------

-- Subset relation
data _⊆ˡ_ : List Ty -> List Ty -> Set where
  base : [] ⊆ˡ [] 
  cons : ∀ {α π₁ π₂} -> π₁ ⊆ˡ π₂ -> (α ∷ π₁) ⊆ˡ (α ∷ π₂)
  drop : ∀ {α π₁ π₂} -> π₁ ⊆ˡ π₂ -> π₁ ⊆ˡ (α ∷ π₂)

refl-⊆ˡ : ∀ {π} -> π ⊆ˡ π
refl-⊆ˡ {[]} = base
refl-⊆ˡ {x ∷ π} = cons refl-⊆ˡ

wken-∈ : ∀ {τ π₁ π₂} -> τ ∈ π₁ -> π₁ ⊆ˡ π₂ -> τ ∈ π₂
wken-∈ () base
wken-∈ Here (cons p) = Here
wken-∈ (There x) (cons p) = There (wken-∈ x p)
wken-∈ x (drop p) = There (wken-∈ x p)

infixr 2 _⊆ˡ_

--------------------------------------------------------------------------------
