import Lattice as L

module Types (𝓛 : L.Lattice) where

open L.Lattice 𝓛 public

open import Data.Fin using (Fin ; zero ; suc) public
open import Data.Unit hiding (_≤_ ; _≟_) public
open import Data.Product using (Σ ; _×_ ; _,_)
open import Data.Maybe using (Maybe ; just ; nothing)

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

open import Data.List hiding (drop ; reverse ) public
open import Lemmas public

Context : Set
Context = List Ty

record _∈⟨_⟩_ (τ : Ty) (l : Label) (π : Context) : Set where
  constructor ⟪_⟫
  field τ∈π : τ ∈ π

infixl 2 ⟪_⟫

_∈⟨_⟩ᴿ_  : Ty -> Label -> Context -> Set
τ ∈⟨ l ⟩ᴿ π = τ ∈⟨ l ⟩ (reverse π)

--------------------------------------------------------------------------------
