{-# OPTIONS --rewriting #-}

module Lemmas where

module Lemmas where

open import Data.List hiding (reverse ; drop)

reverse : ∀ {A : Set} -> List A -> List A
reverse [] = []
reverse (x ∷ π) = reverse π ++ [ x ]

data _∈_ {A : Set} (τ : A) : List A -> Set where
 here : ∀ {π} -> τ ∈ (τ ∷ π)
 there : ∀ {τ' π} -> τ ∈ π -> τ ∈ (τ' ∷ π)

_∈ᴿ_ : ∀ {A} -> A -> List A -> Set
τ ∈ᴿ π = τ ∈ (reverse π)

-- Subset relation
data _⊆_ {A : Set} : List A -> List A -> Set where
  base : [] ⊆ []
  cons : ∀ {α π₁ π₂} -> π₁ ⊆ π₂ -> (α ∷ π₁) ⊆ (α ∷ π₂)
  drop : ∀ {α π₁ π₂} -> π₁ ⊆ π₂ -> π₁ ⊆ (α ∷ π₂)

infixr 2 _⊆_

refl-⊆ : ∀ {A} {π : List A} -> π ⊆ π
refl-⊆ {_} {[]} = base
refl-⊆ {_} {x ∷ π} = cons refl-⊆

prod-⊆ : ∀ {A : Set} {τ : A} {π₁ π₂} -> π₁ ⊆ π₂ -> π₁ ⊆ π₂ ++ [ τ ]
prod-⊆ base = drop base
prod-⊆ (cons x) = cons (prod-⊆ x)
prod-⊆ (drop x) = drop (prod-⊆ x)

snoc-⊆ : ∀ {A : Set} {τ : A} {π₁ π₂} -> π₁ ⊆ π₂ -> π₁ ++ [ τ ] ⊆ π₂ ++ [ τ ]
snoc-⊆ base = cons base
snoc-⊆ (cons x) = cons (snoc-⊆ x)
snoc-⊆ (drop x) = drop (snoc-⊆ x)

rev-⊆ : ∀ {A} {π₁ π₂ : List A} -> π₁ ⊆ π₂ -> reverse π₁ ⊆ reverse π₂
rev-⊆ base = base
rev-⊆ (cons x) = snoc-⊆ (rev-⊆ x)
rev-⊆ (drop x) = prod-⊆ (rev-⊆ x)

drop-⊆ : ∀ {A} {π₁ π₂ : List A} -> π₁ ⊆ π₁ ++ π₂
drop-⊆ {_} {[]} {[]} = base
drop-⊆ {_} {[]} {x ∷ π₂} = drop drop-⊆
drop-⊆ {_} {x ∷ π₁} = cons drop-⊆

wken-∈ : ∀ {A x} {π₁ : List A} {π₂ : List A} -> π₁ ⊆ π₂ -> x ∈ π₁ -> x ∈ π₂
wken-∈ base ()
wken-∈ (cons p) here = here
wken-∈ (cons p) (there q) = there (wken-∈ p q)
wken-∈ (drop p) q = there (wken-∈ p q)

snoc-∈ : ∀ {A} (τ : A) (π : List A) -> τ ∈ (π ++ [ τ ])
snoc-∈ τ [] = here
snoc-∈ τ (x ∷ π) = there (snoc-∈ τ π)

∈-∈ᴿ : ∀ {A} {τ : A}{π} -> τ ∈ π -> τ ∈ᴿ π
∈-∈ᴿ {_} {τ} {.τ ∷ π} here = snoc-∈ τ (reverse π)
∈-∈ᴿ {_} {τ} {τ' ∷ π} (there x) = wken-∈ drop-⊆ (∈-∈ᴿ x)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty

{-# BUILTIN REWRITE _≡_ #-}

rev-append-≡ : ∀ {A x} -> (π : List A) -> reverse (π ++ [ x ]) ≡ x ∷ reverse π
rev-append-≡ [] = refl
rev-append-≡ {_} {x} (x₁ ∷ π) rewrite rev-append-≡ {_} {x} π = refl

{-# REWRITE  rev-append-≡ #-}

rev-rev-≡ : ∀ {A : Set} -> (π : List A) -> reverse (reverse π) ≡ π
rev-rev-≡ [] = refl
rev-rev-≡ (x ∷ π) = cong (_∷_ x) (rev-rev-≡ π)

{-# REWRITE rev-rev-≡ #-}

∈ᴿ-∈ : ∀ {A} {τ : A} {π} -> τ ∈ᴿ π -> τ ∈ π
∈ᴿ-∈ {τ} {π} x = ∈-∈ᴿ x

wken-∈ᴿ : ∀ {A x} {π₁ : List A} {π₂ : List A} -> π₁ ⊆ π₂ -> x ∈ᴿ π₁ -> x ∈ᴿ π₂
wken-∈ᴿ x p = wken-∈ (rev-⊆ x) p

hereᴿ : ∀ {A : Set} {{π}} {τ : A} -> τ ∈ᴿ (τ ∷ π)
hereᴿ {{π}} {τ} = snoc-∈ τ (reverse π)

--------------------------------------------------------------------------------
