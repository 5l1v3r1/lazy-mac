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
data _⊆ˡ_ {A : Set} : List A -> List A -> Set where
  base : [] ⊆ˡ []
  cons : ∀ {α π₁ π₂} -> π₁ ⊆ˡ π₂ -> (α ∷ π₁) ⊆ˡ (α ∷ π₂)
  drop : ∀ {α π₁ π₂} -> π₁ ⊆ˡ π₂ -> π₁ ⊆ˡ (α ∷ π₂)

infixr 2 _⊆ˡ_

refl-⊆ˡ : ∀ {A} {π : List A} -> π ⊆ˡ π
refl-⊆ˡ {_} {[]} = base
refl-⊆ˡ {_} {x ∷ π} = cons refl-⊆ˡ

prod-⊆ : ∀ {A : Set} {τ : A} {π₁ π₂} -> π₁ ⊆ˡ π₂ -> π₁ ⊆ˡ π₂ ++ [ τ ]
prod-⊆ base = drop base
prod-⊆ (cons x) = cons (prod-⊆ x)
prod-⊆ (drop x) = drop (prod-⊆ x)

snoc-⊆ : ∀ {A : Set} {τ : A} {π₁ π₂} -> π₁ ⊆ˡ π₂ -> π₁ ++ [ τ ] ⊆ˡ π₂ ++ [ τ ]
snoc-⊆ base = cons base
snoc-⊆ (cons x) = cons (snoc-⊆ x)
snoc-⊆ (drop x) = drop (snoc-⊆ x)

rev-⊆ˡ : ∀ {A} {π₁ π₂ : List A} -> π₁ ⊆ˡ π₂ -> reverse π₁ ⊆ˡ reverse π₂
rev-⊆ˡ base = base
rev-⊆ˡ (cons x) = snoc-⊆ (rev-⊆ˡ x)
rev-⊆ˡ (drop x) = prod-⊆ (rev-⊆ˡ x)

drop-⊆ : ∀ {A} {π₁ π₂ : List A} -> π₁ ⊆ˡ π₁ ++ π₂
drop-⊆ {_} {[]} {[]} = base
drop-⊆ {_} {[]} {x ∷ π₂} = drop drop-⊆
drop-⊆ {_} {x ∷ π₁} = cons drop-⊆

wken-∈ : ∀ {A x} {π₁ : List A} {π₂ : List A} -> π₁ ⊆ˡ π₂ -> x ∈ π₁ -> x ∈ π₂
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

wken-∈ᴿ : ∀ {A x} {π₁ : List A} {π₂ : List A} -> π₁ ⊆ˡ π₂ -> x ∈ᴿ π₁ -> x ∈ᴿ π₂
wken-∈ᴿ x p = wken-∈ (rev-⊆ˡ x) p

hereᴿ : ∀ {A : Set} {{π}} {τ : A} -> τ ∈ᴿ (τ ∷ π)
hereᴿ {{π}} {τ} = snoc-∈ τ (reverse π)

--------------------------------------------------------------------------------
