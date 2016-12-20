module Lattice.TwoPoint where

open import Lattice.Base
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty

data LH : Set where
 L : LH
 H : LH

data _⊑_ : LH -> LH -> Set where
 L⊑ : ∀ (l : LH) -> L ⊑ l
 H⊑H : H ⊑ H

_⊑?_ : (l₁ l₂ : LH) -> Dec (l₁ ⊑ l₂)
L ⊑? l₂ = yes (L⊑ l₂)
H ⊑? L = no (λ ())
H ⊑? H = yes H⊑H
 
ext-⊑ : ∀ {l₁ l₂} (x y : l₁ ⊑ l₂) -> x ≡ y
ext-⊑ (L⊑ l) (L⊑ .l) = refl
ext-⊑ H⊑H H⊑H = refl

2-point : Lattice 
2-point = Lat LH _⊑_ _⊑?_ ext-⊑
