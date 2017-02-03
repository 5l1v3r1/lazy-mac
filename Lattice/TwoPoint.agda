module Lattice.TwoPoint where

open import Lattice.Base using (Lattice ; Lat)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty

data LH : Set where
 L : LH
 H : LH

_≟_ : (l₁ l₂ : LH) -> Dec (l₁ ≡ l₂)
L ≟ L = yes refl
L ≟ H = no (λ ())
H ≟ L = no (λ ())
H ≟ H = yes refl

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

refl-⊑ : ∀ {l} -> l ⊑ l
refl-⊑ {L} = L⊑ L
refl-⊑ {H} = H⊑H

trans-⊑ : ∀ {l₁ l₂ l₃} -> l₁ ⊑ l₂ -> l₂ ⊑ l₃ -> l₁ ⊑ l₃
trans-⊑ (L⊑ .L) (L⊑ l₃) = L⊑ l₃
trans-⊑ (L⊑ .H) H⊑H = L⊑ H
trans-⊑ H⊑H H⊑H = H⊑H

2-point : Lattice
2-point = Lat LH _⊑_ _⊑?_ _≟_ ext-⊑ refl-⊑ trans-⊑

open import Data.List

lh : List LH
lh = L ∷ H ∷ []
