import Lattice as L
import Scheduler as S

module Concurrent.Calculus (𝓛 : L.Lattice) (𝓢 : S.Scheduler 𝓛) where

open import Types 𝓛
open import Data.Nat
open import Sequential.Calculus 𝓛 hiding (Ms ; Γ)
open S.Scheduler 𝓛 𝓢 renaming (State to Stateˢ)

--------------------------------------------------------------------------------

Thread : Label -> Set
Thread l = TS∙ l (Mac l （）)

-- Pool of threads at a certain label
data Pool (l : Label) : Set where
  [] : Pool l
  _◅_ : (t : Thread l) (T : Pool l) -> Pool l
  ∙ : Pool l

infixr 3 _◅_

lengthᵀ : ∀ {l} -> Pool l -> ℕ
lengthᵀ [] = 0
lengthᵀ (x ◅ P) = suc (lengthᵀ P)
lengthᵀ ∙ = 0

-- Enqueue
_▻_ : ∀ {l} -> Pool l -> Thread l -> Pool l
[] ▻ t = t ◅ []
(x ◅ ts) ▻ t = x ◅ (ts ▻ t)
∙ ▻ t = ∙

--------------------------------------------------------------------------------

-- A list of pools
data Pools : List Label -> Set where
  [] : Pools []
  _◅_ : ∀ {l ls} {{u : Unique l ls}} -> (T : Pool l)(P : Pools ls) -> Pools (l ∷ ls)

open import Relation.Binary.PropositionalEquality
open import Data.Empty

pools-unique : ∀ {l ls} -> (x y : l ∈ ls) -> Pools ls -> x ≡ y
pools-unique here here (x ◅ p) = refl
pools-unique here (there y) (_◅_ {{u}} t p) = ⊥-elim (∈-not-unique y u)
pools-unique (there x) here (_◅_ {{u}} t p) = ⊥-elim (∈-not-unique x u)
pools-unique (there x) (there y) (x₁ ◅ p) rewrite pools-unique x y p = refl

infixl 3 _▻_

--------------------------------------------------------------------------------

-- The global configuration is a thread pool paired with some shared split memory Σ
record Global (ls : List Label) : Set where
  constructor ⟨_,_,_,_⟩
  field Σ : Stateˢ
        Ms : Memories ls
        Γ : Heaps ls
        P : Pools ls

open Global public
open import Relation.Binary.PropositionalEquality

--------------------------------------------------------------------------------
-- Thread Pool operation

data Memberᵀ {l : Label}  : (t : Thread l) -> ℕ -> Pool l -> Set where
--  ∙ : ∀ {n} -> Memberᵀ ∙ n ∙ -- Not clear that we need this
  here : ∀ {t} {ts : Pool l} -> Memberᵀ t zero (t ◅ ts)
  there : ∀ {n t} {ts : Pool l} {t' : Thread l} -> Memberᵀ t n ts -> Memberᵀ t (suc n) (t' ◅ ts)

_↦_∈ᵀ_ : ∀ {l} -> ℕ -> Thread l -> Pool l -> Set
n ↦ t ∈ᵀ ts = Memberᵀ t n ts

data Updateᵀ {l : Label} (t : Thread l) : ℕ -> Pool l -> Pool l -> Set where
  -- ∙ : Updateᵀ t n ∙ ∙  -- Not clear that we need this
  here : ∀ {ts : Pool l} {t' : Thread l} -> Updateᵀ t zero (t' ◅ ts) (t ◅ ts)
  there : ∀ {n} {ts₁ ts₂ : Pool l} {t' : Thread l} -> Updateᵀ t n ts₁ ts₂ -> Updateᵀ t (suc n) (t' ◅ ts₁) (t' ◅ ts₂)

_≔_[_↦_]ᵀ : ∀ {l} -> Pool l -> Pool l -> ℕ -> Thread l -> Set
P' ≔ P [ n ↦ t ]ᵀ = Updateᵀ t n P P'


--------------------------------------------------------------------------------
-- Thread Pools operations

data Memberᴾ {l : Label} (ts : Pool l) : ∀ {ls} -> Pools ls -> Set where
  here : ∀ {ls} {P : Pools ls} {u : Unique l ls} -> Memberᴾ ts (ts ◅ P)
  there : ∀ {l' ls} {P : Pools ls} {u : Unique l' ls} {ts' : Pool l'} -> Memberᴾ ts P -> Memberᴾ ts (ts' ◅ P)

_↦_∈ᴾ_ : ∀ {ls} -> (l : Label) -> Pool l -> Pools ls -> Set
l  ↦ ts ∈ᴾ P = Memberᴾ ts P

data Updateᴾ {l : Label} (ts : Pool l) : ∀ {ls} -> Pools ls -> Pools ls -> Set where
  here : ∀ {ls} {ts' : Pool l} {u : Unique l ls} {P : Pools ls} -> Updateᴾ ts (ts' ◅  P) (ts ◅ P)
  there : ∀ {ls l'} {ts' : Pool l'} {u : Unique l' ls} {P P' : Pools ls} -> Updateᴾ ts P P' -> Updateᴾ ts (ts' ◅ P) (ts' ◅ P')

_≔_[_↦_]ᴾ : ∀ {ls} -> Pools ls -> Pools ls -> (l : Label) -> Pool l -> Set
P' ≔ P [ l ↦ ts ]ᴾ = Updateᴾ ts P P'

--------------------------------------------------------------------------------

memberᴾ-∈ : ∀ {l ls} {P : Pools ls} {T : Pool l} -> l ↦ T ∈ᴾ P -> l ∈ ls
memberᴾ-∈ here = here
memberᴾ-∈ (there x) = there (memberᴾ-∈ x)

updateᴾ-∈ : ∀ {l ls} {P₁ P₂ : Pools ls} {T : Pool l} -> P₂ ≔ P₁ [ l ↦ T ]ᴾ -> l ∈ ls
updateᴾ-∈ here = here
updateᴾ-∈ (there x) = there (updateᴾ-∈ x)

open import Data.Product as P

updateᵀ : ∀ {l n} {t : Thread l} {T : Pool l} -> n ↦ t ∈ᵀ T -> (t' : Thread l) -> ∃ (λ T' → T' ≔ T [ n ↦ t' ]ᵀ)
updateᵀ here t' = _ , here
updateᵀ (there x) t' = P.map (_◅_ _) there (updateᵀ x t')

updateᴾ : ∀ {l ls} {T : Pool l} {P : Pools ls} -> l ↦ T ∈ᴾ P -> (T' : Pool l) -> ∃ (λ P' → P' ≔ P [ l ↦ T' ]ᴾ)
updateᴾ here T' = _ , here
updateᴾ (there T∈P) T' = P.map (_◅_ _) there (updateᴾ T∈P T')

lookupᴾ : ∀ {l ls} -> l ∈ ls -> Pools ls -> Pool l
lookupᴾ here (T ◅ Ps) = T
lookupᴾ (there l∈ls) (T ◅ Ps) = lookupᴾ l∈ls Ps

lookup-∈ᴾ : ∀ {l ls} -> (l∈ls : l ∈ ls) (Ps : Pools ls) -> l ↦ lookupᴾ l∈ls Ps ∈ᴾ Ps
lookup-∈ᴾ here (T ◅ Ps) = here
lookup-∈ᴾ (there l∈ls) (T ◅ Ps) = there (lookup-∈ᴾ l∈ls Ps)
