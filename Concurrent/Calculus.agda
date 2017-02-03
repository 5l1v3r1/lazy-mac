import Lattice as L
import Scheduler as S

module Concurrent.Calculus (𝓛 : L.Lattice) (𝓢 : S.Scheduler 𝓛) where

open import Types 𝓛
open import Sequential.Calculus 𝓛
open S.Scheduler 𝓛 𝓢 renaming (State to Stateˢ) public

--------------------------------------------------------------------------------

data Thread (π : Context) (l : Label) : Set where
  ⟨_,_⟩ :  ∀ {τ} -> Term π τ -> Stack l τ (Mac l （）) -> Thread π l
  ∙ : Thread π l  -- I define this as bullet even though it is probably not strictly necessary

-- Pool of threads at a certain label
data Pool (l : Label) : ℕ -> Set where
  [] : Pool l 0
  _◅_ : ∀ {n π} -> Thread π l -> Pool l n -> Pool l (suc n)
  ∙ : ∀ {n} -> Pool l n

infixr 3 _◅_

-- Enqueue
_▻_ : ∀ {n π l} -> Pool l n -> Thread π l -> Pool l (suc n)
[] ▻ t = t ◅ []
(x ◅ ts) ▻ t = x ◅ (ts ▻ t)
∙ ▻ t = ∙

--------------------------------------------------------------------------------

-- A list of pools
data Pools : List Label -> Set where
  [] : Pools []
  _◅_ : ∀ {l ls n} {{u : Unique l ls}} -> Pool l n -> Pools ls -> Pools (l ∷ ls)

open import Relation.Binary.PropositionalEquality

pools-unique : ∀ {l ls} -> (x y : l ∈ ls) -> Pools ls -> x ≡ y
pools-unique here here (x ◅ p) = refl
pools-unique here (there y) (_◅_ {{u}} t p) = ⊥-elim (∈-not-unique y u)
pools-unique (there x) here (_◅_ {{u}} t p) = ⊥-elim (∈-not-unique x u)
pools-unique (there x) (there y) (x₁ ◅ p) rewrite pools-unique x y p = refl

infixl 3 _▻_

--------------------------------------------------------------------------------

-- The global configuration is a thread pool paired with some shared split memory Σ
record Global (ls : List Label) : Set where
  constructor ⟨_,_,_⟩
  field Σ : Stateˢ
        Γ : Heap ls
        P : Pools ls

open Global public
open import Relation.Binary.PropositionalEquality

-- TODO do we need this?
-- state-≡ : ∀ {ls} {g₁ g₂ : Global ls} -> g₁ ≡ g₂ -> state g₁ ≡ state g₂
-- state-≡ refl = refl

-- storeᵍ-≡ : ∀ {ls} {g₁ g₂ : Global ls} -> g₁ ≡ g₂ -> storeᵍ g₁ ≡ storeᵍ g₂
-- storeᵍ-≡ refl = refl

-- pools-≡ : ∀ {ls} {g₁ g₂ : Global ls} -> g₁ ≡ g₂ -> pools g₁ ≡ pools g₂
-- pools-≡ refl = refl
