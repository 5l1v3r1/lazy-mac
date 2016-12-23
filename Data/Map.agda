module Data.Map where 

open import Data.Maybe
open import Data.List
open import Data.Nat

-- A poor's man partial mapping from ℕ → A
Map : Set -> Set
Map A = List (Maybe A)

--------------------------------------------------------------------------------
-- Operations on mapping are defined as data-types since this, in my
-- experience, simplify unification and proofs (which remain tedious though).
--------------------------------------------------------------------------------

-- data Fresh : Map A -> ℕ -> Set where
--  [] : Fresh [] 0
--  _∷_ : ∀ {Γ n mv} -> Fresh Γ n -> Fresh (mv ∷ Γ) (suc n)

-- Add l t Γ₁ n Γ₂ corresponds to Γ₂ = Γ₁[n ↦ (l, t)] with fresh(n),
-- i.e. it is the proof that map Γ₂ extends map Γ₁ with a new
-- binding.
data Add {A : Set} (v : A) : Map A -> ℕ -> Map A -> Set where
  here : Add v [] 0 (just v ∷ [])
  next : ∀ {mv n Γ Γ'} -> Add v Γ n Γ' -> Add v (mv ∷ Γ) (suc n) (mv ∷ Γ')

-- Syntatic sugar for Add.
_≔ᴬ_[_↦_] : ∀ {A} -> Map A -> Map A -> ℕ -> A -> Set
Γ₂ ≔ᴬ Γ₁ [ n ↦ v ] = Add v Γ₁ n Γ₂

-- Remove v Γ₁ n Γ₂ corresponds to Γ₂ = Γ₁ \ {n ↦ v}, i.e.
-- The map Γ₂ results from removing binding n ↦ (l, t) from map Γ₁.
-- In Γ₂, n is mapped to nothing (we want to keep the position free,
-- for possible later reinsertions).
data Remove {A : Set} (v : A) : Map A -> ℕ -> Map A -> Set where
  here : ∀ {Γ} -> Remove v (just v ∷ Γ) 0 (nothing ∷ Γ)
  next : ∀ {Γ Γ' mv n} -> Remove v Γ n Γ' -> Remove v (mv ∷ Γ) (suc n) (mv ∷ Γ')

-- Syntatic sugar for Remove.
_≔ᴿ_[_↦_]  : ∀ {A} -> Map A -> Map A -> ℕ -> A -> Set
Γ ≔ᴿ Γ' [ n ↦ v ] = Remove v Γ' n Γ 

-- Put v Γ n Γ' corresponds to Γ' = Γ[n ↦ (l, t)], i.e.
-- Γ' is Γ updated so that now n maps to (l,t).
-- Note that contrary to Add, n is not fresh.
data Put {A : Set} (v : A) : Map A -> ℕ -> Map A -> Set where
  here : ∀ {Γ} -> Put v (nothing ∷ Γ) 0 ((just v) ∷ Γ)
  next : ∀ {Γ Γ' mv n} -> Put v Γ n Γ' -> Put v (mv ∷ Γ) (suc n) (mv ∷ Γ')

-- Syntatic sugar for Put
_≔ᴾ_[_↦_] : ∀ {A} -> Map A -> Map A -> ℕ -> A -> Set
Γ' ≔ᴾ Γ [ n ↦ v ] = Put v Γ n Γ'

-- Member v n Γ is the proof that n ↦ (l, t) ∈ Γ
data Member {A : Set} (v : A) : ℕ -> Map A -> Set where
  here : ∀ {Γ} -> Member v 0 ((just v) ∷ Γ)
  next : ∀ {Γ mv n} -> Member v n Γ -> Member v (suc n) (mv ∷ Γ)

-- Syntatic sugar for Member
_↦_∈_ : {A : Set} -> ℕ -> A -> Map A -> Set
n ↦ v ∈ Γ = Member v n Γ

