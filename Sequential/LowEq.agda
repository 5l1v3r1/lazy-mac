import Lattice as L

module Sequential.LowEq (𝓛 : L.Lattice) (A : L.Label 𝓛) where

open import Types 𝓛
open import Sequential.Erasure 𝓛 A as SE

--------------------------------------------------------------------------------
-- Temporarily side-step bug #2245

import Sequential.Calculus as SC
open SC 𝓛

--------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Relation.Nullary
open import Data.Maybe as M
open import Data.Product using (_×_ ; proj₁ ; proj₂)
import Data.Product as P

_≡ᴱ_ : ∀ {l π} -> Env l π -> Env l π -> Set
_≡ᴱ_ = _≡_

_≅ᴴ_ : ∀ {ls} (H₁ H₂ : Heaps ls) -> Set
H₁ ≅ᴴ H₂ = εᴴ H₁ ≡ εᴴ H₂

--------------------------------------------------------------------------------

_≅ᵀ_ : ∀ {π τ} (t₁ t₂ : Term π τ) -> Set
t₁ ≅ᵀ t₂ = εᵀ t₁ ≡ εᵀ t₂

postulate _≈ᵀ_ : ∀ {π τ} -> Term π τ -> Term π τ -> Set
postulate ⌞_⌟ᵀ : ∀ {π τ} {t₁ t₂ : Term π τ} -> t₁ ≈ᵀ t₂ -> t₁ ≅ᵀ t₂
postulate ⌜_⌝ᵀ : ∀ {π τ} {t₁ t₂ : Term π τ} -> t₁ ≅ᵀ t₂ -> t₁ ≈ᵀ t₂

--------------------------------------------------------------------------------

_≅ᶜ_ : ∀ {l τ₁ τ₂} (C₁ C₂ : Cont l τ₁ τ₂) -> Set
C₁ ≅ᶜ C₂ = εᶜ C₁ ≡ εᶜ C₂

-- It is better to define structural low-equivalence with the graph
-- of the function whenever you have > 3 constructors, to avoid the
-- combinatorical explosion when proving ⌜_⌝
-- Depndency between the index may reduce the number of cases, but it
-- we still need lots of isignificant lemmas to extract information
-- from propositional equality proofs.
data _≈ᶜ_ {l} : ∀ {τ₁ τ₂} -> (C₁ C₂ : Cont l τ₁ τ₂) -> Set where
  Var : ∀ {τ₁ τ₂} {{π : Context}} -> (τ∈π : τ₁ ∈⟨ l ⟩ᴿ π) -> Var {τ₂ = τ₂} τ∈π ≈ᶜ Var τ∈π
  # : ∀ {τ} {{π : Context}} -> (τ∈π : τ ∈⟨ l ⟩ᴿ π)  -> # τ∈π ≈ᶜ # τ∈π
  Then_Else_ : ∀ {τ} {π : Context} {t₂ t₂' t₃ t₃' : Term π τ} -> t₂ ≈ᵀ t₂' -> t₃ ≈ᵀ t₃' -> (Then t₂ Else t₃) ≈ᶜ (Then t₂' Else t₃')
  Bind :  ∀ {τ₁ τ₂} {π : Context} {t₁ t₂ : Term π (τ₁ => Mac l τ₂)} -> t₁ ≈ᵀ t₂ -> Bind t₁ ≈ᶜ Bind t₂
  unlabel : ∀ {l' τ} (p : l' ⊑ l) -> unlabel {τ = τ} p ≈ᶜ unlabel p
  unId : ∀ {τ} -> unId {τ = τ} ≈ᶜ unId
  write : ∀ {τ H} {{π : Context}} {p : l ⊑ H} (τ∈π : τ ∈⟨ l ⟩ᴿ π) -> write p τ∈π ≈ᶜ write p τ∈π
  write' : ∀ {τ H} {{π : Context}} {p : l ⊑ H} (H⋤A : H ⋤ A) (τ∈π : τ ∈⟨ l ⟩ᴿ π) -> write p τ∈π ≈ᶜ write∙ p τ∈π
  write'' : ∀ {τ H} {{π : Context}} {p : l ⊑ H} (H⋤A : H ⋤ A) (τ∈π : τ ∈⟨ l ⟩ᴿ π) -> write∙ p τ∈π ≈ᶜ write p τ∈π
  write∙ : ∀ {τ H} {{π : Context}} (p : l ⊑ H) (τ∈π : τ ∈⟨ l ⟩ᴿ π) -> write∙ p τ∈π ≈ᶜ write∙ p τ∈π
  read : ∀ {τ L} -> (p : L ⊑ l) -> read {τ = τ} p ≈ᶜ read p

⌞_⌟ᶜ : ∀ {l τ₁ τ₂} {C₁ C₂ : Cont l τ₁ τ₂} -> C₁ ≈ᶜ C₂ -> C₁ ≅ᶜ C₂
⌞ Var τ∈π ⌟ᶜ = refl
⌞ # τ∈π ⌟ᶜ = refl
⌞ Then x Else x₁ ⌟ᶜ rewrite ⌞ x ⌟ᵀ | ⌞ x₁ ⌟ᵀ = refl
⌞ Bind x ⌟ᶜ rewrite ⌞ x ⌟ᵀ = refl
⌞ unlabel p ⌟ᶜ = refl
⌞ unId ⌟ᶜ = refl
⌞ write τ∈π ⌟ᶜ = refl
⌞ write' {H = H} H⋤A τ∈π ⌟ᶜ with H ⊑? A
... | yes p = ⊥-elim (H⋤A p)
... | no _ = refl
⌞ write'' {H = H} H⋤A τ∈π ⌟ᶜ with H ⊑? A
... | yes p = ⊥-elim (H⋤A p)
... | no _ = refl
⌞ write∙ p τ∈π ⌟ᶜ = refl
⌞ read p ⌟ᶜ = refl

split₁ᶜ : ∀ {l τ π₁ π₂} {t₁ t₂ : Term π₁ τ} {t₁' t₂' : Term π₂ τ} -> _≡_ {_} {Cont l _ _} (Then t₁ Else t₂) (Then t₁' Else t₂') -> π₁ ≡ π₂
split₁ᶜ refl = refl

split₂ᶜ : ∀ {l τ π} {t₁ t₂ t₁' t₂' : Term π τ} -> _≡_ {_} {Cont l _ _} (Then t₁ Else t₂) (Then t₁' Else t₂') -> t₁ ≡ t₁' × t₂ ≡ t₂'
split₂ᶜ refl = refl P., refl

split₃ᶜ : ∀ {l τ τ₂ π₁ π₂} {t₁ : Term π₁ (τ => Mac l τ₂)} {t₁' : Term π₂ (τ => Mac l τ₂)} -> _≡_ {_} {Cont l _ _} (Bind t₁) (Bind t₁') -> π₁ ≡ π₂
split₃ᶜ refl = refl

split₄ᶜ : ∀ {l τ₁ τ₂ π} {t₁ t₂ : Term π (τ₁ => Mac l τ₂)} -> _≡_ {_} {Cont l _ _} (Bind t₁) (Bind t₂) -> t₁ ≡ t₂
split₄ᶜ refl = refl

split₅ᶜ : ∀ {l τ₁ τ₂ π₁ π₂ H} {x : τ₁ ∈⟨ l ⟩ᴿ π₁} {y : τ₂ ∈⟨ l ⟩ᴿ π₂} {l⊑A l⊑A' : l ⊑ H} -> _≡_ {_} {Cont l _ _} (write l⊑A x) (write l⊑A' y)
          -> (τ₁ ≡ τ₂) × (π₁ ≡ π₂)
split₅ᶜ refl = refl P., refl

split₆ᶜ : ∀ {l τ π H} {x : τ ∈⟨ l ⟩ᴿ π} {y : τ ∈⟨ l ⟩ᴿ π} {l⊑A l⊑A' : l ⊑ H} -> _≡_ {_} {Cont l _ _} (write l⊑A x) (write l⊑A' y)
          -> x ≡ y × l⊑A ≡ l⊑A'
split₆ᶜ refl = refl P., refl

split∙₅ᶜ : ∀ {l τ₁ τ₂ π₁ π₂ H} {x : τ₁ ∈⟨ l ⟩ᴿ π₁} {y : τ₂ ∈⟨ l ⟩ᴿ π₂} {l⊑A l⊑A' : l ⊑ H} -> _≡_ {_} {Cont l _ _} (write∙ l⊑A x) (write∙ l⊑A' y)
          -> (τ₁ ≡ τ₂) × (π₁ ≡ π₂)
split∙₅ᶜ refl = refl P., refl

split∙₆ᶜ : ∀ {l τ π H} {x : τ ∈⟨ l ⟩ᴿ π} {y : τ ∈⟨ l ⟩ᴿ π} {l⊑A l⊑A' : l ⊑ H} -> _≡_ {_} {Cont l _ _} (write∙ l⊑A x) (write∙ l⊑A' y)
          -> x ≡ y × l⊑A ≡ l⊑A'
split∙₆ᶜ refl = refl P., refl


⌜_⌝ᶜ : ∀ {l τ₁ τ₂} {C₁ C₂ : Cont l τ₁ τ₂} -> C₁ ≅ᶜ C₂ -> C₁ ≈ᶜ C₂
⌜_⌝ᶜ {C₁ = SC.Var τ∈π₁} {SC.Var .τ∈π₁} refl = Var τ∈π₁
⌜_⌝ᶜ {C₁ = SC.# τ∈π₁} {SC.# .τ∈π₁} refl = # τ∈π₁
⌜_⌝ᶜ {C₁ = SC.# τ∈π} {SC.Then x Else x₁} ()
⌜_⌝ᶜ {C₁ = SC.# τ∈π} {SC.Bind x} ()
⌜_⌝ᶜ {C₁ = SC.Then x Else x₁} {SC.# τ∈π} ()
⌜_⌝ᶜ {C₁ = SC.Then x Else x₁} {SC.Then x₂ Else x₃} eq rewrite split₁ᶜ eq with split₂ᶜ eq
... | eq₁ P., eq₂ = Then ⌜ eq₁ ⌝ᵀ Else ⌜ eq₂ ⌝ᵀ
⌜_⌝ᶜ {C₁ = SC.Bind x} {SC.# τ∈π} ()
⌜_⌝ᶜ {C₁ = SC.Bind x} {SC.Bind x₁} eq rewrite split₃ᶜ eq = Bind ⌜ split₄ᶜ eq ⌝ᵀ
⌜_⌝ᶜ {C₁ = SC.unlabel p} {SC.unlabel .p} refl = unlabel p
⌜_⌝ᶜ {C₁ = SC.unId} {SC.unId} refl = unId
⌜_⌝ᶜ {C₁ = SC.write {H = H} x τ∈π} {SC.write x₁ τ∈π₁} eq with H ⊑? A
⌜_⌝ᶜ {C₁ = SC.write x τ∈π} {SC.write x₁ τ∈π₁} eq | yes p with split₅ᶜ eq
... | refl P., refl with split₆ᶜ eq
... | eq₁ P., eq₂ rewrite eq₁ | eq₂ = write τ∈π₁
⌜_⌝ᶜ {C₁ = SC.write x τ∈π} {SC.write x₁ τ∈π₁} eq | no ¬p with split∙₅ᶜ eq
... | refl P., refl with split∙₆ᶜ eq
... | eq₁ P., eq₂ rewrite eq₁ | eq₂ = write τ∈π₁
⌜_⌝ᶜ {C₁ = SC.write {H = H} x τ∈π} {SC.write∙ x₁ τ∈π₁} eq with H ⊑? A
⌜_⌝ᶜ {C₁ = SC.write {H = H} x τ∈π} {SC.write∙ x₁ τ∈π₁} () | yes p
⌜_⌝ᶜ {C₁ = SC.write x₁ τ∈π₁} {SC.write∙ .x₁ .τ∈π₁} refl | no p = write' p τ∈π₁
⌜_⌝ᶜ {C₁ = SC.write {H = H} x τ∈π} {SC.read x₁} eq with H ⊑? A
⌜_⌝ᶜ {C₁ = SC.write {H = H} x τ∈π} {SC.read x₁} () | yes p
⌜_⌝ᶜ {C₁ = SC.write {H = H} x τ∈π} {SC.read x₁} () | no p
⌜_⌝ᶜ {C₁ = SC.write∙ {H = H} x τ∈π} {SC.write x₁ τ∈π₁} eq with H ⊑? A
⌜_⌝ᶜ {C₁ = SC.write∙ x τ∈π} {SC.write x₁ τ∈π₁} () | yes p
⌜_⌝ᶜ {C₁ = SC.write∙ x τ∈π} {SC.write .x .τ∈π} refl | no ¬p = write'' ¬p τ∈π
⌜_⌝ᶜ {C₁ = SC.write∙ x₁ τ∈π₁} {SC.write∙ .x₁ .τ∈π₁} refl = write∙ x₁ τ∈π₁
⌜_⌝ᶜ {C₁ = SC.write∙ x τ∈π} {SC.read x₁} ()
⌜_⌝ᶜ {C₁ = SC.read x} {SC.write {H = H} x₁ τ∈π} eq with H ⊑? A
⌜_⌝ᶜ {C₁ = SC.read x} {SC.write x₁ τ∈π} () | yes _
⌜_⌝ᶜ {C₁ = SC.read x} {SC.write x₁ τ∈π} () | no _
⌜_⌝ᶜ {C₁ = SC.read x} {SC.write∙ x₁ τ∈π} ()
⌜_⌝ᶜ {C₁ = SC.read x} {SC.read .x} refl = read x

--------------------------------------------------------------------------------

_≅ˢ_ : ∀ {l τ₁ τ₂} (S₁ S₂ : Stack l τ₁ τ₂) -> Set
S₁ ≅ˢ S₂ = εˢ S₁ ≡ εˢ S₂

data _≈ˢ_ {l} : ∀ {τ₁ τ₂} -> (S₁ S₂ : Stack l τ₁ τ₂) -> Set where
  [] : ∀ {τ} -> [] {τ = τ} ≈ˢ []
  _∷_ : ∀ {τ₁ τ₂ τ₃} {C₁ C₂ : Cont l τ₁ τ₂} {S₁ S₂ : Stack l τ₂ τ₃} ->
          C₁ ≈ᶜ C₂ -> S₁ ≈ˢ S₂ -> (C₁ ∷ S₁) ≈ˢ (C₂ ∷ S₂)
  ∙ : ∀ {τ} -> ∙ {τ = τ} ≈ˢ ∙

⌞_⌟ˢ : ∀ {l τ₁ τ₂} {S₁ S₂ : Stack l τ₁ τ₂} -> S₁ ≈ˢ S₂ -> S₁ ≅ˢ S₂
⌞ [] ⌟ˢ = refl
⌞ x ∷ eq ⌟ˢ = cong₂ _∷_ ⌞ x ⌟ᶜ ⌞ eq ⌟ˢ
⌞ ∙ ⌟ˢ = refl

split₁ˢ : ∀ {l τ₁ τ₂ τ₂' τ₃ } {C₁ : Cont l τ₁ τ₂} {C₂ : Cont l τ₁ τ₂'}
          {S₁  : Stack l τ₂ τ₃} {S₂ : Stack l τ₂' τ₃} ->
           _≡_ {_} {Stack l τ₁ τ₃} (C₁ ∷ S₁) (C₂ ∷ S₂) -> τ₂ ≡ τ₂'
split₁ˢ refl = refl


split₂ˢ : ∀ {l τ₁ τ₂ τ₃} {C₁ C₂ : Cont l τ₁ τ₂} {S₁ S₂ : Stack l τ₂ τ₃} ->
           _≡_ {_} {Stack l τ₁ τ₃} (C₁ ∷ S₁)(C₂ ∷ S₂) -> C₁ ≡ C₂ × S₁ ≡ S₂
split₂ˢ refl = refl P., refl

⌜_⌝ˢ : ∀ {l τ₁ τ₂} {S₁ S₂ : Stack l τ₁ τ₂} -> S₁ ≅ˢ S₂ -> S₁ ≈ˢ S₂
⌜_⌝ˢ {S₁ = SC.[]} {SC.[]} eq = []
⌜_⌝ˢ {S₁ = SC.[]} {x SC.∷ S₂} ()
⌜_⌝ˢ {S₁ = SC.[]} {SC.∙} ()
⌜_⌝ˢ {S₁ = x SC.∷ S₁} {SC.[]} ()
⌜_⌝ˢ {S₁ = x SC.∷ S₁} {x₁ SC.∷ S₂} eq with split₁ˢ eq
... | refl with split₂ˢ eq
... | eq₂ P., eq₃ = ⌜ eq₂ ⌝ᶜ ∷ ⌜ eq₃ ⌝ˢ
⌜_⌝ˢ {S₁ = x SC.∷ S₁} {SC.∙} ()
⌜_⌝ˢ {S₁ = SC.∙} {SC.[]} ()
⌜_⌝ˢ {S₁ = SC.∙} {x SC.∷ S₂} ()
⌜_⌝ˢ {S₁ = SC.∙} {SC.∙} eq = ∙

--------------------------------------------------------------------------------

data _≈ᴹᵀ_ {π τ} : Maybe (Term π τ) -> Maybe (Term π τ) -> Set where
  nothing : nothing ≈ᴹᵀ nothing
  just : ∀ {t₁ t₂ : Term π τ} -> t₁ ≈ᵀ t₂ -> just t₁ ≈ᴹᵀ just t₂

_≅ᴹᵀ_ : ∀ {π τ} (mt₁ mt₂ : Maybe (Term π τ)) -> Set
mt₁ ≅ᴹᵀ mt₂ = M.map εᵀ mt₁ ≡ M.map εᵀ mt₂

⌜_⌝ᴹᵀ : ∀ {π τ} {mt₁ mt₂ : Maybe (Term π τ)} -> mt₁ ≅ᴹᵀ mt₂ -> mt₁ ≈ᴹᵀ mt₂
⌜_⌝ᴹᵀ {mt₁ = just x} {just x₁} eq = just ⌜ split eq ⌝ᵀ
  where split : ∀ {π τ} {t₁ t₂ : Term π τ} -> _≡_ {_} {Maybe (Term π τ)} (just t₁) (just t₂) -> t₁ ≡ t₂
        split refl = refl
⌜_⌝ᴹᵀ {mt₁ = just x} {nothing} ()
⌜_⌝ᴹᵀ {mt₁ = nothing} {just x} ()
⌜_⌝ᴹᵀ {mt₁ = nothing} {nothing} refl = nothing

--------------------------------------------------------------------------------

data _≈ᴱ_ {l} : ∀ {π} -> Env l π -> Env l π -> Set where
  [] : [] ≈ᴱ []
  _∷_ : ∀ {π τ} {Δ₁ Δ₂ : Env l π} {mt₁ mt₂ : Maybe (Term π τ)} -> mt₁ ≈ᴹᵀ mt₂ -> Δ₁ ≈ᴱ Δ₂ -> (mt₁ ∷ Δ₁) ≈ᴱ (mt₂ ∷ Δ₂)
  ∙ : ∀ {π} -> ∙ {{π = π}} ≈ᴱ ∙

_≅ᴱ_ : ∀ {π l} -> (Δ₁ Δ₂ : Env l π) -> Set
Δ₁ ≅ᴱ Δ₂ = εᴱ Δ₁ ≡ εᴱ Δ₂

⌜_⌝ᴱ : ∀ {l π} {Δ₁ Δ₂ : Env l π} -> Δ₁ ≅ᴱ Δ₂ -> Δ₁ ≈ᴱ Δ₂
⌜_⌝ᴱ {Δ₁ = SC.[]} {SC.[]} refl = []
⌜_⌝ᴱ {Δ₁ = SC.[]} {SC.∙} ()
⌜_⌝ᴱ {Δ₁ = t SC.∷ Δ₁} {t₁ SC.∷ Δ₂} eq =  ⌜ (proj₁ (split eq)) ⌝ᴹᵀ ∷ ⌜ proj₂ (split eq) ⌝ᴱ
  where split : ∀ {l π τ} {mt₁ mt₂ : Maybe (Term π τ)} {Δ₁ Δ₂ : Env l π} -> (mt₁ ∷ Δ₁) ≡ᴱ (mt₂ ∷ Δ₂) -> mt₁ ≡ mt₂ × Δ₁ ≡ Δ₂
        split refl = refl P., refl
⌜_⌝ᴱ {Δ₁ = t SC.∷ Δ₁} {SC.∙} ()
⌜_⌝ᴱ {Δ₁ = SC.∙} {SC.[]} ()
⌜_⌝ᴱ {Δ₁ = SC.∙} {t SC.∷ Δ₂} ()
⌜_⌝ᴱ {Δ₁ = SC.∙} {SC.∙} refl = ∙

⌞_⌟ᴱ : ∀ {l π} {Δ₁ Δ₂ : Env l π} -> Δ₁ ≈ᴱ Δ₂ -> Δ₁ ≅ᴱ Δ₂
⌞ [] ⌟ᴱ = refl
⌞ nothing ∷ eq ⌟ᴱ rewrite  ⌞ eq ⌟ᴱ = refl
⌞ just x ∷ eq ⌟ᴱ rewrite ⌞ x ⌟ᵀ | ⌞ eq ⌟ᴱ  = refl
⌞ ∙ ⌟ᴱ = refl

--------------------------------------------------------------------------------

data _≈ˣ⟨_⟩_ {l} : Heap l -> Dec (l ⊑ A) -> Heap l -> Set where
  ⟨_,_⟩ : ∀ {π} {l⊑A : l ⊑ A} {Δ₁ Δ₂ : Env l π} -> (M : Memory l) -> Δ₁ ≈ᴱ Δ₂ -> ⟨ M , Δ₁ ⟩ ≈ˣ⟨ yes l⊑A ⟩ ⟨ M , Δ₂ ⟩
  ∙ᴸ : {l⊑A : l ⊑ A} -> ∙ ≈ˣ⟨ yes l⊑A ⟩ ∙
  ∙ : ∀ {H₁ H₂ : Heap l} {l⋤A : l ⋤ A} -> H₁ ≈ˣ⟨ no l⋤A ⟩ H₂

--------------------------------------------------------------------------------

-- Structural low-equivalence for Heaps
data _≈ᴴ_ : ∀ {ls} -> Heaps ls -> Heaps ls -> Set where
  nil : [] ≈ᴴ []
  cons : ∀ {ls} {l} {u : Unique l ls} {Γ₁ Γ₂ : Heaps ls} {H₁ H₂ : Heap l} (x : Dec (l ⊑ A)) ->
               H₁ ≈ˣ⟨ x ⟩ H₂ -> Γ₁ ≈ᴴ Γ₂ -> (_∷_ {{u}} H₁ Γ₁) ≈ᴴ (_∷_ {{u}} H₂ Γ₂)


split : ∀ {ls} {l} {u₁ u₂ : Unique l ls} {Γ₁ Γ₂ : Heaps ls} {H₁ H₂ : Heap l} ->
                 _≡_ {_} {Heaps (l ∷ ls)}  (_∷_ {{u₁}} H₁ Γ₁) (_∷_ {{u₂}} H₂ Γ₂ ) -> u₁ ≡ u₂ × H₁ ≡ H₂ × Γ₁ ≡ Γ₂
split refl = refl P., refl P., refl

split₁ᴴ : ∀ {l π₁ π₂} {M₁ M₂ : Memory l} {Δ₁ : Env l π₁} {Δ₂ : Env l π₂} -> _≡_ {_} {Heap l} ⟨ M₁ , Δ₁ ⟩ ⟨ M₂ , Δ₂ ⟩ -> π₁ ≡ π₂ × M₁ ≡ M₂
split₁ᴴ refl = refl P., refl

split₂ᴴ : ∀ {l π} {M₁ M₂ : Memory l} {Δ₁ Δ₂ : Env l π} -> _≡_ {_} {Heap l} ⟨ M₁ , Δ₁ ⟩ ⟨ M₂ , Δ₂ ⟩ -> Δ₁ ≡ Δ₂
split₂ᴴ refl = refl

aux₂ : ∀ {l} {H₁ H₂ : Heap l} -> (x : Dec (l ⊑ A)) -> SE.εᴹ x H₁ ≡ SE.εᴹ x H₂ -> H₁ ≈ˣ⟨ x ⟩ H₂
aux₂ {H₁ = SC.⟨ x , x₁ ⟩} {SC.⟨ x₂ , x₃ ⟩} (yes p) eq with split₁ᴴ eq
aux₂ {l} {SC.⟨ M , x₁ ⟩} {SC.⟨ .M , x₃ ⟩} (yes p) eq₁ | refl P., refl = ⟨ M , ⌜ split₂ᴴ eq₁ ⌝ᴱ ⟩
aux₂ {H₁ = SC.⟨ x , x₁ ⟩} {SC.∙} (yes p) ()
aux₂ {H₁ = SC.∙} {SC.⟨ x , x₁ ⟩} (yes p) ()
aux₂ {H₁ = SC.∙} {SC.∙} (yes p) refl = ∙ᴸ
aux₂ (no ¬p) eq₁ = ∙

⌜_⌝ᴴ : ∀ {ls} {Γ₁ Γ₂ : Heaps ls} -> Γ₁ ≅ᴴ Γ₂ -> Γ₁ ≈ᴴ Γ₂
⌜_⌝ᴴ {Γ₁ = []} {[]} refl = nil
⌜_⌝ᴴ {Γ₁ = H₁ ∷ Γ₁} {H₂ ∷ Γ₂} eq with split eq
... | eq₁ P., eq₂ P., eq₃ rewrite eq₁ = cons (_ ⊑? A) (aux₂ (_ ⊑? A) eq₂) ⌜ eq₃ ⌝ᴴ

⌞_⌟ᴴ : ∀ {ls} {Γ₁ Γ₂ : Heaps ls} -> Γ₁ ≈ᴴ Γ₂ -> Γ₁ ≅ᴴ Γ₂
⌞ nil ⌟ᴴ = refl
⌞ cons {l = l}  (yes l⊑A) ⟨ M , x ⟩ eq₂ ⌟ᴴ with l ⊑? A
... | yes p rewrite ⌞ x ⌟ᴱ | ⌞ eq₂ ⌟ᴴ = refl
... | no ¬p = ⊥-elim (¬p l⊑A)
⌞ cons ._ ∙ᴸ eq₂ ⌟ᴴ rewrite ⌞ eq₂ ⌟ᴴ = refl
⌞ cons {l = l} (no _) ∙ eq₂ ⌟ᴴ rewrite ⌞ eq₂ ⌟ᴴ with l ⊑? A
⌞ cons (no l⋤A) ∙ eq₂ ⌟ᴴ | yes p = ⊥-elim (l⋤A p)
⌞ cons (no _) ∙ eq₂ ⌟ᴴ | no ¬p = refl

--------------------------------------------------------------------------------
