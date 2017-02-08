import Lattice as L
import Scheduler as S
open import Scheduler.Security

module Concurrent.Erasure {𝓛 : L.Lattice} {𝓢 : S.Scheduler 𝓛} (A : L.Label 𝓛) (𝓝 : NIˢ 𝓛 A 𝓢) where

open import Relation.Nullary
open import Types 𝓛

open import Sequential.Semantics 𝓛

open import Sequential.Erasure 𝓛 A as SE hiding (εᵀ ; εᴾ ; εˢ)
open import Sequential.PINI 𝓛 A using (stepᴸ ; stepᴴ-Γ)

--------------------------------------------------------------------------------
-- Temporarily side-step bug #2245
import Concurrent.Calculus as C
open C 𝓛 𝓢
-- open import Concurrent.Calculus 𝓛 𝓢

import Concurrent.Semantics as CS
open CS 𝓛 𝓢
-- open import Concurrent.Semantics 𝓛 𝓢 public

import Sequential.Calculus as SC
open SC 𝓛

--------------------------------------------------------------------------------

open Scheduler.Security.NIˢ 𝓛 A 𝓝 renaming (State to Stateˢ)

εᵗ : ∀ {l} ->  Thread l -> Thread l
εᵗ C.⟨ t , S ⟩ = ⟨ SE.εᵀ t , SE.εˢ S ⟩

εᵀ : ∀ {l} -> Dec (l ⊑ A) -> Pool l -> Pool l
εᵀ (yes p) C.[] = []
εᵀ (yes p) (t C.◅ T) = εᵗ t ◅ (εᵀ (yes p) T)
εᵀ (yes p) C.∙ = ∙
εᵀ (no ¬p) T = ∙

open import Relation.Binary.PropositionalEquality
open import Data.Empty

εᵀ-ext-≡ : ∀ {l} -> (x y : Dec (l ⊑ A)) (T : Pool l) -> εᵀ x T ≡ εᵀ y T
εᵀ-ext-≡ (yes p) (yes p₁) C.[] = refl
εᵀ-ext-≡ (yes p) (yes p₁) (t C.◅ T) rewrite εᵀ-ext-≡ (yes p) (yes p₁) T = refl
εᵀ-ext-≡ (yes p) (yes p₁) C.∙ = refl
εᵀ-ext-≡ (yes p) (no ¬p) T = ⊥-elim (¬p p)
εᵀ-ext-≡ (no ¬p) (yes p) T = ⊥-elim (¬p p)
εᵀ-ext-≡ (no ¬p) (no ¬p₁) T = refl

-- Pointwise erasure function for pools
εᴾ : ∀ {ls} -> Pools ls -> Pools ls
εᴾ C.[] = []
εᴾ (T C.◅ P) = (εᵀ (_ ⊑? A) T) ◅ (εᴾ P)

εᴳ : ∀ {ls} -> Global ls -> Global ls
εᴳ C.⟨ Σ , Γ , P ⟩ = C.⟨ εˢ Σ , εᴴ Γ , εᴾ P ⟩

import Data.Product as P

memberᴾ : ∀ {l ls} {T : Pool l} {P : Pools ls} -> (l⊑A : l ⊑ A) -> l ↦ T ∈ᴾ P -> l ↦ (εᵀ (yes l⊑A) T) ∈ᴾ (εᴾ P)
memberᴾ {l} l⊑A C.here with l ⊑? A
memberᴾ {T = T} l⊑A C.here | yes p rewrite εᵀ-ext-≡ (yes l⊑A) (yes p) T = here
memberᴾ l⊑A C.here | no ¬p = ⊥-elim (¬p l⊑A)
memberᴾ l⊑A (C.there x) = there (memberᴾ l⊑A x)

memberᵀ : ∀ {l n τ₁ π} {T : Pool l} {t : Term π τ₁} {S : Stack l _ _} -> (l⊑A : l ⊑ A)
          -> n ↦ ⟨ t , S ⟩ ∈ᵀ T -> n ↦ ⟨ SE.εᵀ t , SE.εˢ S ⟩ ∈ᵀ (εᵀ (yes l⊑A) T)
memberᵀ l⊑A C.here = C.here
memberᵀ l⊑A (C.there x) = C.there (memberᵀ l⊑A x)

updateᵀ : ∀ {l π τ n} {t : Term π τ} {S : Stack l _ _} {T₁ T₂ : Pool l} -> (l⊑A : l ⊑ A) -> T₂ ≔ T₁ [ n ↦ ⟨ t , S ⟩ ]ᵀ ->
          (εᵀ (yes l⊑A) T₂) ≔ (εᵀ (yes l⊑A) T₁) [ n ↦ ⟨ (SE.εᵀ t) , SE.εˢ S ⟩ ]ᵀ
updateᵀ l⊑A C.here = C.here
updateᵀ l⊑A (C.there x) = C.there (updateᵀ l⊑A x)

updateᴾ : ∀ {l ls} {T : Pool l} {P₁ P₂ : Pools ls} -> (l⊑A : l ⊑ A) -> P₂ ≔ P₁ [ l ↦ T ]ᴾ -> (εᴾ P₂) ≔ (εᴾ P₁) [ l ↦ (εᵀ (yes l⊑A) T) ]ᴾ
updateᴾ {l} l⊑A C.here with l ⊑? A
updateᴾ {T = T} l⊑A C.here | yes p rewrite εᵀ-ext-≡ (yes l⊑A) (yes p) T = here
updateᴾ l⊑A C.here | no ¬p = ⊥-elim (¬p l⊑A)
updateᴾ l⊑A (C.there x) = C.there (updateᴾ l⊑A x)


done-ε : ∀ {l ls τ} {p : Program l ls τ} -> (l⊑A : l ⊑ A) -> Doneᴾ p -> Doneᴾ (SE.ε₁ᴾ (yes l⊑A) p)
done-ε l⊑A (Done isVal) = Done (εᵀ-Val isVal)

-- Will probably need the graph of the function
stuck-ε : ∀ {l ls τ} {p : Program l ls τ} -> (l⊑A : l ⊑ A) -> Stuckᴾ p -> Stuckᴾ (SE.ε₁ᴾ (yes l⊑A) p)
stuck-ε {l} {ls} {τ} l⊑A (¬done P., ¬redex) = ε¬done ¬done P., ε¬redex ¬redex
  where ε¬done : {p : Program l ls τ} -> ¬ (Doneᴾ p) -> ¬ (Doneᴾ (ε₁ᴾ (yes l⊑A) p))
        ε¬done {⟨ Γ , t , [] ⟩} ¬done₁ (Done isVal) = εᵀ¬Val (¬Done⇒¬Val ¬done₁) isVal
        ε¬done {⟨ Γ , t , x ∷ S ⟩} ¬done₁ ()
        ε¬done {⟨ Γ , t , ∙ ⟩} ¬done₁ ()
        ε¬done {∙} ¬done₁ ()

        -- Lengthy boring proof, I will probably need the graph of the function εᴾ
        postulate ε¬redex : ∀ {p : Program l ls τ} -> ¬ (Redexᴾ p) -> ¬ (Redexᴾ (SE.ε₁ᴾ (yes l⊑A) p))


lengthᵀ-ε-≡ : ∀ {l} (l⊑A : l ⊑ A) (T : Pool l) -> lengthᵀ T ≡ lengthᵀ (εᵀ (yes l⊑A) T)
lengthᵀ-ε-≡ l⊑A C.[] = refl
lengthᵀ-ε-≡ l⊑A (t C.◅ T) rewrite lengthᵀ-ε-≡ l⊑A T = refl
lengthᵀ-ε-≡ l⊑A C.∙ = refl

εᵀ-▻-≡ : ∀ {l} (l⊑A : l ⊑ A) (T : Pool l) (t : Thread l) -> ((εᵀ (yes l⊑A) T) ▻ εᵗ t) ≡ εᵀ (yes l⊑A) (T ▻ t)
εᵀ-▻-≡ l⊑A C.[] t = refl
εᵀ-▻-≡ l⊑A (t C.◅ T) t₁ rewrite εᵀ-▻-≡ l⊑A T t₁ = refl
εᵀ-▻-≡ l⊑A C.∙ t = refl

updateᴾ-▻ : ∀ {l ls} {P₁ P₂ : Pools ls} (T : Pool l) (t : Thread l) -> (l⊑A : l ⊑ A) ->
                 P₁ ≔ P₂ [ l ↦ T ▻ t ]ᴾ ->
                 (εᴾ P₁) ≔ (εᴾ P₂) [ l ↦ (εᵀ (yes l⊑A) T) ▻ (εᵗ t) ]ᴾ
updateᴾ-▻ T t l⊑A x rewrite εᵀ-▻-≡ l⊑A T t = updateᴾ l⊑A x

newᴾ∙ : ∀ {H ls} {P₁ P₂ : Pools ls} (T : Pool H) (t : Thread H) -> (H⋤A : H ⋤ A) -> P₂ ≔ P₁ [ H ↦ T ▻ t ]ᴾ -> εᴾ P₂ ≡ εᴾ P₁
newᴾ∙ {H} T t H⋤A C.here with H ⊑? A
newᴾ∙ T t H⋤A C.here | yes p = ⊥-elim (H⋤A p)
newᴾ∙ T t H⋤A C.here | no ¬p = refl
newᴾ∙ T t H⋤A (C.there x) rewrite newᴾ∙ T t H⋤A x = refl

updateᴾ∙ : ∀ {H ls} {P₁ P₂ : Pools ls} {T : Pool H} -> H ⋤ A -> P₂ ≔ P₁ [ H ↦ T ]ᴾ -> εᴾ P₁ ≡  εᴾ P₂
updateᴾ∙ {H} H⋤A C.here with H ⊑? A
updateᴾ∙ H⋤A C.here | yes p = ⊥-elim (H⋤A p)
updateᴾ∙ H⋤A C.here | no ¬p = refl
updateᴾ∙ H⋤A (C.there x) rewrite updateᴾ∙ H⋤A x = refl
