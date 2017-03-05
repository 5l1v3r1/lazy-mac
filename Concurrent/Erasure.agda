import Lattice as L
import Scheduler as S
open import Scheduler.Security

module Concurrent.Erasure {𝓛 : L.Lattice} {𝓢 : S.Scheduler 𝓛} (A : L.Label 𝓛) (𝓝 : NIˢ 𝓛 A 𝓢) where

open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Relation.Nullary

open import Types 𝓛

open import Sequential.Calculus 𝓛
open import Sequential.Security.Erasure 𝓛 A using (εᵀˢ ; εᵀˢ-ext-≡ ; map-εᴹ ; map-εᴴ)

open import Concurrent.Calculus 𝓛 𝓢

open Scheduler.Security.NIˢ 𝓛 A 𝓝 hiding (State)

--------------------------------------------------------------------------------

map-εᵀ : ∀ {l} -> l ⊑ A -> Pool l -> Pool l
map-εᵀ l⊑A  [] = []
map-εᵀ l⊑A (t ◅ P) = εᵀˢ (yes l⊑A) t ◅ map-εᵀ l⊑A P
map-εᵀ l⊑A ∙ = ∙

εᴾ : ∀ {l} -> Dec (l ⊑ A) -> Pool l -> Pool l
εᴾ (yes l⊑A) P = map-εᵀ l⊑A P
εᴾ (no _) P = ∙


εᴾ-ext-≡ : ∀ {l} -> (x y : Dec (l ⊑ A)) (T : Pool l) -> εᴾ x T ≡ εᴾ y T
εᴾ-ext-≡ (yes p) (yes p₁) [] = refl
εᴾ-ext-≡ (yes p) (yes p₁) (t ◅ T) with εᵀˢ-ext-≡ (yes p) (yes p₁) t | εᴾ-ext-≡ (yes p) (yes p₁) T
... | eq₁ | eq₂ rewrite eq₁ | eq₂ = refl
εᴾ-ext-≡ (yes p) (yes p₁) ∙ = refl
εᴾ-ext-≡ (yes p) (no ¬p) T = ⊥-elim (¬p p)
εᴾ-ext-≡ (no ¬p) (yes p) T = ⊥-elim (¬p p)
εᴾ-ext-≡ (no ¬p) (no ¬p₁) T = refl

-- Pointwise erasure function for pools
map-εᴾ : ∀ {ls} -> Pools ls -> Pools ls
map-εᴾ [] = []
map-εᴾ (T ◅ P) = (εᴾ (_ ⊑? A) T) ◅ (map-εᴾ P)

εᴳ : ∀ {ls} -> Global ls -> Global ls
εᴳ ⟨ Σ , Ms , Γ , P ⟩ = ⟨ εˢ Σ , map-εᴹ Ms , map-εᴴ Γ , map-εᴾ P ⟩

open import Data.Product as P

memberᴾ : ∀ {l ls} {T : Pool l} {P : Pools ls} -> (l⊑A : l ⊑ A) -> l ↦ T ∈ᴾ P -> l ↦ (εᴾ (yes l⊑A) T) ∈ᴾ (map-εᴾ P)
memberᴾ {l} l⊑A here with l ⊑? A
memberᴾ {T = T} l⊑A here | yes p rewrite εᴾ-ext-≡ (yes l⊑A) (yes p) T = here
memberᴾ l⊑A here | no ¬p = ⊥-elim (¬p l⊑A)
memberᴾ l⊑A (there x) = there (memberᴾ l⊑A x)

memberᵀ : ∀ {l n} {T : Pool l} {Ts : Thread _} -> (l⊑A : l ⊑ A)
          -> n ↦ Ts ∈ᵀ T -> n ↦ (εᵀˢ (yes l⊑A) Ts) ∈ᵀ (εᴾ (yes l⊑A) T)
memberᵀ l⊑A here = here
memberᵀ l⊑A (there x) = there (memberᵀ l⊑A x)

updateᵀᴸ : ∀ {l n} {Ts : Thread _}  {T₁ T₂ : Pool l} -> (l⊑A : l ⊑ A) -> T₂ ≔ T₁ [ n ↦ Ts ]ᵀ ->
          (εᴾ (yes l⊑A) T₂) ≔ (εᴾ (yes l⊑A) T₁) [ n ↦ εᵀˢ (yes l⊑A) Ts ]ᵀ
updateᵀᴸ l⊑A here = here
updateᵀᴸ l⊑A (there x) = there (updateᵀᴸ l⊑A x)

updateᴾᴸ : ∀ {l ls} {T : Pool l} {P₁ P₂ : Pools ls} -> (l⊑A : l ⊑ A) -> P₂ ≔ P₁ [ l ↦ T ]ᴾ -> (map-εᴾ P₂) ≔ (map-εᴾ P₁) [ l ↦ (εᴾ (yes l⊑A) T) ]ᴾ
updateᴾᴸ {l} l⊑A here with l ⊑? A
updateᴾᴸ {T = T} l⊑A here | yes p rewrite εᴾ-ext-≡ (yes l⊑A) (yes p) T = here
updateᴾᴸ l⊑A here | no ¬p = ⊥-elim (¬p l⊑A)
updateᴾᴸ l⊑A (there x) = there (updateᴾᴸ l⊑A x)

--------------------------------------------------------------------------------

lengthᵀ-ε-≡ : ∀ {l} (l⊑A : l ⊑ A) (T : Pool l) -> lengthᵀ T ≡ lengthᵀ (εᴾ (yes l⊑A) T)
lengthᵀ-ε-≡ l⊑A [] = refl
lengthᵀ-ε-≡ l⊑A (t ◅ T) rewrite lengthᵀ-ε-≡ l⊑A T = refl
lengthᵀ-ε-≡ l⊑A ∙ = refl

εᴾ-▻-≡ : ∀ {l} (l⊑A : l ⊑ A) (T : Pool l) (t : Thread l) -> ((εᴾ (yes l⊑A) T) ▻ εᵀˢ (yes l⊑A) t) ≡ εᴾ (yes l⊑A) (T ▻ t)
εᴾ-▻-≡ l⊑A [] t = refl
εᴾ-▻-≡ l⊑A (t ◅ T) t₁ with εᴾ-▻-≡ l⊑A T t₁
... | eq rewrite eq = refl
εᴾ-▻-≡ l⊑A ∙ t = refl

updateᴾ-▻ : ∀ {l ls} {P₁ P₂ : Pools ls} (T : Pool l) (t : Thread l) -> (l⊑A : l ⊑ A) ->
                 P₁ ≔ P₂ [ l ↦ T ▻ t ]ᴾ ->
                 (map-εᴾ P₁) ≔ (map-εᴾ P₂) [ l ↦ (εᴾ (yes l⊑A) T) ▻ (εᵀˢ (yes l⊑A) t) ]ᴾ
updateᴾ-▻ {l} T t l⊑A x with εᴾ-▻-≡ l⊑A T t
... | eq rewrite eq = updateᴾᴸ l⊑A x

newᴾ∙ : ∀ {H ls} {P₁ P₂ : Pools ls} (T : Pool H) (t : Thread H) -> (H⋤A : H ⋤ A) -> P₂ ≔ P₁ [ H ↦ T ▻ t ]ᴾ -> map-εᴾ P₂ ≡ map-εᴾ P₁
newᴾ∙ {H} T t H⋤A here with H ⊑? A
newᴾ∙ T t H⋤A here | yes p = ⊥-elim (H⋤A p)
newᴾ∙ T t H⋤A here | no ¬p = refl
newᴾ∙ T t H⋤A (there x) rewrite newᴾ∙ T t H⋤A x = refl

updateᴾ∙ : ∀ {H ls} {P₁ P₂ : Pools ls} {T : Pool H} -> H ⋤ A -> P₂ ≔ P₁ [ H ↦ T ]ᴾ -> map-εᴾ P₁ ≡  map-εᴾ P₂
updateᴾ∙ {H} H⋤A here with H ⊑? A
updateᴾ∙ H⋤A here | yes p = ⊥-elim (H⋤A p)
updateᴾ∙ H⋤A here | no ¬p = refl
updateᴾ∙ H⋤A (there x) rewrite updateᴾ∙ H⋤A x = refl
