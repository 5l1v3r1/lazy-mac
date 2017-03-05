import Lattice as L₁

module Sequential.Security.Lemmas2 (𝓛 : L₁.Lattice) (A : L₁.Label 𝓛) where

import Types as T
open T 𝓛

open import Sequential.Security.Erasure 𝓛 A as SE hiding (updateᴹ)
import Sequential.Security.Graph as G
open G 𝓛 A

--------------------------------------------------------------------------------
-- Temporarily side-step bug #2245

import Sequential.Calculus as SC
open SC 𝓛

--------------------------------------------------------------------------------

import Sequential.Semantics as SS
open SS 𝓛

import Sequential.Security.LowEq as L renaming (⟨_,_,_⟩ to is≈ᴾ)
open L 𝓛 A


import Sequential.Valid as V hiding (memberˢ ; updateˢ ; memberᴱ ; updateᴱ )
open V 𝓛

open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Relation.Nullary
open import Data.Product
open import Data.Maybe

val-≈ : ∀ {π τ} {t₁ t₂ : Term π τ} -> t₁ ≈ᵀ t₂ -> Value t₁ -> Value t₂
val-≈ L.⟨ e₁ , e₂ ⟩ val = valᴱ e₂ (val₁ᴱ e₁ val)

var-≈ : ∀ {π τ} {t₁ t₂ : Term π τ} -> t₁ ≈ᵀ t₂ -> IsVar t₁ -> IsVar t₂
var-≈ L.⟨ G.Var τ∈π , G.Var .τ∈π ⟩ (SC.Var .τ∈π) = SC.Var τ∈π

¬var-≈ : ∀ {π τ} {t₁ t₂ : Term π τ} -> t₁ ≈ᵀ t₂ -> ¬ (IsVar t₁) -> ¬ (IsVar t₂)
¬var-≈ eq = contrapositive (var-≈ (sym-≈ᵀ eq))

done-≈ : ∀ {l τ} {Ts₁ Ts₂ : TS∙ l τ} {l⊑A : l ⊑ A} -> Ts₁ ≈ᵀˢ⟨ (yes l⊑A) ⟩ Ts₂ -> IsDoneTS Ts₁ -> IsDoneTS Ts₂
done-≈ (Kᵀˢ G.⟨ x₃ , G.[] ⟩ G.⟨ x₁ , G.[] ⟩) (SS.isDoneTS isVal) = isDoneTS (val-≈ L.⟨ x₃ , x₁ ⟩ isVal)

fork-≈ : ∀ {π τ} {t₁ t₂ : Term π τ} -> t₁ ≈ᵀ t₂ -> (IsFork t₁) -> (IsFork t₂)
fork-≈ t₁≈t₂ isFork = fork-≈' isFork t₁≈t₂
  where -- Pattern matching in the original order hits a bug.
        fork-≈' : ∀ {π τ} {t₁ t₂ : Term π τ} -> (IsFork t₁) -> t₁ ≈ᵀ t₂ -> (IsFork t₂)
        fork-≈' (SC.Fork p t) L.⟨ G.fork .p h⊑A e₁ , G.fork .p h⊑A₁ e₂ ⟩ = SC.Fork p _
        fork-≈' (SC.Fork p t) L.⟨ G.fork' .p h⋤A e₁ , G.fork' .p h⋤A₁ e₂ ⟩ = SC.Fork p _
        fork-≈' (SC.Fork p t) L.⟨ G.fork' .p h⋤A e₁ , G.fork∙ .p e₂ ⟩ = SC.Fork∙ p _
        fork-≈' (SC.Fork∙ p t) L.⟨ G.fork∙ .p e₁ , G.fork' .p h⋤A e₂ ⟩ = SC.Fork p _
        fork-≈' (SC.Fork∙ p t) L.⟨ G.fork∙ .p e₁ , G.fork∙ .p e₂ ⟩ = SC.Fork∙ p _

forkTS-≈ : ∀ {l τ} {Ts₁ Ts₂ : TS∙ l τ} {l⊑A : l ⊑ A} -> Ts₁ ≈ᵀˢ⟨ yes l⊑A ⟩ Ts₂ -> (IsForkTS Ts₁) -> (IsForkTS Ts₂)
forkTS-≈ (Kᵀˢ G.⟨ eᵀ₁ , eˢ₁ ⟩ G.⟨ eᵀ , eˢ ⟩) (SS.isForkTS isFork) = SS.isForkTS (fork-≈ L.⟨ eᵀ₁ , eᵀ ⟩ isFork)

open import Data.Product as P
open import Function
import Sequential.Calculus renaming (⟨_,_,_⟩ to mkᴾ ; ⟨_,_⟩ to mkᵀ)

member-≈ᴴ : ∀ {l π₁ π₂ τ} {Δ₁ Δ₂ : Heap l π₁} {t₁ : Term π₂ τ} {τ∈π : τ ∈⟨ l ⟩ᴿ π₁} -> Δ₁ map-≈ᵀ Δ₂ -> τ∈π ↦ t₁ ∈ᴴ Δ₁ ->
            Σ (Term π₂ τ) (λ t₂ → t₁ ≈ᵀ t₂ × τ∈π ↦ t₂ ∈ᴴ Δ₂)
member-≈ᴴ {τ∈π = τ∈π} Δ₁≈Δ₂ t∈Δ = aux Δ₁≈Δ₂ t∈Δ
  where aux : ∀ {l π₁ π₂ τ} {Δ₁ Δ₂ : Heap l π₁} {t₁ : Term π₂ τ} {τ∈π : τ ∈⟨ l ⟩ π₁} -> Δ₁ map-≈ᵀ Δ₂ -> Memberᴴ (just t₁) τ∈π Δ₁ ->
              Σ (Term π₂ τ) (λ t₂ → t₁ ≈ᵀ t₂ × Memberᴴ (just t₂) τ∈π Δ₂)
        aux (L.K-mapᵀ (G.just x G.∷ e₁) (G.just x₁ G.∷ e₂)) SC.here = _ , L.⟨ x , x₁ ⟩ , here
        aux (L.K-mapᵀ (x G.∷ e₁) (x₁ G.∷ e₂)) (SC.there t∈Δ₁) = P.map id (P.map id there) (aux (L.K-mapᵀ e₁ e₂) t∈Δ₁)

-- update-≈ᴴ : ∀ {l π₁ π₂ τ} {Δ₁ Δ₁' Δ₂ : Heap l π₁} {mt₁ mt₂ : Maybe (Term π₂ τ)} {τ∈π : τ ∈⟨ l ⟩ π₁} ->
--               Δ₁ map-≈ᵀ Δ₂ -> mt₁ ≈ᴹᵀ mt₂ -> Updateᴴ mt₁ τ∈π Δ₁ Δ₁' -> Σ (Heap l π₁) (λ Δ₂' → Updateᴴ mt₂ τ∈π Δ₂ Δ₂')
-- update-≈ᴴ Δ₁≈Δ₂ mt₁≈mt₂ u = {!!}

member-≈ᴱ : ∀ {l ls π} {Γ₁ Γ₂ : Heaps ls} {Δ₁ : Heap l π} (l⊑A : l ⊑ A) -> Γ₁ map-≈ᴴ Γ₂ -> l ↦ ⟨ Δ₁ ⟩ ∈ᴱ Γ₁ ->
            Σ (Heap l π) (λ Δ₂ → ⟨ Δ₁ ⟩ ≈ᴴ⟨ yes l⊑A ⟩ ⟨ Δ₂ ⟩ × l ↦ ⟨ Δ₂ ⟩ ∈ᴱ Γ₂)
member-≈ᴱ {l} l⊑A (L.K-mapᴴ (x₁ G.∷ x₄) (x₂ G.∷ x₃)) SC.here with l ⊑? A
member-≈ᴱ l⊑A (L.K-mapᴴ (G.Mapᵀ l⊑A₁ x G.∷ x₄) (G.Mapᵀ .l⊑A₁ x₁ G.∷ x₃)) SC.here | .(yes l⊑A₁) = _ , ((L.Kᴴ (G.Mapᵀ l⊑A x) (G.Mapᵀ l⊑A x₁)) , here)
member-≈ᴱ l⊑A (L.K-mapᴴ (G.∙ G.∷ x₄) (G.∙ G.∷ x₃)) SC.here | (no l⋤A) = ⊥-elim (l⋤A l⊑A)
member-≈ᴱ l⊑A (L.K-mapᴴ (x₃ G.∷ x₂) (x G.∷ x₁)) (SC.there l∈Γ) = P.map id (P.map id there) (member-≈ᴱ l⊑A (L.K-mapᴴ x₂ x₁) l∈Γ)

update-≈ᴱ : ∀ {l ls} {Γ₁ Γ₁' Γ₂ : Heaps ls} {H₁ H₂ : Heap∙ l} -> Γ₁ map-≈ᴴ Γ₂ -> Γ₁' ≔ Γ₁ [ l ↦ H₁ ]ᴱ ->
            ∃ (λ Γ₂' → Γ₂' ≔ Γ₂ [ l ↦ H₂ ]ᴱ)
update-≈ᴱ (L.K-mapᴴ (x₃ G.∷ x₂) (x G.∷ x₁)) SC.here = _ , here
update-≈ᴱ (L.K-mapᴴ (x₃ G.∷ x₂) (x G.∷ x₁)) (SC.there u₁) = P.map (_∷_ _) there (update-≈ᴱ (L.K-mapᴴ x₂ x₁) u₁)

member-≈ˢ : ∀ {l ls} {Ms₁ Ms₂ : Memories ls} {M₁ : Memory l} (x : Dec (l ⊑ A)) -> Ms₁ map-≈ᴹ Ms₂ -> l ↦ M₁ ∈ˢ Ms₁ ->
          ∃ (λ M₂ →  M₁ ≈ᴹ⟨ x ⟩ M₂ × l ↦ M₂ ∈ˢ Ms₂)
member-≈ˢ d (L.K-mapᴹ (x G.∷ x₃) (x₁ G.∷ x₂)) SC.here = _ , L.Kᴹ (ext-εᴹ d x) (ext-εᴹ d x₁) , here
member-≈ˢ d (L.K-mapᴹ (x₃ G.∷ x₂) (x G.∷ x₁)) (SC.there l∈Ms) = P.map id (P.map id there) (member-≈ˢ d (L.K-mapᴹ x₂ x₁) l∈Ms)

update-≈ˢ :  ∀ {l ls} {Ms₁ Ms₁' Ms₂ : Memories ls} {M₁ M₂ : Memory l} ->  Ms₁ map-≈ᴹ Ms₂ ->
               Ms₁' ≔ Ms₁ [ l ↦ M₁ ]ˢ -> ∃ (λ Ms₂' → Ms₂' ≔ Ms₂ [ l ↦ M₂ ]ˢ)
update-≈ˢ (L.K-mapᴹ (x₃ G.∷ x₂) (x G.∷ x₁)) SC.here = _ , here
update-≈ˢ (L.K-mapᴹ (x₃ G.∷ x₂) (x G.∷ x₁)) (SC.there u₁) = P.map (_∷_ _) there (update-≈ˢ (L.K-mapᴹ x₂ x₁) u₁)

updateᴹ : ∀ {l τ n} {M₁ M₁' M₂ : Memory l} {c : Cell l τ} {l⊑A : l ⊑ A} ->
            M₁ ≈ᴹ⟨ yes l⊑A ⟩ M₂ -> M₁' ≔ M₁ [ n ↦ c ]ᴹ -> ∃ (λ M₂' → M₂' ≔ M₂ [ n ↦ c ]ᴹ)
updateᴹ (L.Kᴹ (G.Id l⊑A) (G.Id .l⊑A)) SC.here = _ , SC.here
updateᴹ (L.Kᴹ (G.Id l⊑A) (G.Id .l⊑A)) (SC.there u) = P.map (_∷_ _) there (updateᴹ (L.Kᴹ (G.Id l⊑A) (G.Id l⊑A)) u)

member-≈ᴹ : ∀ {l τ n} {l⊑A : l ⊑ A} {M₁ M₂ : Memory l} {c : Cell l τ} -> M₁ ≈ᴹ⟨ yes l⊑A ⟩ M₂ -> n ↦ c ∈ᴹ M₁ -> n ↦ c ∈ᴹ M₂
member-≈ᴹ (L.Kᴹ (G.Id l⊑A) (G.Id .l⊑A)) n∈M = n∈M

redex⟼ : ∀ {ls l π τ τ'} {Ms₁ Ms₂ : Memories ls} {Γ₁ Γ₂ : Heaps ls} {p₁' : Program l ls τ}
             {t₁ t₂ : Term π τ'} {S₁ S₂ : Stack _ _ _ _} {l⊑A : l ⊑ A} ->
             let p₁ = SC.mkᴾ Ms₁  Γ₁ (SC.mkᵀ t₁  S₁)
                 p₂ = SC.mkᴾ Ms₂  Γ₂ (SC.mkᵀ t₂ S₂) in
             validᴾ p₁ -> validᴾ p₂ ->  Ms₁ map-≈ᴹ Ms₂ -> Γ₁ map-≈ᴴ Γ₂ -> t₁ ≈ᵀ t₂ -> S₁ ≈ˢ S₂ ->
             p₁ ⟼ p₁' -> Redexᴾ p₂
redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ t₁≈t₂ S₁≈S₂ (SS.Pure l∈Γ step uᴹ) = {!!}
redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.new l⊑H h⊑A (G.Var ._) , G.new .l⊑H h⊑A₁ (G.Var ._) ⟩ S₁≈S₂ (SS.New H∈Ms uᴹ)
  with member-≈ˢ (yes h⊑A) Ms₁≈Ms₂ H∈Ms
... | M₂ , M₁≈M₂ , H∈Ms' with update-≈ˢ Ms₁≈Ms₂ uᴹ
... | Ms₂' , uᴹ' = Step (New H∈Ms' uᴹ' )
redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.new' l⊑H h⋤A (G.Var ._) , G.new' .l⊑H h⋤A₁ (G.Var ._) ⟩ S₁≈S₂ (SS.New H∈Ms uᴹ)
  with member-≈ˢ (no h⋤A) Ms₁≈Ms₂ H∈Ms
... | M₂ , M₁≈M₂ , H∈Ms' with update-≈ˢ Ms₁≈Ms₂ uᴹ
... | Ms₂' , uᴹ' = Step (New H∈Ms' uᴹ' )
redex⟼ v₁ (proj₁ , proj₂ , () , proj₃) Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.new' l⊑H h⋤A e₁ , G.new∙ .l⊑H e₂ ⟩ S₁≈S₂ (SS.New H∈Ms uᴹ)
redex⟼ (proj₁ , proj₂ , () , proj₃) v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ t₁≈t₂ S₁≈S₂ SS.New∙
redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.Res x G.#[ n ] , G.Res x₁ G.#[ .n ] ⟩ (L.Kˢ (G.write l⊑H H⊑A ._ G.∷ x₄) (G.write .l⊑H H⊑A₁ ._ G.∷ x₂)) (SS.Write₂ H∈Ms uᴹ uˢ)
  with member-≈ˢ (yes H⊑A) Ms₁≈Ms₂ H∈Ms
... | M₂ , M₁≈M₂ , H∈Ms' with updateᴹ M₁≈M₂ uᴹ
... | M₂' , uᴹ' with update-≈ˢ Ms₁≈Ms₂ uˢ
... | Ms₂' , uˢ' = Step (Write₂ H∈Ms' uᴹ' uˢ')
redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.Res x _ , G.Res x₁ _ ⟩ (L.Kˢ (G.write' l⊑H H⋤A ._ G.∷ x₄) (G.write' .l⊑H H⋤A₁ ._ G.∷ x₂)) (SS.Write₂ H∈Ms uᴹ uˢ)
  = ⊥-elim (H⋤A₁ x₁)
redex⟼ v₁ (proj₁ , proj₂ , proj₃ , () , proj₄) Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.Res x e₁ , G.Res x₁ e₂ ⟩ (L.Kˢ (G.write' l⊑H H⋤A ._ G.∷ x₄) (G.write∙ .l⊑H ._ G.∷ x₂)) (SS.Write₂ H∈Ms uᴹ uˢ)
redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.Res∙ x , G.Res x₁ e₂ ⟩ (L.Kˢ (x₅ G.∷ x₄) (x₃ G.∷ x₂)) (SS.Write₂ H∈Ms uᴹ uˢ) = ⊥-elim (x x₁)
redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.Res∙ x₁ , G.Res∙ x₂ ⟩ (L.Kˢ (G.write l⊑H H⊑A ._ G.∷ x₄) (G.write .l⊑H H⊑A₁ ._ G.∷ x)) (SS.Write₂ H∈Ms uᴹ uˢ)
  = ⊥-elim (x₂ H⊑A₁)

redex⟼ (proj₁ , proj₂ , (l∈ls , n , V.is#[ .n ] , isV) , r₂) (proj₃ , proj₄ , (l∈ls' , n' , V.is#[ .n' ] , isV') , r₃) Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.Res∙ x₁ , G.Res∙ x₂ ⟩ (L.Kˢ (G.write' l⊑H H⋤A ._ G.∷ x₄) (G.write' .l⊑H H⋤A₁ ._ G.∷ x)) (SS.Write₂ H∈Ms uᴹ uˢ)
  with updateᴹ-valid (SC.∥ l⊑H , _ ∥) isV'
... | M₂' , uᴹ' with update-≈ˢ Ms₁≈Ms₂ uˢ
... | Ms₂' , uˢ' = Step (Write₂ (lookup-∈ˢ l∈ls' _) uᴹ' uˢ')

redex⟼ (proj₁ , proj₂ , (l∈ls , n , V.is#[ .n ] , isV) , r₂) (proj₃ , proj₄ , (l∈ls' , n' , V.is#[ .n' ]ᴰ , isV') , r₃) Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.Res∙ x₁ , G.Res∙ x₂ ⟩ (L.Kˢ (G.write' l⊑H H⋤A ._ G.∷ x₄) (G.write' .l⊑H H⋤A₁ ._ G.∷ x)) (SS.Write₂ H∈Ms uᴹ uˢ)
  with updateᴹ-valid (SC.∥ l⊑H , _ ∥) isV'
... | M₂' , uᴹ' with update-≈ˢ Ms₁≈Ms₂ uˢ
... | Ms₂' , uˢ' = Step (Writeᴰ₂ (lookup-∈ˢ l∈ls' _) uᴹ' uˢ')

redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.Res∙ x₁ , G.Res∙ x₂ ⟩ (L.Kˢ (G.write' l⊑H H⋤A ._ G.∷ x₄) (G.write∙ .l⊑H ._ G.∷ x)) (SS.Write₂ H∈Ms uᴹ uˢ)
  = ⊥-elim (proj₁ (proj₂ (proj₂ (proj₂ v₂))))

redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.Res x G.#[ n ]ᴰ , G.Res x₁ G.#[ .n ]ᴰ ⟩ (L.Kˢ (G.write l⊑H H⊑A ._ G.∷ x₃) (G.write .l⊑H H⊑A₁ ._ G.∷ x₂)) (SS.Writeᴰ₂ H∈Ms uᴹ uˢ)
  with member-≈ˢ (yes H⊑A) Ms₁≈Ms₂ H∈Ms
... | M₂ , M₁≈M₂ , H∈Ms' with updateᴹ M₁≈M₂ uᴹ
... | M₂' , uᴹ' with update-≈ˢ Ms₁≈Ms₂ uˢ
... | Ms₂' , uˢ' = Step (Writeᴰ₂ H∈Ms' uᴹ' uˢ')

redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.Res x e₁ , G.Res x₁ e₂ ⟩ (L.Kˢ (G.write' l⊑H H⋤A ._ G.∷ x₃) (_ G.∷ x₂)) (SS.Writeᴰ₂ H∈Ms uᴹ uˢ) = ⊥-elim (H⋤A x₁)

redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.Res∙ x , G.Res x₁ e₂ ⟩ (L.Kˢ x₃ x₂) (SS.Writeᴰ₂ H∈Ms uᴹ uˢ) = ⊥-elim (x x₁)
redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.Res∙ x , G.Res∙ x₁ ⟩ (L.Kˢ (G.write l⊑H H⊑A ._ G.∷ x₃) x₂) (SS.Writeᴰ₂ H∈Ms uᴹ uˢ) = ⊥-elim (x₁ H⊑A)
redex⟼ (proj₁ , proj₂ , (l∈ls , n , V.is#[ .n ]ᴰ , isV) , r₂) (proj₃ , proj₄ , (l∈ls' , n' , V.is#[ .n' ] , isV') , r₃) Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.Res∙ x , G.Res∙ x₁ ⟩ (L.Kˢ (G.write' l⊑H H⋤A ._ G.∷ x₃) (G.write' .l⊑H H⋤A₁ ._ G.∷ x₂)) (SS.Writeᴰ₂ H∈Ms uᴹ uˢ)
  with updateᴹ-valid (SC.∥ l⊑H , _ ∥) isV'
... | M₂' , uᴹ' with update-≈ˢ Ms₁≈Ms₂ uˢ
... | Ms₂' , uˢ' = SS.Step (Write₂ (lookup-∈ˢ l∈ls' _) uᴹ' uˢ')

redex⟼ (proj₁ , proj₂ , (l∈ls , n , V.is#[ .n ]ᴰ , isV) , r₂) (proj₃ , proj₄ , (l∈ls' , n' , V.is#[ .n' ] , isV') , () , r₃) Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.Res∙ x , G.Res∙ x₁ ⟩ (L.Kˢ (G.write' l⊑H H⋤A ._ G.∷ x₃) (G.write∙ .l⊑H ._ G.∷ x₂)) (SS.Writeᴰ₂ H∈Ms uᴹ uˢ)
redex⟼ (proj₁ , proj₂ , (l∈ls , n , V.is#[ .n ]ᴰ , isV) , r₂) (proj₃ , proj₄ , (l∈ls' , n' , V.is#[ .n' ]ᴰ , isV') , r₃) Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.Res∙ x , G.Res∙ x₁ ⟩ (L.Kˢ (G.write' l⊑H H⋤A ._ G.∷ x₃) (G.write' .l⊑H H⋤A₁ ._ G.∷ x₂)) (SS.Writeᴰ₂ H∈Ms uᴹ uˢ)
  with updateᴹ-valid (SC.∥ l⊑H , _ ∥) isV'
... | M₂' , uᴹ' with update-≈ˢ Ms₁≈Ms₂ uˢ
... | Ms₂' , uˢ' = SS.Step (Writeᴰ₂ (lookup-∈ˢ l∈ls' _) uᴹ' uˢ')

redex⟼ (proj₁ , proj₂ , (l∈ls , n , V.is#[ .n ]ᴰ , isV) , r₂) (proj₃ , proj₄ , (l∈ls' , n' , V.is#[ .n' ]ᴰ , isV') , () , r₃) Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.Res∙ x , G.Res∙ x₁ ⟩ (L.Kˢ (G.write' l⊑H H⋤A ._ G.∷ x₃) (G.write∙ .l⊑H ._ G.∷ x₂)) (SS.Writeᴰ₂ H∈Ms uᴹ uˢ)

redex⟼ (proj₁ , proj₂ , _ , () , proj₃) v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ t₁≈t₂ S₁≈S₂ SS.Write∙₂
redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.Res x G.#[ n ] , G.Res x₁ G.#[ .n ] ⟩ (L.Kˢ (G.read ._ G.∷ x₅) (G.read ._ G.∷ x₄)) (SS.Read₂ l∈Γ n∈M)
  with member-≈ˢ (yes x) Ms₁≈Ms₂ l∈Γ
... | M₂ , M₁≈M₂ , l∈Ms'  = Step (Read₂ l∈Ms' (member-≈ᴹ M₁≈M₂ n∈M))
redex⟼ {l⊑A = l⊑A} v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.Res∙ x , _ ⟩ (L.Kˢ (x₂ G.∷ x₅) (x₃ G.∷ x₄)) (SS.Read₂ l∈Γ n∈M) = ⊥-elim (x l⊑A)
redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.Res x G.#[ n ]ᴰ , G.Res x₁ G.#[ .n ]ᴰ ⟩ (L.Kˢ (G.read L⊑l G.∷ x₃) (G.read .L⊑l G.∷ x₂)) (SS.Readᴰ₂ L∈Ms n∈M)
  with member-≈ˢ (yes x) Ms₁≈Ms₂ L∈Ms
... | M₂ , M₁≈M₂ , l∈Ms' = Step (Readᴰ₂ l∈Ms' (member-≈ᴹ M₁≈M₂ n∈M))
redex⟼ {l⊑A = l⊑A} v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.Res∙ x , e₂ ⟩ S₁≈S₂ (SS.Readᴰ₂ {L⊑l = L⊑l} L∈Ms n∈M) = ⊥-elim (x (trans-⊑ L⊑l l⊑A))
redex⟼ {l⊑A = l⊑A} v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.deepDup e₁ , G.deepDup e₂ ⟩ S₁≈S₂ (SS.DeepDup₁ ¬var l∈Γ uᴱ)
  with member-≈ᴱ l⊑A Γ₁≈Γ₂ l∈Γ
... | Δ₂ , Δ₁≈Δ₂ , l∈Γ₂ with update-≈ᴱ Γ₁≈Γ₂ uᴱ
... | Γ₂' , uᴱ' = Step (DeepDup₁ (¬var-≈ L.⟨ e₁ , e₂ ⟩ ¬var) l∈Γ₂ uᴱ')
redex⟼ {l⊑A = l⊑A} v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ G.deepDup (G.Var τ∈π) , G.deepDup (G.Var .τ∈π) ⟩ S₁≈S₂ (SS.DeepDup₂ {L⊑l = L⊑l} .τ∈π L∈Γ t∈Δ l∈Γ uᴱ)
  with member-≈ᴱ (trans-⊑ L⊑l l⊑A) Γ₁≈Γ₂ L∈Γ
... | Δ₁ , L.Kᴴ (G.Mapᵀ ._ e₁) (G.Mapᵀ ._ e₂) , L∈Γ₂ with member-≈ᴴ {τ∈π = τ∈π} (L.K-mapᵀ e₁ e₂) t∈Δ
... | t₂ , t₁≈t₂ , t∈Δ₂ᴸ  with member-≈ᴱ l⊑A Γ₁≈Γ₂ l∈Γ
... | Δ₂ ,  Δ₁≈Δ₂ , l∈Γ₂ with update-≈ᴱ Γ₁≈Γ₂ uᴱ
... | Γ₂' , uᴱ' = SS.Step (DeepDup₂ {L⊑l = L⊑l} τ∈π L∈Γ₂ t∈Δ₂ᴸ l∈Γ₂ uᴱ')

redex-≈ : ∀ {l ls τ} {l⊑A : l ⊑ A} {p₁ p₂ : Program l ls τ} {{v₁ : validᴾ p₁}} {{v₂ : validᴾ p₂}} ->
            p₁ ≈ᴾ⟨ (yes l⊑A) ⟩ p₂ -> Redexᴾ p₁  -> Redexᴾ p₂
redex-≈ {l⊑A = l⊑A} {{v₁}} {{v₂}} (L.is≈ᴾ Ms₁≈Ms₂ Γ₁≈Γ₂ (L.Kᵀˢ G.⟨ eᵀ , eˢ ⟩ G.⟨ eᵀ₁ , eˢ₁ ⟩)) (Step step)
  = redex⟼ {l⊑A = l⊑A} v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ L.⟨ eᵀ , eᵀ₁ ⟩ (L.Kˢ eˢ eˢ₁) step
redex-≈ (L.is≈ᴾ Ms₁≈Ms₂ Γ₁≈Γ₂ (L.Kᵀˢ G.∙ᴸ G.∙ᴸ)) (SS.Step x) = SS.Step SS.Hole

--------------------------------------------------------------------------------

¬fork-≈ : ∀ {π τ} {t₁ t₂ : Term π τ} -> t₁ ≈ᵀ t₂ -> ¬ (IsFork t₁) -> ¬ (IsFork t₂)
¬fork-≈ t₁≈t₂ = contrapositive (fork-≈ (sym-≈ᵀ t₁≈t₂))

¬IsForkTS-≈ : ∀ {τ l} {Ts₁ Ts₂ : TS∙ l τ} {l⊑A : l ⊑ A} -> Ts₁ ≈ᵀˢ⟨ yes l⊑A ⟩ Ts₂ -> ¬ (IsForkTS Ts₁) -> ¬ (IsForkTS Ts₂)
¬IsForkTS-≈ Ts₁≈Ts₂ = contrapositive (forkTS-≈ (sym-≈ᵀˢ Ts₁≈Ts₂))

¬done-≈ : ∀ {l τ} {l⊑A : l ⊑ A} {Ts₁ Ts₂ : TS∙ l τ} -> Ts₁ ≈ᵀˢ⟨ yes l⊑A ⟩ Ts₂ -> ¬ (IsDoneTS Ts₁) -> ¬ (IsDoneTS Ts₂)
¬done-≈ Ts₁≈Ts₂  = contrapositive (done-≈ (sym-≈ᵀˢ Ts₁≈Ts₂))

¬redex-≈ : ∀ {l ls τ} {l⊑A : l ⊑ A} {p₁ p₂ : Program l ls τ} {{v₁ : validᴾ p₁}} {{v₂ : validᴾ p₂}} ->
             p₁ ≈ᴾ⟨ (yes l⊑A) ⟩ p₂ -> ¬ (Redexᴾ p₁)  -> ¬ (Redexᴾ p₂)
¬redex-≈ p₁≈p₂ = contrapositive (redex-≈ (sym-≈ᴾ p₁≈p₂))

-- we get low-equivalence using pini
-- postulate redex-≈ : ∀ {l ls τ} {p₁ p₁' p₂ : Program l ls τ} -> (l⊑A : l ⊑ A) -> p₁ ≈ᴾ⟨ (yes l⊑A) ⟩ p₂ -> p₁ ⟼ p₁' ->
--             ∃ (λ p₂' -> (p₁' ≈ᴾ⟨ yes l⊑A ⟩ p₂') × (p₂ ⟼ p₂'))

open _≈ᴾ⟨_⟩_

stuck-≈ : ∀ {l ls τ} {p₁ p₂ : Program l ls τ} {l⊑A : l ⊑ A} {{v₁ : validᴾ p₁}} {{v₂ : validᴾ p₂}} ->
            p₁ ≈ᴾ⟨ (yes l⊑A) ⟩ p₂ -> Stuckᴾ p₁ -> Stuckᴾ p₂
stuck-≈ {p₁ = SC.mkᴾ Ms₁ Γ₁ Ts₁} {SC.mkᴾ Ms₂ Γ₂ Ts₂} p₁≈p₂ (¬done , ¬redex , ¬fork)
  = ¬done-≈ (Ts₁≈Ts₂ p₁≈p₂) ¬done , ¬redex-≈ p₁≈p₂ ¬redex  , ¬IsForkTS-≈ (Ts₁≈Ts₂ p₁≈p₂) ¬fork
