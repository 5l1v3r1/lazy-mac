import Lattice as L
import Scheduler as S₁

module Concurrent.Valid (𝓛 : L.Lattice) (𝓢 : S₁.Scheduler 𝓛) where

import Types as T
open T 𝓛

open S₁.Scheduler 𝓛 𝓢 renaming (State to Stateˢ)
open import Scheduler.Base 𝓛 renaming (⟪_,_,_⟫ to mkᴹ)

import Sequential.Calculus as S
open S 𝓛

import Sequential.Valid as V hiding (validᴾ ; validˢ )
open V 𝓛

import  Concurrent.Calculus as C renaming (⟨_,_,_,_⟩ to mkᴳ) hiding (updateᴾ)
open C 𝓛 𝓢

import Concurrent.Semantics as CS
open CS  𝓛 𝓢

open import Data.Product as P
open import Data.Empty
open import Data.Nat

validᴾ : ∀ {l ls} -> Memories ls -> Pool l -> Set
validᴾ Ms C.[] = ⊤
validᴾ Ms (t C.◅ P) = validTS∙ Ms t × validᴾ Ms P
validᴾ Ms C.∙ = ⊥

map-validᴾ : ∀ {ls ls'} -> Memories ls -> Pools ls' -> Set
map-validᴾ Ms C.[] = ⊤
map-validᴾ Ms (T C.◅ Ps) = validᴾ Ms T × map-validᴾ Ms Ps

valid-Idᵀ : ∀ {ls} -> Label -> ℕ -> Pools ls -> Set
valid-Idᵀ {ls} l n Ps = P.Σ (l ∈ ls) (λ l∈ls -> n ≤ lengthᵀ (lookupᴾ l∈ls Ps))

validᴳ : ∀ {ls} -> Global ls -> Set
validᴳ (mkᴳ Σ Ms Γ Ps) = map-validᴹ Ms × map-validᴴ Ms Γ × map-validᴾ Ms Ps

memberᴾ : ∀ {l ls n} {Ms : Memories ls} {t : Thread l} {P : Pool l} -> validᴾ Ms P -> n ↦ t ∈ᵀ P -> validTS∙ Ms t
memberᴾ v C.here = proj₁ v
memberᴾ v (C.there x) = memberᴾ (proj₂ v) x

memberᴾˢ : ∀ {l ls₁ ls₂} {Ms : Memories ls₁} {Ps : Pools ls₂} {P : Pool l} -> map-validᴾ Ms Ps -> l ↦ P ∈ᴾ Ps -> validᴾ Ms P
memberᴾˢ (proj₁ , proj₂) C.here = proj₁
memberᴾˢ v (C.there l∈Ps) = memberᴾˢ (proj₂ v) l∈Ps

updateᴾ : ∀ {l n ls } {Ms : Memories ls} {P₁ P₂ : Pool l} {t : Thread l}
           -> validᴾ Ms P₁ -> validTS∙ Ms t -> P₂ ≔ P₁ [ n ↦ t ]ᵀ -> validᴾ Ms P₂
updateᴾ v₁ v₂ C.here = v₂ , proj₂ v₁
updateᴾ (v₁ , v₂) v₃ (C.there u) = v₁ , updateᴾ v₂ v₃ u

updateᴾˢ : ∀ {l ls₁ ls₂} {Ms : Memories ls₁} {Ps₁ Ps₂ : Pools ls₂} {P : Pool l}
           -> map-validᴾ Ms Ps₁ -> validᴾ Ms P -> Ps₂ ≔ Ps₁ [ l ↦ P ]ᴾ -> map-validᴾ Ms Ps₂
updateᴾˢ v₁ v₂ C.here = v₂ , proj₂ v₁
updateᴾˢ (proj₁ , proj₂) v₂ (C.there u₁) = proj₁ , updateᴾˢ proj₂ v₂ u₁

valid-▻ : ∀ {l ls} {Ms : Memories ls} {P : Pool l} {t : Thread l} -> validᴾ Ms P -> validTS∙ Ms t -> validᴾ Ms (P ▻ t)
valid-▻ {P = C.[]} v₁ v₂ = v₂ , T.tt
valid-▻ {P = t C.◅ P} (v₁ , v₂) v₃ = v₁ , (valid-▻ v₂ v₃)
valid-▻ {P = C.∙} () v₂

wkenᴾ : ∀ {l ls₁ ls₂} {P : Pool l} {Ms₁ : Memories ls₁}{Ms₂ : Memories ls₂} -> Ms₁ ⊆ˢ Ms₂ -> validᴾ Ms₁ P -> validᴾ Ms₂ P
wkenᴾ {P = C.[]} x v = T.tt
wkenᴾ {P = t C.◅ P} x (proj₁ , proj₂) = (wkenTS∙ x proj₁) , (wkenᴾ x proj₂)
wkenᴾ {P = C.∙} x ()

wkenᴾˢ : ∀ {ls ls₁ ls₂} {Ps : Pools ls} {Ms₁ : Memories ls₁}{Ms₂ : Memories ls₂} -> Ms₁ ⊆ˢ Ms₂ -> map-validᴾ Ms₁ Ps -> map-validᴾ Ms₂ Ps
wkenᴾˢ {Ps = C.[]} x v = T.tt
wkenᴾˢ {Ps = T C.◅ Ps} x (proj₁ , proj₂) = (wkenᴾ x proj₁) , (wkenᴾˢ x proj₂)

valid↪ : ∀ {n l ls} {g₁ g₂ : Global ls} -> (l , n) ⊢ g₁ ↪ g₂ -> validᴳ g₁ -> validᴳ g₂
valid↪ (CS.step-∅ l∈P t∈T ¬fork step sch uᵀ uᴾ) (MSⱽ , Γⱽ , Psᵛ) with memberᴾˢ Psᵛ l∈P
... | P₁ⱽ with memberᴾ P₁ⱽ t∈T
... | tⱽ with valid⟼ (MSⱽ , Γⱽ , tⱽ) step | ⟼-⊆ˢ step
... | Msⱽ' , Γⱽ' , tⱽ' | Ms₁⊆Ms₂ = Msⱽ' , (Γⱽ' , updateᴾˢ (wkenᴾˢ Ms₁⊆Ms₂ Psᵛ) (updateᴾ (wkenᴾ Ms₁⊆Ms₂  P₁ⱽ) tⱽ' uᵀ) uᴾ)
valid↪ (CS.fork {tᴴ = tᴴ} l∈P t∈T uᵀ u₁ᴾ H∈P₂ sch u₂ᴾ) (MSⱽ , Γⱽ , Psᵛ) with memberᴾˢ Psᵛ l∈P
... | P₁ⱽ with memberᴾ P₁ⱽ t∈T
... | (h∈ls , tᴴⱽ) , Sⱽ  with updateᴾˢ Psᵛ (updateᴾ P₁ⱽ (T.tt , Sⱽ) uᵀ) u₁ᴾ
... | Psᵛ' = MSⱽ , Γⱽ , updateᴾˢ Psᵛ' (valid-▻ (memberᴾˢ Psᵛ' H∈P₂) (valid-deepDupᵀ {{ tᴴ }}  tᴴⱽ , tt)) u₂ᴾ
valid↪ (CS.fork∙ l∈P t∈T uᵀ uᴾ sch) (MSⱽ , Γⱽ , Psᵛ) with memberᴾ (memberᴾˢ Psᵛ l∈P) t∈T
valid↪ (CS.fork∙ l∈P t∈T uᵀ uᴾ sch) (MSⱽ , Γⱽ , Psᵛ) | () , proj₂
valid↪ (CS.skip l∈P t∈T stuck sch) (MSⱽ , Γⱽ , Psᵛ) = MSⱽ , Γⱽ , Psᵛ
valid↪ (CS.done l∈P t∈T don sch) (MSⱽ , Γⱽ , Psᵛ) = MSⱽ , Γⱽ , Psᵛ
