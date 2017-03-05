import Lattice as L

module Sequential.Security.Lemmas (𝓛 : L.Lattice) (A : L.Label 𝓛) where

import Types as T
open T 𝓛

import Sequential.Calculus as S renaming (⟨_,_,_⟩ to ⟨_∥_∥_⟩)
open S 𝓛
open import Sequential.Security.Erasure 𝓛 A as SE hiding (memberᴴ ; updateᴴ ; memberᴱ ; updateᴱ ; updateᴹ ; memberᴹ)

open import Relation.Nullary

import Sequential.Semantics as S₁
open S₁ 𝓛

open import Data.Nat as N

import Sequential.Security.Graph as G renaming (⟨_,_,_⟩ to mkᴱ)
open G 𝓛 A

open import Data.Empty
open import Data.Maybe

open import Data.Product
import Data.Product as P
open import Function

import Sequential.Valid as V hiding (memberᴴ ; updateᴴ ; memberᴱ ; updateᴱ ; memberˢ ; updateˢ)
open V 𝓛

memberᴴ : ∀ {l π π' τ} {Δ Δ' : Heap l π} {t' : Term π' τ} -> (τ∈π : τ ∈⟨ l ⟩ᴿ π) ->  EraseMapᵀ Δ Δ' -> τ∈π ↦ t' ∈ᴴ Δ' -> ∃ (λ t -> Eraseᵀ t t' × τ∈π ↦ t ∈ᴴ Δ)
memberᴴ ⟪ τ∈π ⟫ = aux ⟪ ∈ᴿ-∈ τ∈π ⟫
  where aux : ∀ {l π π' τ} {Δ Δ' : Heap l π} {t' : Term π' τ} -> (τ∈π : τ ∈⟨ l ⟩ π) ->  EraseMapᵀ Δ Δ' -> Memberᴴ (just t') τ∈π Δ' ->
                ∃ (λ t -> Eraseᵀ t t' × Memberᴴ (just t) τ∈π  Δ)
        aux T.⟪ T.here ⟫ (just x ∷ eᴱ) S.here = _ , (x , here)
        aux T.⟪ T.there τ∈π₁ ⟫ (x ∷ eᴱ) (S.there t∈Δ') = P.map id (P.map id there) (aux ⟪ τ∈π₁ ⟫ eᴱ t∈Δ')
        aux T.⟪ T.there τ∈π₁ ⟫ ∙ ()

-- TODO rename to updateᴴ ?
updateᴴ : ∀ {l π π' τ} {Δ₁ Δ₁' Δ₂' : Heap l π} {mt mt' : Maybe (Term π' τ)} -> (τ∈π : τ ∈⟨ l ⟩ π)
          -> Eraseᴹᵀ mt mt' -> EraseMapᵀ Δ₁ Δ₁' -> Updateᴴ mt' τ∈π Δ₁' Δ₂' -> ∃ (λ Δ₂ → EraseMapᵀ Δ₂ Δ₂' × Updateᴴ mt τ∈π Δ₁ Δ₂)
updateᴴ .(T.⟪ T.here ⟫) eᴹ (x G.∷ eᴱ) S.here = _ , ((eᴹ G.∷ eᴱ) , here)
updateᴴ ._ eᴹ (eˣ ∷ eᴱ) (S.there u) = P.map (_∷_ _) (P.map (_∷_ eˣ) there) (updateᴴ _ eᴹ eᴱ u)

open import Relation.Binary.PropositionalEquality hiding (subst)

data Redexᴱ {l τ} (x : Dec (l ⊑ A)) (p p'ᴱ : State l τ) : Set where
  Step : ∀ {p'} -> p ⇝ p' -> Erase x p' p'ᴱ -> Redexᴱ x p p'ᴱ

sim⇝ : ∀ {l ls π₁ π₂ τ τ₁ τ₂} {Δ₁ Δ₁' : Heap l π₁} {Δ₂'  : Heap l π₂}
         {t₁ t₁' : Term π₁ τ₁} {t₂' : Term π₂ τ₂} {S₁ S₁' : Stack l _ _ τ} {S₂' : Stack l _ _ τ} {Ms : Memories ls} ->
         {{isV : valid-state Ms ⟨ Δ₁ ∥ t₁ ∥ S₁ ⟩}} -> (l⊑A : l ⊑ A) -> EraseMapᵀ Δ₁ Δ₁' -> Eraseᵀ t₁ t₁' -> Eraseˢ S₁ S₁' ->
          ⟨ Δ₁' ∥ t₁' ∥ S₁' ⟩ ⇝ ⟨ Δ₂' ∥ t₂' ∥ S₂' ⟩ -> Redexᴱ (yes l⊑A) ⟨ Δ₁ ∥ t₁ ∥ S₁ ⟩ ⟨ Δ₂' ∥ t₂' ∥ S₂' ⟩
sim⇝ l⊑A eᴱ (G.App eᵀ eᵀ₁) eˢ (S₁.App₁ {τ₁ = τ₁} {π = π})
  = Step App₁ (mkᴱ ((just eᵀ₁) ∷ eᴱ) (wkenᴱ eᵀ (drop refl-⊆)) (((Var _) ∷ wkenᴱˢ _ eˢ)))
sim⇝ l⊑A eᴱ (G.Abs eᵀ) (G.Var α∈π G.∷ eˢ) (S₁.App₂ .α∈π) = Step (S₁.App₂ α∈π) (mkᴱ eᴱ (substᴱ (lift-εᵀ (Var α∈π)) eᵀ)  eˢ)
sim⇝ l⊑A eᴱ (G.Var ⟪ τ∈π ⟫) eˢ (S₁.Var₁ ⟪ .τ∈π ⟫ t∈Δ' ¬val' rᴱ') with memberᴴ ⟪ τ∈π ⟫ eᴱ t∈Δ'
... | t , eᵀ , t∈Δ with updateᴴ ⟪ ∈-∈ᴿ τ∈π ⟫ nothing eᴱ rᴱ'
... | Γ₂ , e₂ᴱ , rᴱ = Step (Var₁ ⟪ τ∈π ⟫ t∈Δ (¬val⁻ᴱ eᵀ ¬val') rᴱ) (mkᴱ e₂ᴱ eᵀ ((G.# T.⟪ τ∈π ⟫) G.∷ eˢ))
sim⇝ l⊑A eᴱ (G.Var τ∈π) eˢ (S₁.Var₁' .τ∈π v∈Δ' val') with memberᴴ τ∈π eᴱ v∈Δ'
... | v , eᵀ , v∈Δ = Step (Var₁' τ∈π v∈Δ (val⁻ᴱ eᵀ val' )) (mkᴱ eᴱ eᵀ eˢ )
sim⇝ l⊑A eᴱ eᵀ (G.# ⟪ τ∈π ⟫ G.∷ eˢ) (S₁.Var₂ ⟪ .τ∈π ⟫ val' u'ᴱ) with updateᴴ ⟪ ∈-∈ᴿ τ∈π ⟫ (just eᵀ) eᴱ u'ᴱ
... | Δ₂ , e₂ᴱ , uᴱ = Step (Var₂ ⟪ τ∈π ⟫ (val⁻ᴱ eᵀ val') uᴱ) (mkᴱ e₂ᴱ eᵀ eˢ )
sim⇝ l⊑A eᴱ (G.If eᵀ Then eᵀ₁ Else eᵀ₂) eˢ S₁.If = Step S₁.If (mkᴱ eᴱ eᵀ  ((G.Then eᵀ₁ Else eᵀ₂) G.∷ eˢ ))
sim⇝ l⊑A eᴱ G.True ((G.Then x Else x₁) G.∷ eˢ) S₁.IfTrue = Step S₁.IfTrue (mkᴱ eᴱ x eˢ)
sim⇝ l⊑A eᴱ G.False ((G.Then x Else x₁) G.∷ eˢ) S₁.IfFalse = Step S₁.IfFalse (mkᴱ eᴱ x eˢ )
sim⇝ l⊑A eᴱ (G.Return eᵀ) eˢ S₁.Return = Step S₁.Return (mkᴱ eᴱ (G.Mac eᵀ) eˢ )
sim⇝ l⊑A eᴱ (eᵀ G.>>= eᵀ₁) eˢ S₁.Bind₁ = Step S₁.Bind₁ (mkᴱ eᴱ eᵀ (G.Bind eᵀ₁ G.∷ eˢ ))
sim⇝ l⊑A eᴱ (G.Mac eᵀ) (G.Bind x G.∷ eˢ) S₁.Bind₂ = Step S₁.Bind₂ (mkᴱ eᴱ (G.App x eᵀ) eˢ )
sim⇝ l⊑A eᴱ (G.label h⊑A eᵀ) eˢ (S₁.Label' p) = Step (S₁.Label' p) (mkᴱ eᴱ (G.Return (G.Res h⊑A (G.Id eᵀ))) eˢ )
sim⇝ l⊑A eᴱ (G.label' h⋤A eᵀ) eˢ (S₁.Label'∙ p) = Step (Label' p) (mkᴱ eᴱ (G.Return (Res∙ h⋤A)) eˢ )
sim⇝ {{isV = proj₁ , () , proj₂}} l⊑A eᴱ (G.label∙ eᵀ) eˢ (S₁.Label'∙ p)
sim⇝ l⊑A eᴱ (G.unlabel p eᵀ) eˢ (S₁.Unlabel₁ .p) = Step (S₁.Unlabel₁ p) (mkᴱ eᴱ eᵀ (G.unlabel p G.∷ eˢ ))
sim⇝ l⊑A eᴱ (G.Res x eᵀ) (G.unlabel p G.∷ eˢ) (S₁.Unlabel₂ .p) = Step (S₁.Unlabel₂ p) (mkᴱ eᴱ (G.Return (G.unId eᵀ)) eˢ )
sim⇝ l⊑A eᴱ (G.Res∙ x) (G.unlabel p G.∷ eˢ) (S₁.Unlabel₂ .p) = ⊥-elim (x (trans-⊑ p l⊑A))
sim⇝ l⊑A eᴱ (G.unId eᵀ) eˢ S₁.UnId₁ = Step S₁.UnId₁ (mkᴱ eᴱ eᵀ (G.unId G.∷ eˢ ))
sim⇝ l⊑A eᴱ (G.Id eᵀ) (G.unId G.∷ eˢ) S₁.UnId₂ = Step S₁.UnId₂ (mkᴱ eᴱ eᵀ eˢ )
sim⇝ l⊑A G.∙ G.∙ G.∙ S₁.Hole₂ = Step S₁.Hole₂ (mkᴱ G.∙ G.∙ G.∙ )
sim⇝ l⊑A eᴱ (G.new l⊑h h⊑A eᵀ) eˢ (S₁.New₁ ¬var) = Step (New₁ (¬var⁻ᴱ eᵀ ¬var)) (mkᴱ (G.just eᵀ G.∷ eᴱ) (G.new l⊑h h⊑A (G.Var T.⟪ _ ⟫)) (wkenᴱˢ _ eˢ ))
sim⇝ l⊑A eᴱ (G.new' l⊑h h⋤A eᵀ) eˢ (S₁.New∙₁ ¬var) = Step (New₁ (¬var⁻ᴱ eᵀ ¬var)) (mkᴱ (G.just eᵀ G.∷ eᴱ) (G.new' l⊑h h⋤A (G.Var T.⟪ _ ⟫)) (wkenᴱˢ _ eˢ ))
sim⇝ l⊑A eᴱ (G.new∙ l⊑h eᵀ) eˢ (S₁.New∙₁ ¬var) = Step (New∙₁ (¬var⁻ᴱ eᵀ ¬var)) (mkᴱ (G.just eᵀ G.∷ eᴱ) (G.new∙ l⊑h (G.Var T.⟪ _ ⟫)) (wkenᴱˢ _ eˢ ))
sim⇝ l⊑A eᴱ (G.write l⊑H h⊑A eᵀ eᵀ₁) eˢ S₁.Write₁ = Step Write₁ (mkᴱ (G.just eᵀ₁ G.∷ eᴱ) (wkenᴱ eᵀ (drop refl-⊆)) (write l⊑H h⊑A ⟪ _ ⟫ ∷ wkenᴱˢ _ eˢ ))
sim⇝ l⊑A eᴱ (G.write' l⊑H h⋤A eᵀ eᵀ₁) eˢ S₁.Write∙₁ = Step Write₁ (mkᴱ (G.just eᵀ₁ G.∷ eᴱ) (wkenᴱ eᵀ (drop refl-⊆)) ((G.write' l⊑H h⋤A ⟪ _ ⟫) G.∷ wkenᴱˢ _ eˢ) )
sim⇝ l⊑A eᴱ (G.write∙ l⊑H eᵀ eᵀ₁) eˢ S₁.Write∙₁ = Step Write∙₁ (mkᴱ (G.just eᵀ₁ G.∷ eᴱ) (wkenᴱ eᵀ (drop refl-⊆)) ((write∙ l⊑H ⟪ _ ⟫) G.∷ wkenᴱˢ _ eˢ) )
sim⇝ l⊑A eᴱ (G.read L⊑l eᵀ) eˢ S₁.Read₁ = Step S₁.Read₁ (mkᴱ eᴱ eᵀ (G.read L⊑l G.∷ eˢ ))

memberᴱ : ∀ {h π ls} {Δ' : Heap h π} {Γ Γ' : Heaps ls} (h⊑A : h ⊑ A) ->
          EraseMapᴴ Γ Γ' -> h ↦ ⟨ Δ' ⟩ ∈ᴱ Γ' -> Σ (Heap h π) (λ Δ -> Eraseᴴ (yes h⊑A) (⟨ Δ ⟩) (⟨ Δ' ⟩) × h ↦ ⟨ Δ ⟩ ∈ᴱ Γ)
memberᴱ {H} h⊑A (x ∷ e) S.here with H ⊑? A
memberᴱ h⊑A (G.Mapᵀ p x G.∷ e) S.here | yes .p = _ , G.Mapᵀ h⊑A x , here
memberᴱ h⊑A (() ∷ e) S.here | no ¬p
memberᴱ h⊑A (x ∷ e) (S.there x₁) = P.map id (P.map id there) (memberᴱ h⊑A e x₁)

-- TODO Eraseᴴ is redundant
updateᴱ : ∀ {h π ls} {Δ Δ' : Heap h π} {Γ₁ Γ₁' Γ₂' : Heaps ls} (h⊑A : h ⊑ A) ->
          EraseMapᴴ Γ₁ Γ₁' -> Eraseᴴ (yes h⊑A) (⟨ Δ ⟩) (⟨ Δ' ⟩)  -> Γ₂' ≔ Γ₁' [ h ↦ ⟨ Δ' ⟩ ]ᴱ -> ∃ (λ Γ₂ -> Γ₂ ≔ Γ₁ [ h ↦ ⟨ Δ ⟩ ]ᴱ)
updateᴱ h⊑A (x G.∷ e₁) e₂ S.here = _ , here
updateᴱ h⊑A (x G.∷ e₁) e₂ (S.there u₁) = P.map (_∷_ _) there (updateᴱ h⊑A e₁ e₂ u₁)

memberˢ : ∀ {l ls} {M₂ : Memory l} {Ms₁ Ms₂ : Memories ls} -> (l⊑A : l ⊑ A) -> EraseMapᴹ Ms₁ Ms₂ -> l ↦ M₂ ∈ˢ Ms₂ ->
            ∃ (λ M₁ -> Eraseᴹ (yes l⊑A) M₁ M₂ × l ↦ M₁ ∈ˢ Ms₁)
memberˢ {l} l⊑A (x G.∷ e) S.here with l ⊑? A
memberˢ l⊑A (x G.∷ e) S.here | yes p = _ , (ext-εᴹ (yes l⊑A) x , here)
memberˢ l⊑A (x G.∷ e) S.here | no ¬p = ⊥-elim (¬p l⊑A)
memberˢ l⊑A (x G.∷ e) (S.there l∈Ms) = P.map id (P.map id there) (memberˢ l⊑A e l∈Ms)

updateˢ : ∀ {h ls} {M₁ M₁' : Memory h} {Ms₁ Ms₁' Ms₂' : Memories ls} (h⊑A : h ⊑ A) ->
          EraseMapᴹ Ms₁ Ms₁' -> Eraseᴹ (yes h⊑A) M₁ M₁' -> Ms₂' ≔ Ms₁' [ h ↦ M₁' ]ˢ ->  ∃ (λ Ms₂ -> Ms₂ ≔ Ms₁ [ h ↦ M₁ ]ˢ)
updateˢ h⊑A (x G.∷ map-eᴹ) (G.Id .h⊑A) S.here = _ , here
updateˢ h⊑A (x G.∷ map-eᴹ) eᴹ (S.there u₁) = P.map (_∷_ _) there (updateˢ h⊑A map-eᴹ eᴹ u₁)

newᴱᴹ : ∀ {L τ} {L⊑A : L ⊑ A}  {M₁ M₂ : Memory L} -> (c : Cell L τ) ->
         Eraseᴹ (yes L⊑A) M₁ M₂ -> Eraseᴹ (yes L⊑A) (newᴹ c M₁) (newᴹ c M₂)
newᴱᴹ c (G.Id L⊑A) = G.Id L⊑A

-- TODO is this any diffferent than updateˢ ?
writeˢ : ∀ {h ls} {M : Memory h} {Ms₁ Ms₁' Ms₂' : Memories ls} (h⊑A : h ⊑ A) ->
           EraseMapᴹ Ms₁ Ms₁' -> Ms₂' ≔ Ms₁' [ h ↦ M ]ˢ -> ∃ (λ Ms₂ -> Ms₂ ≔ Ms₁ [ h ↦ M ]ˢ)
writeˢ H⊑A (x G.∷ e) S.here = _ , here
writeˢ H⊑A (x G.∷ e) (S.there u₁) = P.map (_∷_ _) there (writeˢ H⊑A e u₁)

updateᴹ : ∀ {l n τ} {M₁' M₂' M₁ : Memory l} {l⊑A : l ⊑ A} -> (c : Cell l τ) -> Eraseᴹ (yes l⊑A) M₁ M₁' ->
          M₂' ≔ M₁' [ n ↦ c ]ᴹ -> ∃ (λ M₂ -> Eraseᴹ (yes l⊑A) M₂ M₂' × M₂ ≔ M₁ [ n ↦ c ]ᴹ)
updateᴹ c (G.Id l⊑A) S.here = c S.∷ _ , G.Id l⊑A , S.here
updateᴹ c (G.Id l⊑A) (S.there u) = P.map (_∷_ _) (P.map consᴱ there) (updateᴹ c (G.Id _) u)
  where consᴱ : ∀ {l τ} {M₁ M₂ : Memory l} {l⊑A : l ⊑ A} {c : Cell l τ} -> Eraseᴹ (yes l⊑A) M₁ M₂ -> Eraseᴹ (yes l⊑A) (c ∷ M₁) (c ∷ M₂)
        consᴱ (G.Id l⊑A₁) = G.Id l⊑A₁


memberᴹ : ∀ {l n τ} {M₁' M₁ : Memory l} {l⊑A : l ⊑ A} {c : Cell l τ} -> Eraseᴹ (yes l⊑A) M₁ M₁' ->
          n ↦ c ∈ᴹ M₁' -> n ↦ c ∈ᴹ M₁
memberᴹ (G.Id l⊑A) u = u


newˢ : ∀ {l ls τ} {M : Memory l} {Ms : Memories ls} -> (c : Cell l τ) ->
       l ↦ M ∈ˢ Ms -> ∃ (λ Ms' -> Ms' ≔ Ms [ l ↦ newᴹ c M ]ˢ)
newˢ c S.here = _ , here
newˢ c (S.there u₁) = P.map (_∷_ _) there (newˢ c u₁)

mk-∈ˢ : ∀ {l ls} -> (l∈ls : l ∈ ls) -> {Ms : Memories ls} -> map-validᴹ Ms ->
             let M = lookupˢ l∈ls Ms in  l ↦ M ∈ˢ Ms × validᴹ M
mk-∈ˢ T.here {M S.∷ Ms} (proj₁ , proj₂) = here , proj₁
mk-∈ˢ (T.there l∈ls) {M S.∷ Ms} (proj₁ , proj₂) = P.map there id (mk-∈ˢ l∈ls {Ms} proj₂)

sim⟼ : ∀ {L ls τ} {p₁ p₁' p₂' : Program L ls τ} (L⊑A : L ⊑ A) (p₁ⱽ : validᴾ p₁) -> Eraseᴾ (yes L⊑A) p₁ p₁' -> p₁' ⟼ p₂' -> Redexᴾ p₁
sim⟼ L⊑A (vᴹˢ , vᴴˢ , (vᵀ , vˢ)) (G.mkᴱ eᴹˢ eᴴˢ G.⟨ eᵀ , eˢ ⟩) (S₁.Pure l∈Γ' step' uᴱ') with memberᴱ L⊑A eᴴˢ l∈Γ'
... | _ , (Mapᵀ _ eᴴ) , l∈Γ with sim⇝ {{ valid-∈ᴱ vᴴˢ l∈Γ , (vᵀ , vˢ) }} L⊑A eᴴ eᵀ eˢ step'
... | Step step (G.mkᴱ eᴴ' eᵗ' eˢ' ) with updateᴱ L⊑A eᴴˢ (Mapᵀ _ eᴴ') uᴱ'
... | _ , uˢ = S₁.Step (Pure l∈Γ step uˢ)
sim⟼ L⊑A v₁ (G.mkᴱ eᴹˢ eᴴˢ G.⟨ G.new l⊑H h⊑A (G.Var τ∈π) , eˢ ⟩) (S₁.New H∈Ms' uˢ') with memberˢ h⊑A eᴹˢ H∈Ms'
... | M , eᴹ , H∈Ms with updateˢ h⊑A eᴹˢ (newᴱᴹ ∥ l⊑H , τ∈π ∥ eᴹ) uˢ'
... | Ms , uˢ = S₁.Step (New H∈Ms uˢ)
sim⟼ L⊑A (proj₁ , proj₂ , (h∈ls , _) , proj₅) (G.mkᴱ eᴹˢ eᴴˢ G.⟨ G.new' l⊑H h⋤A (G.Var τ∈π) , eˢ ⟩) S₁.New∙
  with mk-∈ˢ h∈ls proj₁
... | h∈Γ , vᴹ  with newˢ S.∥ l⊑H , τ∈π ∥ h∈Γ
... | Ms' , uˢ = Step (New h∈Γ uˢ)
sim⟼ L⊑A (proj₁ , proj₂ , () , proj₃) (G.mkᴱ eᴹˢ eᴴˢ G.⟨ G.new∙ l⊑H eᵀ , eˢ ⟩) S₁.New∙
sim⟼ L⊑A v₁ (G.mkᴱ eᴹˢ eᴴˢ G.⟨ G.Res x #[ n ] , G.write l⊑H H⊑A τ∈π G.∷ eˢ ⟩) (S₁.Write₂ H∈Ms' uᴹ' uˢ') with memberˢ H⊑A eᴹˢ H∈Ms'
... | M , eᴹ , H∈Ms with updateᴹ S.∥ l⊑H , τ∈π ∥ eᴹ uᴹ'
... | _ , eᴹ' , uᴹ  with updateˢ H⊑A eᴹˢ eᴹ' uˢ'
... | MS , uˢ = S₁.Step (Write₂ H∈Ms uᴹ uˢ)
sim⟼ L⊑A v₁ (G.mkᴱ eᴹˢ eᴴˢ G.⟨ G.Res x #[ n ]ᴰ , G.write l⊑H H⊑A τ∈π G.∷ eˢ ⟩) (S₁.Writeᴰ₂ H∈Ms' uᴹ' uˢ') with memberˢ H⊑A eᴹˢ H∈Ms'
... | M , eᴹ , H∈Ms with updateᴹ S.∥ l⊑H , τ∈π ∥ eᴹ uᴹ'
... | _ , eᴹ' , uᴹ  with updateˢ H⊑A eᴹˢ eᴹ' uˢ'
... | MS , uˢ = S₁.Step (Writeᴰ₂ H∈Ms uᴹ uˢ)
sim⟼ L⊑A (proj₁ , proj₂ , (l∈ls , n , V.is#[ .n ] , validAddr) , proj₇) (G.mkᴱ eᴹˢ eᴴˢ G.⟨ G.Res x eᵀ , G.write' l⊑H H⋤A τ∈π G.∷ eˢ ⟩) S₁.Write∙₂
  with mk-∈ˢ l∈ls proj₁
... | H∈Ms , vᴹ with updateᴹ-valid S.∥ l⊑H , τ∈π ∥ validAddr
... | _ , uᴹ with updataˢ-valid l∈ls
... | _ , uˢ = Step (Write₂ H∈Ms uᴹ uˢ)
sim⟼ L⊑A (proj₁ , proj₂ , (l∈ls , n , V.is#[ .n ]ᴰ , validAddr) , proj₇) (G.mkᴱ eᴹˢ eᴴˢ G.⟨ G.Res x eᵀ , G.write' l⊑H H⋤A τ∈π G.∷ eˢ ⟩) S₁.Write∙₂
  with mk-∈ˢ l∈ls proj₁
... | H∈Ms , vᴹ with updateᴹ-valid S.∥ l⊑H , τ∈π ∥ validAddr
... | _ , uᴹ with updataˢ-valid l∈ls
... | _ , uˢ = Step (Writeᴰ₂ H∈Ms uᴹ uˢ)
sim⟼ L⊑A (proj₁ , proj₂ , proj₃ , () , proj₄) (G.mkᴱ eᴹˢ eᴴˢ G.⟨ G.Res x eᵀ , G.write∙ l⊑H ._ G.∷ eˢ ⟩) S₁.Write∙₂
sim⟼ L⊑A (proj₁ , proj₂ , (l∈ls , n , V.is#[ .n ] , validAddr) , proj₇) (G.mkᴱ eᴹˢ eᴴˢ G.⟨ G.Res∙ x , G.write' l⊑H H⋤A τ∈π G.∷ eˢ ⟩) S₁.Write∙₂
  with mk-∈ˢ l∈ls proj₁
... | H∈Ms , vᴹ with updateᴹ-valid S.∥ l⊑H , τ∈π ∥ validAddr
... | _ , uᴹ with updataˢ-valid l∈ls
... | _ , uˢ = Step (Write₂ H∈Ms uᴹ uˢ)
sim⟼ L⊑A (proj₁ , proj₂ , (l∈ls , n , V.is#[ .n ]ᴰ , validAddr) , proj₇) (G.mkᴱ eᴹˢ eᴴˢ G.⟨ G.Res∙ x , G.write' l⊑H H⋤A τ∈π G.∷ eˢ ⟩) S₁.Write∙₂
  with mk-∈ˢ l∈ls proj₁
... | H∈Ms , vᴹ with updateᴹ-valid S.∥ l⊑H , τ∈π ∥ validAddr
... | _ , uᴹ with updataˢ-valid l∈ls
... | _ , uˢ = Step (Writeᴰ₂ H∈Ms uᴹ uˢ)
sim⟼ L⊑A (proj₁ , proj₂ , proj₃ , () , proj₄) (G.mkᴱ eᴹˢ eᴴˢ G.⟨ G.Res∙ x , G.write∙ l⊑H τ∈π G.∷ eˢ ⟩) S₁.Write∙₂
sim⟼ L⊑A v₁ (G.mkᴱ eᴹˢ eᴴˢ G.⟨ G.Res x G.#[ n ] , G.read ._ G.∷ eˢ ⟩) (S₁.Read₂ l∈Γ' n∈M') with memberˢ x eᴹˢ l∈Γ'
... | M , eᴹ , H∈Ms = Step (Read₂ H∈Ms (memberᴹ eᴹ n∈M'))
sim⟼ L⊑A v₁ (G.mkᴱ eᴹˢ eᴴˢ G.⟨ G.Res x G.#[ n ]ᴰ , G.read ._ G.∷ eˢ ⟩) (S₁.Readᴰ₂ l∈Γ' n∈M') with memberˢ x eᴹˢ l∈Γ'
... | M , eᴹ , H∈Ms = S₁.Step (Readᴰ₂ H∈Ms (memberᴹ eᴹ n∈M'))
sim⟼ L⊑A v₁ (G.mkᴱ eᴹˢ eᴴˢ G.⟨ G.deepDup eᵀ , eˢ ⟩) (S₁.DeepDup₁ ¬var l∈Γ' uᴱ') with memberᴱ L⊑A eᴴˢ l∈Γ'
... | _ , (Mapᵀ _ eᴴ) , l∈Γ with updateᴱ L⊑A eᴴˢ (G.Mapᵀ L⊑A ((just eᵀ) G.∷ eᴴ)) uᴱ'
... | _ , uᴱ = S₁.Step (DeepDup₁ (¬var⁻ᴱ eᵀ ¬var) l∈Γ uᴱ)
sim⟼ L⊑A v₁ (G.mkᴱ eᴹˢ eᴴˢ G.⟨ G.deepDup (G.Var τ∈π) , eˢ ⟩) (S₁.DeepDup₂ {L⊑l = l⊑L} .τ∈π L∈Γ' t∈Δ' l∈Γ' uᴱ') with memberᴱ (trans-⊑ l⊑L L⊑A) eᴴˢ L∈Γ'
... | _ , (Mapᵀ _ eᴴ) , L∈Γ with memberᴴ τ∈π eᴴ t∈Δ'
... | _ , eᵀ , t∈Δ with memberᴱ L⊑A eᴴˢ l∈Γ'
... | _ , (Mapᵀ _ eᴴˡ) , l∈Γ with updateᴱ L⊑A eᴴˢ (G.Mapᵀ L⊑A ((just (deepDupᵀᴱ eᵀ)) G.∷ eᴴˡ)) uᴱ'
... | _ , uᴱ = Step (DeepDup₂ {L⊑l = l⊑L} τ∈π L∈Γ t∈Δ l∈Γ uᴱ)
sim⟼ L⊑A v₁ (G.mkᴱ eᴹˢ eᴴˢ G.∙ᴸ) S₁.Hole = S₁.Step S₁.Hole

open import Sequential.Security.Simulation 𝓛 A

redex⁻ᴱ : ∀ {l ls τ} {p p' : Program l ls τ} {{pⱽ : validᴾ p}} {l⊑A : l ⊑ A}  -> Eraseᴾ (yes l⊑A) p p' -> Redexᴾ p' -> Redexᴾ p
redex⁻ᴱ {{pⱽ}} {l⊑A} e (S₁.Step step) = sim⟼ l⊑A pⱽ e step

redexᴱ : ∀ {l ls τ} {p p' : Program l ls τ} {l⊑A : l ⊑ A} -> Eraseᴾ (yes l⊑A) p p' -> Redexᴾ p -> Redexᴾ p'
redexᴱ {l⊑A = l⊑A} e (S₁.Step step) rewrite unlift-εᴾ e = Step (ε₁ᴾ-sim (yes l⊑A) step)

¬redexᴱ : ∀ {l ls τ} {p p' : Program l ls τ} {l⊑A : l ⊑ A} {{pⱽ : validᴾ p}} -> Eraseᴾ (yes l⊑A) p p' -> ¬ (Redexᴾ p) -> ¬ (Redexᴾ p')
¬redexᴱ {{pⱽ}} e = contrapositive (redex⁻ᴱ e)
