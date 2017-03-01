import Lattice as L

module Sequential.Lemmas (𝓛 : L.Lattice) (A : L.Label 𝓛) where

import Types as T
open T 𝓛

import Sequential.Calculus as S
open S 𝓛
open import Sequential.Erasure 𝓛 A as SE hiding (memberᴴ ; updateᴴ ; memberᴱ ; updateᴱ)

open import Relation.Nullary

import Sequential.Semantics as S₁
open S₁ 𝓛

import Sequential.Graph as G
open G 𝓛 A

open import Data.Empty
open import Data.Maybe

open import Data.Product using (∃ ; Σ ; _×_ ; proj₁ ; proj₂)
import Data.Product as P
open import Function

-- TODO rename to updateᴱ ?
memberᴱ : ∀ {l π π' τ} {Δ Δ' : Heap l π} {t' : Term π' τ} -> (τ∈π : τ ∈⟨ l ⟩ᴿ π) ->  EraseMapᵀ Δ Δ' -> τ∈π ↦ t' ∈ᴴ Δ' -> ∃ (λ t -> Eraseᵀ t t' × τ∈π ↦ t ∈ᴴ Δ)
memberᴱ ⟪ τ∈π ⟫ = aux ⟪ ∈ᴿ-∈ τ∈π ⟫
  where aux : ∀ {l π π' τ} {Δ Δ' : Heap l π} {t' : Term π' τ} -> (τ∈π : τ ∈⟨ l ⟩ π) ->  EraseMapᵀ Δ Δ' -> Memberᴴ (just t') τ∈π Δ' ->
                ∃ (λ t -> Eraseᵀ t t' × Memberᴴ (just t) τ∈π  Δ)
        aux T.⟪ T.here ⟫ (just x ∷ eᴱ) S.here = _ P., (x P., here)
        aux T.⟪ T.there τ∈π₁ ⟫ (x ∷ eᴱ) (S.there t∈Δ') = P.map id (P.map id there) (aux ⟪ τ∈π₁ ⟫ eᴱ t∈Δ')
        aux T.⟪ T.there τ∈π₁ ⟫ ∙ ()

-- TODO rename to updateᴴ ?
updateᴱ : ∀ {l π π' τ} {Δ₁ Δ₁' Δ₂' : Heap l π} {mt mt' : Maybe (Term π' τ)} -> (τ∈π : τ ∈⟨ l ⟩ π)
          -> Eraseᴹᵀ mt mt' -> EraseMapᵀ Δ₁ Δ₁' -> Updateᴴ mt' τ∈π Δ₁' Δ₂' -> ∃ (λ Δ₂ → EraseMapᵀ Δ₂ Δ₂' × Updateᴴ mt τ∈π Δ₁ Δ₂)
updateᴱ .(T.⟪ T.here ⟫) eᴹ (x G.∷ eᴱ) S.here = _ P., ((eᴹ G.∷ eᴱ) P., here)
updateᴱ ._ eᴹ (eˣ ∷ eᴱ) (S.there u) = P.map (_∷_ _) (P.map (_∷_ eˣ) there) (updateᴱ _ eᴹ eᴱ u)

open import Relation.Binary.PropositionalEquality hiding (subst)

data Redexᴱ {l τ} (x : Dec (l ⊑ A)) (p p'ᴱ : State l τ) : Set where
  Step : ∀ {p'} -> p ⇝ p' -> Erase x p' p'ᴱ -> Redexᴱ x p p'ᴱ

sim⇝ : ∀ {l π₁ π₂ τ τ₁ τ₂} {Δ₁ Δ₁' : Heap l π₁} {Δ₂'  : Heap l π₂} {t₁ t₁' : Term π₁ τ₁} {t₂' : Term π₂ τ₂} {S₁ S₁' : Stack l _ _ τ} {S₂' : Stack l _ _ τ} -> (l⊑A : l ⊑ A) -> EraseMapᵀ Δ₁ Δ₁' -> Eraseᵀ t₁ t₁' -> Eraseˢ S₁ S₁' -> ⟨ Δ₁' , t₁' , S₁' ⟩ ⇝ ⟨ Δ₂' , t₂' , S₂' ⟩ -> Redexᴱ (yes l⊑A) ⟨ Δ₁ , t₁ , S₁ ⟩ ⟨ Δ₂' , t₂' , S₂' ⟩
sim⇝ l⊑A eᴱ (G.App eᵀ eᵀ₁) eˢ (S₁.App₁ {τ₁ = τ₁} {π = π})
  = Step App₁ G.⟨ (just eᵀ₁) ∷ eᴱ , wkenᴱ eᵀ (drop refl-⊆) , ((Var _) ∷ wkenᴱˢ _ eˢ) ⟩
sim⇝ l⊑A eᴱ (G.Abs eᵀ) (G.Var α∈π G.∷ eˢ) (S₁.App₂ .α∈π) = Step (S₁.App₂ α∈π) G.⟨ eᴱ , substᴱ (lift-εᵀ (Var α∈π)) eᵀ  , eˢ ⟩
sim⇝ l⊑A eᴱ (G.Var ⟪ τ∈π ⟫) eˢ (S₁.Var₁ ⟪ .τ∈π ⟫ t∈Δ' ¬val' rᴱ') with memberᴱ ⟪ τ∈π ⟫ eᴱ t∈Δ'
... | t P., eᵀ P., t∈Δ with updateᴱ ⟪ ∈-∈ᴿ τ∈π ⟫ nothing eᴱ rᴱ'
... | Γ₂ P., e₂ᴱ P., rᴱ = Step (Var₁ ⟪ τ∈π ⟫ t∈Δ (¬valᴱ eᵀ ¬val') rᴱ) G.⟨ e₂ᴱ , eᵀ , ((G.# T.⟪ τ∈π ⟫) G.∷ eˢ) ⟩
sim⇝ l⊑A eᴱ (G.Var τ∈π) eˢ (S₁.Var₁' .τ∈π v∈Δ' val') with memberᴱ τ∈π eᴱ v∈Δ'
... | v P., eᵀ P., v∈Δ = Step (Var₁' τ∈π v∈Δ (valᴱ eᵀ val' )) G.⟨ eᴱ , eᵀ , eˢ ⟩
sim⇝ l⊑A eᴱ eᵀ (G.# ⟪ τ∈π ⟫ G.∷ eˢ) (S₁.Var₂ ⟪ .τ∈π ⟫ val' u'ᴱ) with updateᴱ ⟪ ∈-∈ᴿ τ∈π ⟫ (just eᵀ) eᴱ u'ᴱ
... | Δ₂ P., e₂ᴱ P., uᴱ = Step (Var₂ ⟪ τ∈π ⟫ (valᴱ eᵀ val') uᴱ) G.⟨ e₂ᴱ , eᵀ , eˢ ⟩
sim⇝ l⊑A eᴱ (G.If eᵀ Then eᵀ₁ Else eᵀ₂) eˢ S₁.If = Step S₁.If G.⟨ eᴱ , eᵀ , (G.Then eᵀ₁ Else eᵀ₂) G.∷ eˢ ⟩
sim⇝ l⊑A eᴱ G.True ((G.Then x Else x₁) G.∷ eˢ) S₁.IfTrue = Step S₁.IfTrue G.⟨ eᴱ , x , eˢ ⟩
sim⇝ l⊑A eᴱ G.False ((G.Then x Else x₁) G.∷ eˢ) S₁.IfFalse = Step S₁.IfFalse G.⟨ eᴱ , x , eˢ ⟩
sim⇝ l⊑A eᴱ (G.Return eᵀ) eˢ S₁.Return = Step S₁.Return G.⟨ eᴱ , G.Mac eᵀ , eˢ ⟩
sim⇝ l⊑A eᴱ (eᵀ G.>>= eᵀ₁) eˢ S₁.Bind₁ = Step S₁.Bind₁ G.⟨ eᴱ , eᵀ , G.Bind eᵀ₁ G.∷ eˢ ⟩
sim⇝ l⊑A eᴱ (G.Mac eᵀ) (G.Bind x G.∷ eˢ) S₁.Bind₂ = Step S₁.Bind₂ G.⟨ eᴱ , G.App x eᵀ , eˢ ⟩
sim⇝ l⊑A eᴱ (G.label h⊑A eᵀ) eˢ (S₁.Label' p) = Step (S₁.Label' p) G.⟨ eᴱ , G.Return (G.Res h⊑A (G.Id eᵀ)) , eˢ ⟩
sim⇝ l⊑A eᴱ (G.label' h⋤A eᵀ) eˢ (S₁.Label'∙ p) = Step (Label' p) G.⟨ eᴱ , (G.Return (Res∙ h⋤A)) , eˢ ⟩
sim⇝ l⊑A eᴱ (G.label∙ eᵀ) eˢ (S₁.Label'∙ p) = Step (Label'∙ p) G.⟨ eᴱ , (G.Return (Res∙ {!!})) , eˢ ⟩ -- TODO must store H⋤A in label∙
sim⇝ l⊑A eᴱ (G.unlabel p eᵀ) eˢ (S₁.Unlabel₁ .p) = Step (S₁.Unlabel₁ p) G.⟨ eᴱ , eᵀ , G.unlabel p G.∷ eˢ ⟩
sim⇝ l⊑A eᴱ (G.Res x eᵀ) (G.unlabel p G.∷ eˢ) (S₁.Unlabel₂ .p) = Step (S₁.Unlabel₂ p) G.⟨ eᴱ , G.Return (G.unId eᵀ) , eˢ ⟩
sim⇝ l⊑A eᴱ (G.Res∙ x) (G.unlabel p G.∷ eˢ) (S₁.Unlabel₂ .p) = ⊥-elim (x (trans-⊑ p l⊑A))
sim⇝ l⊑A eᴱ (G.unId eᵀ) eˢ S₁.UnId₁ = Step S₁.UnId₁ G.⟨ eᴱ , eᵀ , G.unId G.∷ eˢ ⟩
sim⇝ l⊑A eᴱ (G.Id eᵀ) (G.unId G.∷ eˢ) S₁.UnId₂ = Step S₁.UnId₂ G.⟨ eᴱ , eᵀ , eˢ ⟩
sim⇝ l⊑A G.∙ G.∙ G.∙ S₁.Hole₂ = Step S₁.Hole₂ G.⟨ G.∙ , G.∙ , G.∙ ⟩
sim⇝ l⊑A eᴱ (G.new l⊑h h⊑A eᵀ) eˢ (S₁.New₁ ¬var) = Step (New₁ (¬varᴱ eᵀ ¬var)) G.⟨ (G.just eᵀ G.∷ eᴱ) , (G.new l⊑h h⊑A (G.Var T.⟪ _ ⟫)) , wkenᴱˢ _ eˢ ⟩
sim⇝ l⊑A eᴱ (G.new' l⊑h h⋤A eᵀ) eˢ (S₁.New∙₁ ¬var) = Step (New₁ (¬varᴱ eᵀ ¬var)) G.⟨ G.just eᵀ G.∷ eᴱ , G.new' l⊑h h⋤A (G.Var T.⟪ _ ⟫) , wkenᴱˢ _ eˢ ⟩
sim⇝ l⊑A eᴱ (G.new∙ l⊑h eᵀ) eˢ (S₁.New∙₁ ¬var) = Step (New∙₁ (¬varᴱ eᵀ ¬var)) G.⟨ G.just eᵀ G.∷ eᴱ , G.new∙ l⊑h (G.Var T.⟪ _ ⟫) , wkenᴱˢ _ eˢ ⟩
sim⇝ l⊑A eᴱ (G.write l⊑H h⊑A eᵀ eᵀ₁) eˢ S₁.Write₁ = Step Write₁ G.⟨ (G.just eᵀ₁ G.∷ eᴱ) , (wkenᴱ eᵀ (drop refl-⊆)) , write l⊑H h⊑A ⟪ _ ⟫ ∷ wkenᴱˢ _ eˢ ⟩
sim⇝ l⊑A eᴱ (G.write' l⊑H h⋤A eᵀ eᵀ₁) eˢ S₁.Write∙₁ = Step Write₁ G.⟨ (G.just eᵀ₁ G.∷ eᴱ) , (wkenᴱ eᵀ (drop refl-⊆)) , ((G.write' l⊑H h⋤A ⟪ _ ⟫) G.∷ wkenᴱˢ _ eˢ) ⟩
sim⇝ l⊑A eᴱ (G.write∙ l⊑H eᵀ eᵀ₁) eˢ S₁.Write∙₁ = Step Write∙₁ G.⟨ (G.just eᵀ₁ G.∷ eᴱ) , (wkenᴱ eᵀ (drop refl-⊆)) , ((write∙ l⊑H ⟪ _ ⟫) G.∷ wkenᴱˢ _ eˢ) ⟩
sim⇝ l⊑A eᴱ (G.read L⊑l eᵀ) eˢ S₁.Read₁ = Step S₁.Read₁ G.⟨ eᴱ , eᵀ , G.read L⊑l G.∷ eˢ ⟩

memberᴴ : ∀ {h π ls} {Δ' : Heap h π} {Γ Γ' : Heaps ls} (h⊑A : h ⊑ A) ->
          EraseMapᴴ Γ Γ' -> h ↦ ⟨ Δ' ⟩ ∈ᴱ Γ' -> Σ (Heap h π) (λ Δ -> Eraseᴴ (yes h⊑A) (⟨ Δ ⟩) (⟨ Δ' ⟩) × h ↦ ⟨ Δ ⟩ ∈ᴱ Γ)
memberᴴ {H} h⊑A (x ∷ e) S.here with H ⊑? A
memberᴴ h⊑A (G.Mapᵀ p x G.∷ e) S.here | yes .p = _ P., G.Mapᵀ h⊑A x P., here
memberᴴ h⊑A (() ∷ e) S.here | no ¬p
memberᴴ h⊑A (x ∷ e) (S.there x₁) = P.map id (P.map id there) (memberᴴ h⊑A e x₁)

updateᴴ : ∀ {h ls} {M₁ M₁' : Memory h} {Ms₁ Ms₁' Ms₂' : Memories ls} (h⊑A : h ⊑ A) ->
          EraseMapᴹ Ms₁ Ms₁' -> Eraseᴹ (yes h⊑A) M₁ M₁' -> Ms₂' ≔ Ms₁' [ h ↦ M₁' ]ˢ ->  ∃ (λ Ms₂ -> Ms₂ ≔ Ms₁ [ h ↦ M₁ ]ˢ)
updateᴴ h⊑A (x G.∷ map-eᴹ) (G.Id .h⊑A) S.here = _ P., here
updateᴴ h⊑A (x G.∷ map-eᴹ) eᴹ (S.there u₁) = P.map (_∷_ _) there (updateᴴ h⊑A map-eᴹ eᴹ u₁)

newᴱᴹ : ∀ {L τ} {L⊑A : L ⊑ A}  {M₁ M₂ : Memory L} -> (c : Cell L τ) ->
         Eraseᴹ (yes L⊑A) M₁ M₂ -> Eraseᴹ (yes L⊑A) (newᴹ c M₁) (newᴹ c M₂)
newᴱᴹ c (G.Id L⊑A) = G.Id L⊑A

writeᴹ : ∀ {h ls} {M : Memory h} {Ms₁ Ms₁' Ms₂' : Memories ls} (h⊑A : h ⊑ A) ->
           EraseMapᴹ Ms₁ Ms₁' -> Ms₂' ≔ Ms₁' [ h ↦ M ]ˢ -> ∃ (λ Ms₂ -> Ms₂ ≔ Ms₁ [ h ↦ M ]ˢ)
writeᴹ H⊑A (x G.∷ e) S.here = _ P., here
writeᴹ H⊑A (x G.∷ e) (S.there u₁) = P.map (_∷_ _) there (writeᴹ H⊑A e u₁)

-- import Sequential.Valid as V
-- open V 𝓛

-- mk-∈ : ∀ {l ls} -> l ∈ ls -> {Γ : Heaps ls} -> validᴴ Γ -> ∃ (λ H → l ↦ H ∈ᴴ Γ × validᴴ₂ Γ H)
-- mk-∈ T.here {H S.∷ Γ} (proj₁ P., proj₂) = H P., here P., proj₁
-- mk-∈ (T.there l∈ls) {x S.∷ Γ} (proj₁ P., proj₂) with mk-∈ l∈ls {Γ} proj₂
-- mk-∈ (T.there l∈ls) {x S.∷ Γ} (proj₂ P., proj₃) | H' P., H∈Γ P., H'ⱽ = H' P., ((there H∈Γ) P., (wkenᴴ₂ (drop refl-⊆ᴴ) H'ⱽ))

-- simᴾ : ∀ {l ls τ} {p p' : Program l ls τ} {l⊑A : l ⊑ A} {{pⱽ : validᴾ p}} -> Eraseᴾ (yes l⊑A) p p' -> ¬ (Redexᴾ p) -> ¬ (Redexᴾ p')

-- simᴾ {l⊑A = l⊑A} ⟨ e₁ᴴ  , eᵀ₁ , e₁ˢ  ⟩ ¬redex (S₁.Step (S₁.Pure l∈Γ' step' uᴴ')) with memberᴴ l⊑A e₁ᴴ l∈Γ'
-- ... | Δ P., ⟨ ._ , e₁ᴱ ⟩ P., l∈Γ with sim⇝ l⊑A  e₁ᴱ eᵀ₁ e₁ˢ step'
-- ... | Step step ⟨ e₂ᴱ , e₂ᵀ , e₂ˢ ⟩ with updateᴴ l⊑A e₁ᴴ ⟨ l⊑A , e₂ᴱ ⟩ uᴴ'
-- ... | Γ₂ P., uᴴ = ⊥-elim (¬redex (S₁.Step (Pure l∈Γ step uᴴ)))

-- simᴾ ⟨ x , new l⊑h h⊑A (Var τ∈π) , x₂ ⟩ ¬redex (S₁.Step (S₁.New H∈Γ' uᴴ')) with memberᴴ h⊑A x H∈Γ'
-- ... | Δ P., eˣ P., H∈Γ with updateᴴ h⊑A x (newᴱᴹ ∥ l⊑h , τ∈π ∥ eˣ) uᴴ'
-- ... | Γ₂ P., uᴴ = ⊥-elim (¬redex (S₁.Step (New H∈Γ uᴴ)))

-- -- In the original program a high reference was created, however in the erased
-- -- world I have lost all information about it, hence I cannot recreate the original step.
-- -- I believe that this could be fixed by keeping H∈Γ and uᴴ around in New∙ (without actually making the change)
-- -- in order to replicate the step as I did for New.
-- simᴾ {{pⱽ = Γⱽ P., (H∈ls P., tt) P., Sⱽ}} G.⟨ Γ , G.new' l⊑h h⋤A (G.Var τ∈π) , S ⟩ ¬redex (S₁.Step S₁.New∙) with mk-∈ H∈ls Γⱽ
-- simᴾ {{Γⱽ P., (H∈ls P., T.tt) P., Sⱽ}} G.⟨ Γ₁ , G.new' l⊑h h⋤A (G.Var τ∈π) , S₁ ⟩ ¬redex (S₁.Step S₁.New∙)
--   | S.⟨ M , Δ ⟩ P., H∈Γ P., (Mⱽ  P., Δⱽ) =  ⊥-elim (¬redex (Step (New {!H∈Γ!} {!!})))  -- new x is a redex
-- simᴾ {l} {ls} {τ} {._} {._} {l⊑A} {{Γⱽ P., (H∈ls P., T.tt) P., Sⱽ}} G.⟨ Γ₁ , G.new' l⊑h h⋤A (G.Var τ∈π) , S₁ ⟩ ¬redex (S₁.Step S₁.New∙)
--   | S.∙ P., H∈Γ P., ()

-- simᴾ ⟨ x , new∙ l⊑h (Var ._) , x₂ ⟩ ¬redex (Step New∙) = ⊥-elim (¬redex (Step New∙))

-- simᴾ ⟨ x , Res x₁ #[ n ] , write l⊑H H⊑A τ∈π ∷ x₃ ⟩ ¬redex (S₁.Step (S₁.Write₂ H∈Γ' u'ᴹ u'ᴴ)) with memberᴴ H⊑A x H∈Γ'
-- ... | Δ P., _ P., H∈Γ with writeᴴ {Δ = Δ} H⊑A x u'ᴴ
-- ... | Γ₂ P., uᴴ = ⊥-elim (¬redex (S₁.Step (Write₂ H∈Γ u'ᴹ uᴴ)))

-- simᴾ ⟨ x , Res x₁ #[ n ]ᴰ , write l⊑H H⊑A ._ ∷ x₃ ⟩ ¬redex (S₁.Step (S₁.Writeᴰ₂ H∈Γ' u'ᴹ u'ᴴ)) with memberᴴ H⊑A x H∈Γ'
-- ... | Δ P., _ P., H∈Γ with writeᴴ {Δ = Δ} H⊑A x u'ᴴ
-- ... | Γ₂ P., uᴴ = ⊥-elim (¬redex (S₁.Step (Writeᴰ₂ H∈Γ u'ᴹ uᴴ)))

-- simᴾ ⟨ x , Res x₁ x₂ , write' l⊑H H⋤A ._ ∷ x₃ ⟩ ¬redex (S₁.Step S₁.Write∙₂) = ⊥-elim (¬redex (S₁.Step {!Write₂ ? ? ?!}))
-- simᴾ ⟨ x , Res x₁ x₂ , write∙ l⊑H ._ ∷ x₃ ⟩ ¬redex (S₁.Step S₁.Write∙₂) = ⊥-elim (¬redex (Step Write∙₂))

-- simᴾ ⟨ x , Res∙ x₁ , write' l⊑H H⋤A ._ ∷ x₂ ⟩ ¬redex (S₁.Step S₁.Write∙₂) = ⊥-elim (¬redex (S₁.Step {!Write₂ ? ? ?!}))
-- simᴾ ⟨ x , Res∙ x₁ , write∙ l⊑H ._ ∷ x₂ ⟩ ¬redex (S₁.Step S₁.Write∙₂) = ⊥-elim (¬redex (S₁.Step Write∙₂))

-- simᴾ {l⊑A = l⊑A} ⟨ x , Res x₁ #[ n ] , read ._ ∷ x₃ ⟩ ¬redex (S₁.Step (S₁.Read₂ l∈Γ' n∈M)) with memberᴴ l⊑A x l∈Γ'
-- ... | Δ P., ⟨ ._ , eᴱ ⟩ P., l∈Γ = ⊥-elim (¬redex (S₁.Step (Read₂ l∈Γ n∈M)))
-- simᴾ {l⊑A = l⊑A} ⟨ x , Res x₁ #[ n ]ᴰ , read L⊑l ∷ x₃ ⟩ ¬redex (S₁.Step (S₁.Readᴰ₂ L∈Γ' n∈M)) with memberᴴ (trans-⊑ L⊑l l⊑A) x L∈Γ'
-- ... | Δ P., ⟨ ._ , eᴱ ⟩ P., l∈Γ = ⊥-elim (¬redex (S₁.Step (Readᴰ₂ l∈Γ n∈M)))

-- simᴾ {l⊑A = l⊑A}⟨ x , deepDup (Var τ∈π) , x₂ ⟩ ¬redex (S₁.Step (S₁.DeepDupˢ {Δ = Δ'} L⊏l L∈Γ' t∈Δ')) with memberᴴ (trans-⊑ (proj₁ L⊏l) l⊑A) x L∈Γ'
-- ... | Δ P., ⟨ ._ , eᴱ ⟩ P., L∈Γ with memberᴱ τ∈π eᴱ t∈Δ'
-- ... | t P., eᵀ P., t∈Δ = ⊥-elim (¬redex (S₁.Step (DeepDupˢ L⊏l L∈Γ t∈Δ)))

-- simᴾ ∙ᴸ ¬redex (S₁.Step x₃) = ¬redex (S₁.Step x₃)
