import Lattice as L

module Sequential.Security.Lemmas2 (𝓛 : L.Lattice) (A : L.Label 𝓛) where

open import Types 𝓛
open import Sequential.Security.Erasure 𝓛 A as SE
import Sequential.Security.Graph as G
open G 𝓛 A

--------------------------------------------------------------------------------
-- Temporarily side-step bug #2245

import Sequential.Calculus as SC
open SC 𝓛

--------------------------------------------------------------------------------

import Sequential.Semantics as SS
open SS 𝓛

open import Sequential.Security.LowEq 𝓛 A renaming (⟨_,_,_⟩ to is≈ᴾ ; ⟨_,_⟩ to is≈ᵀ)

open import Sequential.Valid 𝓛

open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Relation.Nullary


val-≈ : ∀ {π τ} {t₁ t₂ : Term π τ} -> t₁ ≈ᵀ t₂ -> Value t₁ -> Value t₂
val-≈ (is≈ᵀ e₁ e₂) val = valᴱ e₂ (val₁ᴱ e₁ val)

done-≈ : ∀ {l τ} {Ts₁ Ts₂ : TS∙ l τ} {l⊑A : l ⊑ A} -> Ts₁ ≈ᵀˢ⟨ (yes l⊑A) ⟩ Ts₂ -> IsDoneTS Ts₁ -> IsDoneTS Ts₂
done-≈ (Kᵀˢ G.⟨ x₃ , G.[] ⟩ G.⟨ x₁ , G.[] ⟩) (SS.isDoneTS isVal) = isDoneTS (val-≈ (is≈ᵀ x₃  x₁) isVal)

fork-≈ : ∀ {π τ} {t₁ t₂ : Term π τ} -> t₁ ≈ᵀ t₂ -> (IsFork t₁) -> (IsFork t₂)
fork-≈ t₁≈t₂ isFork = fork-≈' isFork t₁≈t₂
  where -- Pattern matching in the original order hits a bug.
        fork-≈' : ∀ {π τ} {t₁ t₂ : Term π τ} -> (IsFork t₁) -> t₁ ≈ᵀ t₂ -> (IsFork t₂)
        fork-≈' (SC.Fork p t) (is≈ᵀ (G.fork .p h⊑A e₁) (G.fork .p h⊑A₁ e₂) ) = SC.Fork p _
        fork-≈' (SC.Fork p t) (is≈ᵀ (G.fork' .p h⋤A e₁) (G.fork' .p h⋤A₁ e₂) ) = SC.Fork p _
        fork-≈' (SC.Fork p t) (is≈ᵀ (G.fork' .p h⋤A e₁) (G.fork∙ .p e₂) ) = SC.Fork∙ p _
        fork-≈' (SC.Fork∙ p t) (is≈ᵀ (G.fork∙ .p e₁) (G.fork' .p h⋤A e₂) ) = SC.Fork p _
        fork-≈' (SC.Fork∙ p t) (is≈ᵀ (G.fork∙ .p e₁) (G.fork∙ .p e₂) ) = SC.Fork∙ p _

forkTS-≈ : ∀ {l τ} {Ts₁ Ts₂ : TS∙ l τ} {l⊑A : l ⊑ A} -> Ts₁ ≈ᵀˢ⟨ yes l⊑A ⟩ Ts₂ -> (IsForkTS Ts₁) -> (IsForkTS Ts₂)
forkTS-≈ (Kᵀˢ G.⟨ eᵀ₁ , eˢ₁ ⟩ G.⟨ eᵀ , eˢ ⟩) (SS.isForkTS isFork) = SS.isForkTS (fork-≈ (is≈ᵀ eᵀ₁ eᵀ) isFork)

open import Data.Product

import Sequential.Calculus renaming (⟨_,_,_⟩ to mkᴾ ; ⟨_,_⟩ to mkᵀ)

redex⟼ : ∀ {ls l π τ τ'} {Ms₁ Ms₂ : Memories ls} {Γ₁ Γ₂ : Heaps ls} {p₁' : Program l ls τ}
             {t₁ t₂ : Term π τ'} {S₁ S₂ : Stack _ _ _ _} ->
             let p₁ = SC.mkᴾ Ms₁  Γ₁ (SC.mkᵀ t₁  S₁)
                 p₂ = SC.mkᴾ Ms₂  Γ₂ (SC.mkᵀ t₂ S₂) in
             validᴾ p₁ -> validᴾ p₂ ->  Ms₁ map-≈ᴹ Ms₂ -> Γ₁ map-≈ᴴ Γ₂ -> t₁ ≈ᵀ t₂ -> S₁ ≈ˢ S₂ ->
             p₁ ⟼ p₁' -> Redexᴾ p₂
redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ t₁≈t₂ S₁≈S₂ (SS.Pure l∈Γ step uᴹ) = {!!}
redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ t₁≈t₂ S₁≈S₂ (SS.New H∈Ms uᴹ) = {!!}
redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ t₁≈t₂ S₁≈S₂ SS.New∙ = {!!}
redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ t₁≈t₂ S₁≈S₂ (SS.Write₂ H∈Ms uᴹ uˢ) = {!!}
redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ t₁≈t₂ S₁≈S₂ (SS.Writeᴰ₂ H∈Ms uᴹ uˢ) = {!!}
redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ t₁≈t₂ S₁≈S₂ SS.Write∙₂ = {!!}
redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ t₁≈t₂ S₁≈S₂ (SS.Read₂ l∈Γ n∈M) = {!!}
redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ t₁≈t₂ S₁≈S₂ (SS.Readᴰ₂ L∈Ms n∈M) = {!!}
redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ t₁≈t₂ S₁≈S₂ (SS.DeepDup₁ ¬var l∈Γ uᴱ) = {!!}
redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ t₁≈t₂ S₁≈S₂ (SS.DeepDup₂ τ∈π L∈Γ t∈Δ l∈Γ uᴱ) = {!!}

redex-≈ : ∀ {l ls τ} {l⊑A : l ⊑ A} {p₁ p₂ : Program l ls τ} {{v₁ : validᴾ p₁}} {{v₂ : validᴾ p₂}} ->
            p₁ ≈ᴾ⟨ (yes l⊑A) ⟩ p₂ -> Redexᴾ p₁  -> Redexᴾ p₂
redex-≈ {{v₁}} {{v₂}} (is≈ᴾ  Ms₁≈Ms₂ Γ₁≈Γ₂ (Kᵀˢ G.⟨ eᵀ , eˢ ⟩ G.⟨ eᵀ₁ , eˢ₁ ⟩)) (SS.Step step)
  = redex⟼ v₁ v₂ Ms₁≈Ms₂ Γ₁≈Γ₂ (is≈ᵀ eᵀ eᵀ₁) (Kˢ eˢ eˢ₁) step
redex-≈ (is≈ᴾ Ms₁≈Ms₂  Γ₁≈Γ₂ (Kᵀˢ G.∙ᴸ G.∙ᴸ)) (SS.Step step) = SS.Step SS.Hole

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
