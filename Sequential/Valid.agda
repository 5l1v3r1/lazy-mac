import Lattice as L

module Sequential.Valid (𝓛 : L.Lattice) where

import Types as T
open T 𝓛

import Sequential.Calculus as S renaming (⟨_,_,_⟩ to mkP) hiding (wkenᴱ)
open S 𝓛

open import Data.Nat using (_≤_ ; _<_ ; s≤s ; z≤n ; decTotalOrder)
open import Data.Empty
--import Data.List as LL
open import Data.Product as P
open import Data.Maybe

-- open decTotalOrder ℕ renaming (trans to trans-≤)

-- A valid term contains only valid references, that contain a valid
-- address and no free-variables, i.e. variables unbounded in the
-- heap.

-- data Valid {l : Label} : ∀ {τ : Ty} -> State l τ -> Set where

-- validAddr : ∀ {l ls} -> l ∈ ls -> Heaps ls -> ℕ -> Set
-- validAddr here (⟨ M , Δ ⟩ ∷ Γ) n = n < lengthᴹ M
-- validAddr here (∙ ∷ _) n = ⊥
-- validAddr (there l∈ls) (_ S.∷ Γ) n = validAddr l∈ls Γ n

validAddr : ∀ {l} -> Memory l -> ℕ -> Set
validAddr M n = n < lengthᴹ M

validᵀ : ∀ {ls τ π} -> Heaps ls -> Term π τ -> Set
validᵀ Γ S.（） = ⊤
validᵀ Γ S.True = ⊤
validᵀ Γ S.False = ⊤
validᵀ Γ (S.Id t) = validᵀ Γ t
validᵀ Γ (S.unId t) = validᵀ Γ t
validᵀ Γ (S.Var τ∈π) = ⊤
validᵀ Γ (S.Abs t) = validᵀ Γ t
validᵀ Γ (S.App t t₁) = validᵀ Γ t × validᵀ Γ t₁
validᵀ Γ (S.If t Then t₁ Else t₂) = (validᵀ Γ t) × (validᵀ Γ t₁) × validᵀ Γ t₂
validᵀ Γ (S.Return l t) = validᵀ Γ t
validᵀ Γ (t S.>>= t₁) = (validᵀ Γ t) × (validᵀ Γ t₁)
validᵀ Γ (S.Mac l t) = validᵀ Γ t
validᵀ {ls} {τ = Res .l Addr} Γ (S.Res l S.#[ t ]) = Σ (l ∈ ls) (λ l∈ls -> validAddr (lookupᴹ l∈ls Γ) t )
validᵀ {ls} {τ = Res .l Addr} Γ (S.Res l S.#[ t ]ᴰ) = Σ (l ∈ ls) (λ l∈ls -> validAddr (lookupᴹ l∈ls Γ) t )
validᵀ {ls} Γ (S.Res l t) = validᵀ Γ t
validᵀ Γ (S.label l⊑h t) = validᵀ Γ t
validᵀ Γ (S.label∙ l⊑h t) = ⊥
validᵀ Γ (S.unlabel l⊑h t) = validᵀ Γ t
validᵀ Γ (S.read x t) = validᵀ Γ t
validᵀ Γ (S.write x t t₁) = (validᵀ Γ t) × (validᵀ Γ t₁)
validᵀ Γ (S.write∙ x t t₁) = ⊥
validᵀ Γ (S.new x t) = validᵀ Γ t
validᵀ Γ (S.new∙ x t) = ⊥
validᵀ Γ S.#[ x ] = ⊤
validᵀ Γ S.#[ x ]ᴰ = ⊤
validᵀ Γ (S.fork l⊑h t) = validᵀ Γ t
validᵀ Γ (S.fork∙ l⊑h t) = ⊥
validᵀ Γ (S.deepDup t) = validᵀ Γ t
validᵀ Γ S.∙ = ⊥

-- Should I impose validity of variables as well?
-- It does not seem necessary at the moment
validᶜ : ∀ {l ls τ₁ τ₂} -> Heaps ls -> Cont l τ₁ τ₂ -> Set
validᶜ Γ (S.Var τ∈π) = ⊤
validᶜ Γ (S.# τ∈π) = ⊤
validᶜ Γ (S.Then x Else x₁) = (validᵀ Γ x) × validᵀ Γ x₁
validᶜ Γ (S.Bind x) = validᵀ Γ x
validᶜ Γ (S.unlabel p) = ⊤
validᶜ Γ S.unId = ⊤
validᶜ Γ (S.write x τ∈π) = ⊤
validᶜ Γ (S.write∙ x τ∈π) = ⊥
validᶜ Γ (S.read x) = ⊤

validˢ : ∀ {l ls τ₁ τ₂} -> Heaps ls -> Stack l τ₁ τ₂ -> Set
validˢ Γ S.[] = ⊤
validˢ Γ (C S.∷ S) = validᶜ Γ C × validˢ Γ S
validˢ Γ S.∙ = ⊥

validᴱ : ∀ {l π ls} -> Heaps ls -> Env l π -> Set
validᴱ Γ S.[] = ⊤
validᴱ Γ (just t S.∷ Δ) = validᵀ Γ t × validᴱ Γ Δ
validᴱ Γ (nothing S.∷ Δ) = validᴱ Γ Δ
validᴱ Γ S.∙ = ⊥

validᴹ : ∀ {l} -> (M : Memory l) -> Set
validᴹ S.[] = ⊤
validᴹ (cᴸ S.∷ M) = validᴹ M
validᴹ S.∙ = ⊥

validᴴ₂ : ∀ {l ls} (Γ : Heaps ls) (H : Heap l) -> Set
validᴴ₂ Γ S.⟨ M , Δ ⟩ = validᴹ M × validᴱ Γ Δ
validᴴ₂ Γ S.∙ = ⊥

validᴴ : ∀ {ls} -> Heaps ls -> Set
validᴴ {ls} Γ = ∀ {l} -> (l∈ls : l ∈ ls) -> validᴴ₂ Γ (lookupᴴ l∈ls Γ)

validᴾ : ∀ {l ls τ} -> Program l ls τ -> Set
validᴾ (S.mkP Γ t S ) = validᴴ Γ × (validᵀ Γ t) × (validˢ Γ S)
validᴾ S.∙ = ⊥

valid-𝓛 : (ls : List Label) -> Set
valid-𝓛 [] = ⊤
valid-𝓛 (l ∷ ls) = Unique l ls × valid-𝓛 ls

---------------------------------------------------------------------------------

Γ₀ : {ls : List Label} {{us : valid-𝓛 ls}} -> Heaps ls
Γ₀ {[]} {{_}} = []
Γ₀ {l ∷ ls} {{u , us}} = ⟨ [] , [] ⟩ ∷ Γ₀

wkenᵀ : ∀ {l π τ ls} {u : Unique l ls} {H : Heap l} {Γ : Heaps ls} (t : Term π τ) -> validᵀ Γ t -> validᵀ (H ∷ Γ) t
wkenᵀ S.（） ok = T.tt
wkenᵀ S.True ok = T.tt
wkenᵀ S.False ok = T.tt
wkenᵀ (S.Id t) ok = wkenᵀ t ok
wkenᵀ (S.unId t) ok = wkenᵀ t ok
wkenᵀ (S.Var τ∈π) ok = T.tt
wkenᵀ (S.Abs t) ok = wkenᵀ t ok
wkenᵀ (S.App t t₁) (proj₁ , proj₂) = (wkenᵀ t proj₁) , (wkenᵀ t₁ proj₂)
wkenᵀ (S.If t Then t₁ Else t₂) (proj₁ , proj₂ , proj₃) = (wkenᵀ t proj₁) , ((wkenᵀ t₁ proj₂) , (wkenᵀ t₂ proj₃))
wkenᵀ (S.Return l₁ t) ok = wkenᵀ t ok
wkenᵀ (t S.>>= t₁) (proj₁ , proj₂) = (wkenᵀ t proj₁) , (wkenᵀ t₁ proj₂)
wkenᵀ (S.Mac l₁ t) ok = wkenᵀ t ok
wkenᵀ {τ = T.Res .l₁ T.（）} (S.Res l₁ t) ok = wkenᵀ t ok
wkenᵀ {τ = T.Res .l₁ T.Bool} (S.Res l₁ t) ok = wkenᵀ t ok
wkenᵀ {τ = T.Res .l₁ (τ T.=> τ₁)} (S.Res l₁ t) ok = wkenᵀ t ok
wkenᵀ {τ = T.Res .l₂ (T.Mac l₁ τ)} (S.Res l₂ t) ok = wkenᵀ t ok
wkenᵀ {τ = T.Res .l₂ (T.Res l₁ τ)} (S.Res l₂ t) ok = wkenᵀ t ok
wkenᵀ {τ = T.Res .l₁ (T.Id τ)} (S.Res l₁ t) ok = wkenᵀ t ok
wkenᵀ {τ = T.Res .l₁ T.Addr} (S.Res l₁ (S.unId t)) ok = wkenᵀ t ok
wkenᵀ {τ = T.Res .l₁ T.Addr} (S.Res l₁ (S.Var τ∈π)) ok = tt
wkenᵀ {τ = T.Res .l₁ T.Addr} (S.Res l₁ (S.App t t₁))  (proj₁ , proj₂) = (wkenᵀ t proj₁) , (wkenᵀ t₁ proj₂)
wkenᵀ {τ = T.Res .l₁ T.Addr} (S.Res l₁ (S.If t Then t₁ Else t₂))
  (proj₁ , proj₂ , proj₃) = (wkenᵀ t proj₁) , ((wkenᵀ t₁ proj₂) , (wkenᵀ t₂ proj₃))
wkenᵀ {τ = T.Res .l₁ T.Addr} (S.Res l₁ S.#[ x ]) (l∈ls , proj₂) = there l∈ls , proj₂
wkenᵀ {τ = T.Res .l₁ T.Addr} (S.Res l₁ S.#[ x ]ᴰ) (l∈ls , proj₂) = there l∈ls , proj₂
wkenᵀ {τ = T.Res .l₁ T.Addr} (S.Res l₁ (S.deepDup t)) ok = wkenᵀ t ok
wkenᵀ {τ = T.Res .l₁ T.Addr} (S.Res l₁ S.∙) ()
wkenᵀ (S.label l⊑h t) ok = wkenᵀ t ok
wkenᵀ (S.label∙ l⊑h t) ()
wkenᵀ (S.unlabel l⊑h t) ok = wkenᵀ t ok
wkenᵀ (S.read x t) ok = wkenᵀ t ok
wkenᵀ (S.write x t t₁) (proj₁ , proj₂) = (wkenᵀ t proj₁) , (wkenᵀ t₁ proj₂)
wkenᵀ (S.write∙ x t t₁) ()
wkenᵀ (S.new x t) ok = wkenᵀ t ok
wkenᵀ (S.new∙ x t) ()
wkenᵀ S.#[ x ] ok = T.tt
wkenᵀ S.#[ x ]ᴰ ok = T.tt
wkenᵀ (S.fork l⊑h t) ok = wkenᵀ t ok
wkenᵀ (S.fork∙ l⊑h t) ()
wkenᵀ (S.deepDup t) ok = wkenᵀ t ok
wkenᵀ S.∙ ()

wkenᴱ : ∀ {l l' π ls} {u : Unique l ls} {H : Heap l} {Γ : Heaps ls} {Δ : Env l' π} -> validᴱ Γ Δ -> validᴱ (H ∷ Γ) Δ
wkenᴱ {Δ = S.[]} Δᴱ = tt
wkenᴱ {Δ = just t S.∷ Δ} (tⱽ , Δᴱ) = wkenᵀ t tⱽ , wkenᴱ {Δ = Δ} Δᴱ
wkenᴱ {Δ = nothing S.∷ Δ} Δᴱ = wkenᴱ {Δ = Δ} Δᴱ
wkenᴱ {Δ = S.∙} ()

wkenᴴ : ∀ {l₁ l₂ ls} {Γ : Heaps ls} {H₁ : Heap l₁} {H₂ : Heap l₂} {u : Unique l₁ ls} -> validᴴ₂ Γ H₂ -> validᴴ₂ (H₁ ∷ Γ) H₂
wkenᴴ {H₂ = S.⟨ M , Δ ⟩} (a , b) = a , wkenᴱ {Δ = Δ} b
wkenᴴ {H₂ = S.∙} ()

validᴴ₀ : ∀ {ls : List Label} {{us : valid-𝓛 ls}} -> validᴴ {ls} Γ₀
validᴴ₀ T.here = T.tt , T.tt
validᴴ₀ {{u , us}} (T.there l∈ls) = wkenᴴ (validᴴ₀ {{us}} l∈ls)

S₀ : ∀ {l τ} -> Stack l τ τ
S₀ = []

validˢ₀ : ∀ {l τ ls} -> (Γ : Heaps ls) -> validˢ Γ (S₀ {l} {τ})
validˢ₀ Γ = tt

P₀ : ∀ {ls l τ π} {{us : valid-𝓛 ls}} -> Term π τ -> Program l ls τ
P₀ {{us = us}} t = mkP Γ₀ t S₀

-- Initial configurations are valid given a valid initial term,
-- i.e. it does not have no free variables and references.
validᴾ₀ : ∀ {τ l ls} {t : Term [] τ} {{us : valid-𝓛 ls}} -> validᵀ (Γ₀ {{us}}) t -> validᴾ (P₀ {l = l} {{us}} t)
validᴾ₀ vᵀ = validᴴ₀ , vᵀ , tt

--------------------------------------------------------------------------------

import Sequential.Semantics as SS
open SS 𝓛

open import Relation.Binary.PropositionalEquality
open import Function

valid-memberᴴ : ∀ {l ls π} {Γ : Heaps ls} {M : Memory l} {Δ : Env l π} -> validᴴ Γ -> l ↦ ⟨ M , Δ ⟩ ∈ᴴ Γ -> validᴹ M × validᴱ Γ Δ
valid-memberᴴ {Γ = Γ} Γⱽ l∈Γ = {!!}
-- with lookupᴴ (member-∈ l∈Γ) Γ | Γⱽ (member-∈ l∈Γ)
-- valid-memberᴴ Γⱽ l∈Γ | S.⟨ x , x₁ ⟩ | proj₁ , proj₂  rewrite sym (lookupᴴ-≡ (member-∈ l∈Γ) l∈Γ) = {!!}
-- valid-memberᴴ Γⱽ l∈Γ | S.∙ | ()
-- aux
--   where aux : ∀ {l ls₁ ls₂ π} {Γ₁ : Heaps ls₁} {Γ₂ : Heaps ls₂} {M : Memory l} {Δ : Env l π} ->
--               validᴴ Γ₁ Γ₂ -> l ↦ ⟨ M , Δ ⟩ ∈ᴴ Γ₂ -> validᴹ M × validᴱ Γ₁ Δ
--         aux (proj₁ , proj₂) S.here = proj₁
--         aux (proj₁ , proj₂) (S.there x₁) = aux proj₂ x₁

valid-newᴹ : ∀ {l τ} (c : Cell l τ) (M : Memory l) -> validᴹ M -> validᴹ (newᴹ c M) × (lengthᴹ M < lengthᴹ (newᴹ c M))
valid-newᴹ c S.[] ok-M = tt , s≤s z≤n
valid-newᴹ c (cᴸ S.∷ M) ok-M = P.map id s≤s (valid-newᴹ c M ok-M)
valid-newᴹ c S.∙ ()

valid-new-Addr : ∀ {l ls τ π} {Γ Γ' : Heaps ls} {Δ : Env l π} {M : Memory l} -> validᴹ M -> (c : Cell l τ) ->
              (uᴴ : Γ' ≔ Γ [ l ↦ ⟨ newᴹ c M , Δ ⟩ ]ᴴ) -> validAddr (lookupᴹ (update-∈ uᴴ) Γ') (lengthᴹ M)
valid-new-Addr {M = M} Mᵛ c (S.there uᴴ) = valid-new-Addr {M = M} Mᵛ c uᴴ
valid-new-Addr {M = M} Mᵛ c S.here = aux {c = c} {M = M} Mᵛ
 where aux : ∀ {l τ} {c : Cell l τ} {M : Memory l} -> validᴹ M -> lengthᴹ M < lengthᴹ (newᴹ c M)
       aux {M = S.[]} M≠∙ = s≤s z≤n
       aux {M = cᴸ S.∷ M} M≠∙ = s≤s (aux {M = M} M≠∙)
       aux {M = S.∙} ()


open import Relation.Binary as B
open B.DecTotalOrder Data.Nat.decTotalOrder renaming (trans to trans-≤ ; refl to refl-≤)

update-valid-Addr : ∀ {l} {M₁ M₂ : Memory l} {n : ℕ} -> validAddr M₁ n ->
                    validᴹ M₁ -> validᴹ M₂ -> lengthᴹ M₁ Data.Nat.≤ lengthᴹ M₂ -> validAddr M₂ n
update-valid-Addr {_} {M₁} {M₂} aⱽ Mⱽ₁ Mⱽ₂ M₁≤M₂ = trans-≤ aⱽ M₁≤M₂

newᴹ-≤ : ∀ {l τ} (M : Memory l) (c : Cell l τ) -> lengthᴹ M Data.Nat.≤ lengthᴹ (newᴹ c M)
newᴹ-≤ S.[] c = z≤n
newᴹ-≤ (cᴸ S.∷ M) c = s≤s (newᴹ-≤ M c)
newᴹ-≤ S.∙ c = refl-≤

newᴴ-≤ : ∀ {l π ls} {Γ₁ Γ₂ : Heaps ls} {M₁ M₂ : Memory l} {Δ : Env l π} -> l ↦ ⟨ M₁ , Δ ⟩ ∈ᴴ Γ₁ -> Γ₂ ≔ Γ₁ [ l ↦ ⟨ M₂ , Δ ⟩ ]ᴴ ->
           (lengthᴹ M₁) Data.Nat.≤ (lengthᴹ M₂) ->
          (∀ {l} -> (l∈ls : l ∈ ls) ->
             lengthᴹ (lookupᴹ l∈ls Γ₁) Data.Nat.≤ lengthᴹ (lookupᴹ l∈ls Γ₂))
newᴴ-≤ S.here S.here M₁≤M₂ T.here = M₁≤M₂
newᴴ-≤ S.here S.here _ (T.there l∈ls) = refl-≤
newᴴ-≤ {l} S.here (S.there {u = u} y) = ⊥-elim (∈-not-unique (update-∈ y) u)
newᴴ-≤ (S.there {u = u} x) S.here = ⊥-elim (∈-not-unique (member-∈ x) u)
newᴴ-≤ {Γ₁ = S.⟨ x , x₁ ⟩ S.∷ Γ₁} (S.there x₂) (S.there y) _ T.here = refl-≤
newᴴ-≤ {Γ₁ = S.∙ S.∷ Γ₁} (S.there x) (S.there y) _ T.here = refl-≤
newᴴ-≤ (S.there x) (S.there y) M₁≤M₂ (T.there z) = newᴴ-≤ x y M₁≤M₂ z

update-validᵀ : ∀ {l π  π'  τ ls} {Γ Γ' : Heaps ls} {Δ : Env l π} {M₁ M₂ : Memory l} ->
                l ↦ ⟨ M₁ , Δ ⟩ ∈ᴴ Γ ->
                Γ' ≔ Γ [ l ↦ ⟨ M₂ , Δ ⟩ ]ᴴ -> (lengthᴹ M₁) Data.Nat.≤ (lengthᴹ M₂) -> (t : Term π' τ) -> validᵀ Γ t -> validᵀ Γ' t
update-validᵀ l∈Γ u M₁≤M₂ S.（） tⱽ = tt
update-validᵀ l∈Γ u M₁≤M₂ S.True tⱽ = tt
update-validᵀ l∈Γ u M₁≤M₂ S.False tⱽ = tt
update-validᵀ l∈Γ u M₁≤M₂ (S.Id t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ l∈Γ u M₁≤M₂ (S.unId t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ l∈Γ u M₁≤M₂ (S.Var τ∈π) tⱽ = tt
update-validᵀ l∈Γ u M₁≤M₂ (S.Abs t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ l∈Γ u M₁≤M₂ (S.App t t₁) (tⱽ , t₁ⱽ) = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ , update-validᵀ l∈Γ u M₁≤M₂ t₁ t₁ⱽ
update-validᵀ l∈Γ u M₁≤M₂ (S.If t Then t₁ Else t₂) (tⱽ , t₁ⱽ , t₂ⱽ)
  = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ , update-validᵀ l∈Γ u M₁≤M₂ t₁ t₁ⱽ , update-validᵀ l∈Γ u M₁≤M₂ t₂ t₂ⱽ
update-validᵀ l∈Γ u M₁≤M₂ (S.Return l₁ t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ l∈Γ u M₁≤M₂ (t S.>>= t₁) (tⱽ , t₁ⱽ) = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ , update-validᵀ l∈Γ u M₁≤M₂ t₁ t₁ⱽ
update-validᵀ l∈Γ u M₁≤M₂ (S.Mac l₁ t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ {τ = Res .l₁ （）} l∈Γ u M₁≤M₂ (S.Res l₁ t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ {τ = Res .l₁ Bool} l∈Γ u M₁≤M₂ (S.Res l₁ t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ {τ = Res .l₁ (τ => τ₁)} l∈Γ u M₁≤M₂ (S.Res l₁ t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ {τ = Res .l₂ (Mac l₁ τ)} l∈Γ u M₁≤M₂ (S.Res l₂ t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ {τ = Res .l₂ (Res l₁ τ)} l∈Γ u M₁≤M₂ (S.Res l₂ t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ {τ = Res .l₁ (Id τ)} l∈Γ u M₁≤M₂ (S.Res l₁ t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ {τ = Res .l₁ Addr} l∈Γ u M₁≤M₂ (S.Res l₁ (S.unId t)) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ {τ = Res .l₁ Addr} l∈Γ u M₁≤M₂ (S.Res l₁ (S.Var τ∈π)) tⱽ = tt
update-validᵀ {τ = Res .l₁ Addr} l∈Γ u M₁≤M₂ (S.Res l₁ (S.App t t₁)) (tⱽ , t₁ⱽ) = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ , update-validᵀ l∈Γ u M₁≤M₂ t₁ t₁ⱽ
update-validᵀ {τ = Res .l₁ Addr} l∈Γ u M₁≤M₂ (S.Res l₁ (S.If t Then t₁ Else t₂)) (tⱽ , t₁ⱽ , t₂ⱽ)
  = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ , update-validᵀ l∈Γ u M₁≤M₂ t₁ t₁ⱽ , update-validᵀ l∈Γ u M₁≤M₂ t₂ t₂ⱽ
update-validᵀ {τ = Res .l₁ Addr} l∈Γ u M₁≤M₂ (S.Res l₁ S.#[ n ]) (l∈ls , tⱽ) = l∈ls , trans-≤ tⱽ (newᴴ-≤ l∈Γ u M₁≤M₂ l∈ls)
update-validᵀ {τ = Res .l₁ Addr} l∈Γ u M₁≤M₂ (S.Res l₁ S.#[ n ]ᴰ) (l∈ls , tⱽ) = l∈ls , trans-≤ tⱽ (newᴴ-≤ l∈Γ u M₁≤M₂ l∈ls)
update-validᵀ {τ = Res .l₁ Addr} l∈Γ u M₁≤M₂ (S.Res l₁ (S.deepDup t)) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ {τ = Res .l₁ Addr} l∈Γ u M₁≤M₂ (S.Res l₁ S.∙) ()
update-validᵀ l∈Γ u M₁≤M₂ (S.label l⊑h t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ l∈Γ u M₁≤M₂ (S.label∙ l⊑h t) ()
update-validᵀ l∈Γ u M₁≤M₂ (S.unlabel l⊑h t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ l∈Γ u M₁≤M₂ (S.read x t) tⱽ =  update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ l∈Γ u M₁≤M₂ (S.write x t t₁) (tⱽ , t₁ⱽ) = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ ,  update-validᵀ l∈Γ u M₁≤M₂ t₁ t₁ⱽ
update-validᵀ l∈Γ u M₁≤M₂ (S.write∙ x t t₁) ()
update-validᵀ l∈Γ u M₁≤M₂ (S.new x t) tⱽ =  update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ l∈Γ u M₁≤M₂ (S.new∙ x t) ()
update-validᵀ l∈Γ u M₁≤M₂ S.#[ x ] tⱽ = tt
update-validᵀ l∈Γ u M₁≤M₂ S.#[ x ]ᴰ tⱽ = tt
update-validᵀ l∈Γ u M₁≤M₂ (S.fork l⊑h t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ l∈Γ u M₁≤M₂ (S.fork∙ l⊑h t) ()
update-validᵀ l∈Γ u M₁≤M₂ (S.deepDup t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ l∈Γ u M₁≤M₂ S.∙ ()

update-validᶜ : ∀ {l π l' ls τ₁ τ₂} {C : Cont l' τ₁ τ₂} {Γ Γ' : Heaps ls} {Δ : Env l π} {M₁ M₂ : Memory l} ->
                l ↦ ⟨ M₁ , Δ ⟩ ∈ᴴ Γ ->
                Γ' ≔ Γ [ l ↦ ⟨ M₂ , Δ ⟩ ]ᴴ -> (lengthᴹ M₁) Data.Nat.≤ (lengthᴹ M₂)
                -> validᶜ Γ C -> validᶜ Γ' C
update-validᶜ {C = S.Var τ∈π} l∈Γ u M₁≤M₂ Cⱽ = tt
update-validᶜ {C = S.# τ∈π} l∈Γ u M₁≤M₂ Cⱽ = tt
update-validᶜ {C = S.Then t₁ Else t₂} l∈Γ u M₁≤M₂ (proj₁ , proj₂) = (update-validᵀ l∈Γ u M₁≤M₂ t₁ proj₁) , (update-validᵀ l∈Γ u M₁≤M₂ t₂ proj₂)
update-validᶜ {C = S.Bind t} l∈Γ u M₁≤M₂ Cⱽ = update-validᵀ l∈Γ u M₁≤M₂ t Cⱽ
update-validᶜ {C = S.unlabel p} l∈Γ u M₁≤M₂ Cⱽ = tt
update-validᶜ {C = S.unId} l∈Γ u M₁≤M₂ Cⱽ = tt
update-validᶜ {C = S.write x τ∈π} l∈Γ u M₁≤M₂ Cⱽ = tt
update-validᶜ {C = S.write∙ x τ∈π} l∈Γ u M₁≤M₂ ()
update-validᶜ {C = S.read x} l∈Γ u M₁≤M₂ Cⱽ = tt

update-validˢ : ∀ {l π l' ls τ₁ τ₂} {S : Stack l' τ₁ τ₂} {Γ Γ' : Heaps ls} {Δ : Env l π} {M₁ M₂ : Memory l} ->
                  l ↦ ⟨ M₁ , Δ ⟩ ∈ᴴ Γ ->
                  Γ' ≔ Γ [ l ↦ ⟨ M₂ , Δ ⟩ ]ᴴ -> (lengthᴹ M₁) Data.Nat.≤ (lengthᴹ M₂)
                -> validˢ Γ S -> validˢ Γ' S
update-validˢ {S = S.[]} l∈Γ u M₁≤M₂ Sⱽ = tt
update-validˢ {S = C S.∷ S} l∈Γ u M₁≤M₂ (Cⱽ , Sⱽ) = update-validᶜ {C = C} l∈Γ u M₁≤M₂ Cⱽ , (update-validˢ l∈Γ u M₁≤M₂ Sⱽ)
update-validˢ {S = S.∙} l∈Γ u M₁≤M₂ ()


-- update-validᴱ : ∀ {l l' ls π π'} {Γ Γ' : Heaps ls} {Δ : Env l π} {Δ' : Env l' π'} {M₁ M₂ : Memory l'} -> l' ↦ ⟨ M₁ , Δ' ⟩ ∈ᴴ Γ ->
--                 Γ' ≔ Γ [ l' ↦ ⟨ M₂ , Δ' ⟩ ]ᴴ -> validᴱ Γ Δ -> validᴱ Γ' Δ
-- update-validᴱ {Δ = Δ} S.here S.here v = {!!}
-- update-validᴱ S.here (S.there u₁) v = {!!}
-- update-validᴱ (S.there l∈Γ) S.here v = {!!}
-- update-validᴱ (S.there l∈Γ) (S.there u₁) v = update-validᴱ l∈Γ u₁ v

-- update-validᴴ : ∀ {l π ls} {Γ Γ' : Heaps ls} {Δ : Env l π} {M₁ M₂ : Memory l} ->
--                   l ↦ ⟨ M₁ , Δ ⟩ ∈ᴴ Γ ->
--                   Γ' ≔ Γ [ l ↦ ⟨ M₂ , Δ ⟩ ]ᴴ -> (lengthᴹ M₁) Data.Nat.≤ (lengthᴹ M₂) ->
--                   validᴴ Γ -> validᴴ Γ' Γ'
-- update-validᴴ S.here u₁ M₁≤M₂ v = {!!}
-- update-validᴴ (S.there l∈Γ) S.here M₁≤M₂ v = ⊥-elim {!!}
-- update-validᴴ {Γ = S.⟨ x , x₁ ⟩ S.∷ Γ} (S.there l∈Γ) (S.there u) M₁≤M₂ ((proj₁ , proj₂) , proj₃)
--   = ((proj₁ , update-validᴱ l∈Γ u proj₂ )) , {!update-validᴴ l∈Γ u M₁≤M₂  ?!} -- {!!} , {!!}
-- update-validᴴ {Γ = S.∙ S.∷ Γ} (S.there l∈Γ) (S.there u₁) M₁≤M₂ (() , proj₂)

valid⟼ : ∀ {ls τ l} {p₁ p₂ : Program l ls τ} -> validᴾ p₁ -> p₁ ⟼ p₂ -> validᴾ p₂
valid⟼ ok (SS.Pure l∈Γ step uᴴ) = {!!}
valid⟼ (proj₁ , proj₃ , proj₂) (SS.New {M = M} {τ∈π = τ∈π} {l⊑h = l⊑h} H∈Γ uᴴ) with valid-memberᴴ proj₁ H∈Γ
... | Mⱽ , Δⱽ with valid-newᴹ ∥ l⊑h ,  τ∈π ∥ M Mⱽ
... | M'ⱽ , ok-Addr = {!!} , (((update-∈ uᴴ) , valid-new-Addr {M = M} Mⱽ ∥ l⊑h ,  τ∈π ∥ uᴴ) , update-validˢ H∈Γ uᴴ (newᴹ-≤ M ∥ l⊑h ,  τ∈π ∥) proj₂)
valid⟼ (proj₁ , () , proj₂) SS.New∙
valid⟼ ok (SS.Write₂ H∈Γ uᴹ uᴴ) = {!!}
valid⟼ ok (SS.Writeᴰ₂ H∈Γ uᴹ uᴴ) = {!!}
valid⟼ (proj₁ , proj₃ , () , proj₂) SS.Write∙₂
valid⟼ ok (SS.Read₂ l∈Γ n∈M) = {!!}
valid⟼ ok (SS.Readᴰ₂ L∈Γ n∈M) = {!!}
valid⟼ ok (SS.DeepDupˢ L⊏l L∈Γ t∈Δ) = {!!}
valid⟼ () SS.Hole
