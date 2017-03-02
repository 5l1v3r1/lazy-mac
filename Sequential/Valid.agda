import Lattice as L

module Sequential.Valid (𝓛 : L.Lattice) where

import Types as T hiding (wken-∈)
open T 𝓛

import Sequential.Calculus as S renaming (⟨_,_,_⟩ to mkP ; ⟨_,_⟩ to mkTS) -- hiding (wkenᴱ)
open S 𝓛

open import Data.Nat using (_≤_ ; _<_ ; s≤s ; z≤n ; decTotalOrder)
open import Data.Empty
--import Data.List as LL
open import Data.Product as P
open import Data.Maybe

-- open decTotalOrder ℕ renaming (trans to trans-≤)

-- A valid term contains only valid references, that contain a valid address.

validAddr : ∀ {l} -> Memory l -> ℕ -> Set
validAddr M n = n < lengthᴹ M -- TODO and M ≠ ∙ ?

data IsAddr {π} : Term π Addr -> ℕ -> Set where
  is#[_] : (n : ℕ) -> IsAddr #[ n ] n
  is#[_]ᴰ : (n : ℕ) -> IsAddr #[ n ]ᴰ n

validᵀ : ∀ {ls τ π} -> Memories ls -> Term π τ -> Set
validᵀ Ms S.（） = ⊤
validᵀ Ms S.True = ⊤
validᵀ Ms S.False = ⊤
validᵀ Ms (S.Id t) = validᵀ Ms t
validᵀ Ms (S.unId t) = validᵀ Ms t
validᵀ Ms (S.Var τ∈π) = ⊤
validᵀ Ms (S.Abs t) = validᵀ Ms t
validᵀ Ms (S.App t t₁) = validᵀ Ms t × validᵀ Ms t₁
validᵀ Ms (S.If t Then t₁ Else t₂) = (validᵀ Ms t) × (validᵀ Ms t₁) × validᵀ Ms t₂
validᵀ Ms (S.Return l t) = validᵀ Ms t
validᵀ Ms (t S.>>= t₁) = (validᵀ Ms t) × (validᵀ Ms t₁)
validᵀ Ms (S.Mac l t) = validᵀ Ms t
validᵀ {ls} {τ = Res .l Addr} Ms (S.Res l t) = Σ (l ∈ ls) (λ l∈ls -> ∃ (λ n -> IsAddr t n × validAddr (lookupˢ l∈ls Ms) n ))
validᵀ Ms (S.Res l t) = validᵀ Ms t
validᵀ Ms (S.label l⊑h t) = validᵀ Ms t
validᵀ Ms (S.label∙ l⊑h t) = ⊥
validᵀ Ms (S.unlabel l⊑h t) = validᵀ Ms t
validᵀ Ms (S.read x t) = validᵀ Ms t
validᵀ Ms (S.write x t t₁) = (validᵀ Ms t) × (validᵀ Ms t₁)
validᵀ Ms (S.write∙ x t t₁) = ⊥
validᵀ {π = π} Ms (S.new {h = H} x t) = ∃ (λ M → H ↦ M ∈ˢ Ms × validᵀ Ms t)
validᵀ Ms (S.new∙ x t) = ⊥
validᵀ Ms S.#[ x ] = ⊤
validᵀ Ms S.#[ x ]ᴰ = ⊤
validᵀ Ms (S.fork l⊑h t) = validᵀ Ms t
validᵀ Ms (S.fork∙ l⊑h t) = ⊥
validᵀ Ms (S.deepDup t) = validᵀ Ms t
validᵀ Ms S.∙ = ⊥

validᶜ : ∀ {l π ls τ₁ τ₂} -> Memories ls -> Cont l π τ₁ τ₂ -> Set
validᶜ Ms (S.Var τ∈π) = ⊤
validᶜ Ms (S.# τ∈π) = ⊤
validᶜ Ms (S.Then x Else x₁) = (validᵀ Ms x) × validᵀ Ms x₁
validᶜ Ms (S.Bind x) = validᵀ Ms x
validᶜ Ms (S.unlabel p) = ⊤
validᶜ Ms S.unId = ⊤
validᶜ Ms (S.write x τ∈π) = ⊤
validᶜ Ms (S.write∙ x τ∈π) = ⊥
validᶜ Ms (S.read x) = ⊤

validˢ : ∀ {l  π ls τ₁ τ₂} -> Memories ls -> Stack l π τ₁ τ₂ -> Set
validˢ Ms S.[] = ⊤
validˢ Ms (C S.∷ S) = validᶜ Ms C × validˢ Ms S
validˢ Ms S.∙ = ⊥

validᴹᵀ : ∀ {π τ ls} -> Memories ls -> Maybe (Term π τ) -> Set
validᴹᵀ Ms (just x) = validᵀ Ms x
validᴹᵀ Ms nothing = ⊤


validᴴ : ∀ {l π ls} -> Memories ls -> Heap l π -> Set
validᴴ Ms S.[] = ⊤
validᴴ Ms (mt S.∷ Δ) = validᴹᵀ Ms mt × validᴴ Ms Δ
validᴴ Ms S.∙ = ⊥

validᴹ : ∀ {l} -> (M : Memory l) -> Set
validᴹ S.[] = ⊤
validᴹ (cᴸ S.∷ M) = validᴹ M
validᴹ S.∙ = ⊥

validᴴ∙ : ∀ {l ls} (Ms : Memories ls) (H : Heap∙ l) -> Set
validᴴ∙ Ms S.⟨ Δ ⟩ = validᴴ Ms Δ
validᴴ∙ Ms S.∙ = ⊥

valid-state : ∀ {l ls τ} -> Memories ls -> State l τ -> Set
valid-state Ms (S.mkP Δ t S) = validᴴ Ms Δ × validᵀ Ms t × validˢ Ms S
valid-state _ S.∙ = ⊥

map-validᴹ : ∀ {ls} -> Memories ls -> Set
map-validᴹ S.[] = ⊤
map-validᴹ (M S.∷ Ms) = validᴹ M × map-validᴹ Ms

map-validᴴ : ∀ {ls₁ ls₂} -> Memories ls₁ -> Heaps ls₂ -> Set
map-validᴴ Ms S.[] = ⊤
map-validᴴ Ms (x S.∷ Γ) = validᴴ∙ Ms x × map-validᴴ Ms Γ

validTS∙ : ∀ {l τ ls} -> Memories ls -> TS∙ l τ -> Set
validTS∙ Ms (mkTS t S) = validᵀ Ms t × validˢ Ms S
validTS∙ _ S.∙ = ⊥

validᴾ : ∀ {l ls τ} -> Program l ls τ -> Set
validᴾ (S.mkP Ms Γ TS ) = map-validᴹ Ms × map-validᴴ Ms Γ × validTS∙ Ms TS

valid-𝓛 : (ls : List Label) -> Set
valid-𝓛 [] = ⊤
valid-𝓛 (l ∷ ls) = Unique l ls × valid-𝓛 ls

Ms₀ : {ls : List Label} {{us : valid-𝓛 ls}} -> Memories ls
Ms₀ {[]} {{_}} = []
Ms₀ {l ∷ ls} {{u , us}} = [] ∷ Ms₀

--------------------------------------------------------------------------------

open import Relation.Binary as B
open B.DecTotalOrder Data.Nat.decTotalOrder hiding (_≤_) renaming (trans to trans-≤ ; refl to refl-≤)


open import Function

-- -- TODO might need more assuptions in cons, such both are valid (in Rule Var₂)
-- data _⊆ᴱ_ {l} : ∀ {π₁ π₂} -> Heap l π₁ -> Heap l π₂ -> Set where
--   nil : [] ⊆ᴱ []
--   cons : ∀ {π τ} {mt₁ mt₂ : Maybe (Term π τ)} {Δ₁ Δ₂ : Heap l π} -> Δ₁ ⊆ᴱ Δ₂ -> (mt₁ ∷ Δ₁) ⊆ᴱ (mt₂ ∷ Δ₂)
--   drop : ∀ {π τ} {mt : Maybe (Term π τ)} {Δ₁ Δ₂ : Heap l π} -> Δ₁ ⊆ᴱ Δ₂ -> Δ₁ ⊆ᴱ (mt ∷ Δ₂ )
--   ∙ : ∀ {π} -> (∙ {{π}}) ⊆ᴱ (∙ {{π}})

-- data _⊆∙ᴴ_ {l} : Heap∙ l -> Heap∙ l -> Set where
--  ⟨_,_⟩  : ∀ {π₁ π₂} {M₁ M₂ : Memory l} {Δ₁ : Heap l π₁} {Δ₂ : Heap l π₂} -> Δ₁ ⊆ᴱ Δ₂ -> ⟨ Δ₁ ⟩ ⊆∙ᴴ ⟨ Δ₂ ⟩
--  ∙ : ∙ ⊆∙ᴴ ∙

-- data _⊆ᴹ_ : ∀ {ls₁ ls₂} -> Memories ls₁ -> Memories ls₂ -> Set where
--   nil : [] ⊆ᴹ []
--   cons : ∀ {ls₁ ls₂ l} {u₁ : Unique l ls₁} {u₂ : Unique l ls₂} {Γ₁ : Memories ls₁} {Γ₂ : Memories ls₂} {M₁ M₂ : Memory l}
--          -> M₁ ⊆∙ᴹ M₂ -> Ms₁ ⊆ᴹ Ms₂ -> (M₁ ∷ Ms₁) ⊆ᴹ (M₂ ∷ Ms₂)
--   drop : ∀ {ls₁ ls₂ l} {u₂ : Unique l ls₂} {Γ₁ : Memories ls₁} {Γ₂ : Memories ls₂} {H : Heap∙ l}
--            -> Γ₁ ⊆ᴹ Γ₂ -> Γ₁ ⊆ᴹ (H ∷ Γ₂)

-- refl-⊆ᴱ : ∀ {π l} {Δ : Heap l π} -> Δ ⊆ᴱ Δ
-- refl-⊆ᴱ {Δ = S.[]} = nil
-- refl-⊆ᴱ {Δ = t S.∷ Δ} = cons refl-⊆ᴱ
-- refl-⊆ᴱ {Δ = S.∙} = ∙

-- refl-⊆'ᴴ : ∀ {l} {H : Heap∙ l} -> H ⊆∙ᴴ H
-- refl-⊆'ᴴ {H = S.⟨ x₁ ⟩} = ? --  ⟨ refl-≤ , refl-⊆ᴱ ⟩
-- refl-⊆'ᴴ {H = S.∙} = ∙

-- refl-⊆ᴴ : ∀ {ls} {Γ : Heaps ls} -> Γ ⊆ᴴ Γ
-- refl-⊆ᴴ {Γ = S.[]} = nil
-- refl-⊆ᴴ {Γ = x S.∷ Γ} = cons refl-⊆'ᴴ refl-⊆ᴴ

open import Function

-- wken-Addr : ∀ {ls₁ ls₂ l} {M₁ : Memories ls₁} {M₂ : Memories ls₂} {n : ℕ} ->
--               M₁ ⊆ᴴ M₂ -> Σ (l ∈ ls₁) (λ l∈ls₁ -> validAddr (lookupˢ l∈ls₁ M₁) n) -> Σ (l ∈ ls₂) (λ l∈ls₂ -> validAddr (lookupˢ l∈ls₂ M₂) n)
-- wken-Addr nil (() , proj₂)
-- wken-Addr (cons ⟨ x₁ ⟩ Γ₁⊆Γ₂) (T.here , proj₂) = ? -- here , trans-≤ proj₂ x
-- wken-Addr (cons ∙ Γ₁⊆Γ₂) (T.here , proj₂) = here , proj₂
-- wken-Addr (cons x Γ₁⊆Γ₂) (T.there proj₁ , proj₂) = P.map there id (wken-Addr Γ₁⊆Γ₂ (proj₁ , proj₂))
-- wken-Addr (drop Γ₁⊆Γ₂) (proj₁ , proj₂) = P.map there id (wken-Addr Γ₁⊆Γ₂ (proj₁ , proj₂))

-- wken-∈ : ∀ {l ls₁ ls₂} {Γ₁ : Heaps ls₁} {Γ₂ : Heaps ls₂}-> l ∈ ls₁ -> Γ₁ ⊆ᴴ Γ₂ -> l ∈ ls₂
-- wken-∈ T.here (cons x Γ₁⊆Γ₂) = here
-- wken-∈ T.here (drop Γ₁⊆Γ₂) = there (wken-∈ here Γ₁⊆Γ₂)
-- wken-∈ (T.there l∈ls) (cons x Γ₁⊆Γ₂) = there (wken-∈ l∈ls Γ₁⊆Γ₂)
-- wken-∈ (T.there l∈ls) (drop Γ₁⊆Γ₂) = there (wken-∈ (there l∈ls) Γ₁⊆Γ₂)

-- wkenᵁ : ∀ {l ls₁ ls₂} {Γ₁ : Heaps ls₁} {Γ₂ : Heaps ls₂} {H₁ : Heap l}
--       -> l ↦ H₁ ∈ᴴ Γ₁ -> Γ₁ ⊆ᴴ Γ₂ -> Σ (Heap l) (λ H₂ -> H₁ ⊆∙ᴴ H₂ × l ↦ H₂ ∈ᴴ Γ₂)
-- wkenᵁ S.here (cons x Γ₁⊆Γ₂) = _ , (x , here)
-- wkenᵁ S.here (drop Γ₁⊆Γ₂) = P.map id (P.map id there) (wkenᵁ here Γ₁⊆Γ₂)
-- wkenᵁ (S.there x) (cons x₁ Γ₁⊆Γ₂) = P.map id (P.map id there) (wkenᵁ x Γ₁⊆Γ₂)
-- wkenᵁ (S.there x) (drop Γ₁⊆Γ₂) = P.map id (P.map id there) (wkenᵁ (there x) Γ₁⊆Γ₂)

-- wkenᵀ : ∀ {π τ ls₁ ls₂} {Γ₁ : Heaps ls₁} {Γ₂ : Heaps ls₂} -> Γ₁ ⊆ᴴ Γ₂ -> (t : Term π τ) -> validᵀ Γ₁ t -> validᵀ Γ₂ t
-- wkenᵀ Γ₁⊆Γ₂ S.（） ok = T.tt
-- wkenᵀ Γ₁⊆Γ₂ S.True ok = T.tt
-- wkenᵀ Γ₁⊆Γ₂ S.False ok = T.tt
-- wkenᵀ Γ₁⊆Γ₂ (S.Id t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
-- wkenᵀ Γ₁⊆Γ₂ (S.unId t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
-- wkenᵀ Γ₁⊆Γ₂ (S.Var τ∈π) ok = T.tt
-- wkenᵀ Γ₁⊆Γ₂ (S.Abs t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
-- wkenᵀ Γ₁⊆Γ₂ (S.App t t₁) (proj₁ , proj₂) = (wkenᵀ Γ₁⊆Γ₂ t proj₁) , (wkenᵀ Γ₁⊆Γ₂ t₁ proj₂)
-- wkenᵀ Γ₁⊆Γ₂ (S.If t Then t₁ Else t₂) (proj₁ , proj₂ , proj₃) = (wkenᵀ Γ₁⊆Γ₂ t proj₁) , ((wkenᵀ Γ₁⊆Γ₂ t₁ proj₂) , (wkenᵀ Γ₁⊆Γ₂ t₂ proj₃))
-- wkenᵀ Γ₁⊆Γ₂ (S.Return l₁ t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
-- wkenᵀ Γ₁⊆Γ₂ (t S.>>= t₁) (proj₁ , proj₂) = (wkenᵀ Γ₁⊆Γ₂ t proj₁) , (wkenᵀ Γ₁⊆Γ₂ t₁ proj₂)
-- wkenᵀ Γ₁⊆Γ₂ (S.Mac l₁ t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
-- wkenᵀ {τ = T.Res .l₁ T.（）} Γ₁⊆Γ₂ (S.Res l₁ t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
-- wkenᵀ {τ = T.Res .l₁ T.Bool} Γ₁⊆Γ₂ (S.Res l₁ t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
-- wkenᵀ {τ = T.Res .l₁ (τ T.=> τ₁)} Γ₁⊆Γ₂ (S.Res l₁ t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
-- wkenᵀ {τ = T.Res .l₂ (T.Mac l₁ τ)} Γ₁⊆Γ₂ (S.Res l₂ t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
-- wkenᵀ {τ = T.Res .l₂ (T.Res l₁ τ)} Γ₁⊆Γ₂ (S.Res l₂ t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
-- wkenᵀ {τ = T.Res .l₁ (T.Id τ)} Γ₁⊆Γ₂ (S.Res l₁ t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
-- wkenᵀ {τ = T.Res .l₁ T.Addr} Γ₁⊆Γ₂ (S.Res l₁ (S.unId t)) ok = wkenᵀ Γ₁⊆Γ₂ t ok
-- wkenᵀ {τ = T.Res .l₁ T.Addr} Γ₁⊆Γ₂ (S.Res l₁ (S.Var τ∈π)) ok = tt
-- wkenᵀ {τ = T.Res .l₁ T.Addr} Γ₁⊆Γ₂ (S.Res l₁ (S.App t t₁))  (proj₁ , proj₂) = (wkenᵀ Γ₁⊆Γ₂ t proj₁) , (wkenᵀ Γ₁⊆Γ₂ t₁ proj₂)
-- wkenᵀ {τ = T.Res .l₁ T.Addr} Γ₁⊆Γ₂ (S.Res l₁ (S.If t Then t₁ Else t₂))
--   (proj₁ , proj₂ , proj₃) = (wkenᵀ Γ₁⊆Γ₂ t proj₁) , ((wkenᵀ Γ₁⊆Γ₂ t₁ proj₂) , (wkenᵀ Γ₁⊆Γ₂ t₂ proj₃))
-- wkenᵀ {τ = T.Res .l₁ T.Addr} Γ₁⊆Γ₂ (S.Res l₁ S.#[ x ]) v = wken-Addr Γ₁⊆Γ₂ v
-- wkenᵀ {τ = T.Res .l₁ T.Addr} Γ₁⊆Γ₂ (S.Res l₁ S.#[ x ]ᴰ) v = wken-Addr Γ₁⊆Γ₂ v
-- wkenᵀ {τ = T.Res .l₁ T.Addr} Γ₁⊆Γ₂ (S.Res l₁ (S.deepDup t)) ok = wkenᵀ Γ₁⊆Γ₂ t ok
-- wkenᵀ {τ = T.Res .l₁ T.Addr} Γ₁⊆Γ₂ (S.Res l₁ S.∙) ()
-- wkenᵀ Γ₁⊆Γ₂ (S.label l⊑h t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
-- wkenᵀ Γ₁⊆Γ₂ (S.label∙ l⊑h t) ()
-- wkenᵀ Γ₁⊆Γ₂ (S.unlabel l⊑h t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
-- wkenᵀ Γ₁⊆Γ₂ (S.read x t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
-- wkenᵀ Γ₁⊆Γ₂ (S.write x t t₁) (proj₁ , proj₂) = (wkenᵀ Γ₁⊆Γ₂ t proj₁) , (wkenᵀ Γ₁⊆Γ₂ t₁ proj₂)
-- wkenᵀ Γ₁⊆Γ₂ (S.write∙ x t t₁) ()
-- wkenᵀ Γ₁⊆Γ₂ (S.new x t) (ok₁ , ok₂ , ok₃) = ?
-- -- with wkenᵁ ok₂ Γ₁⊆Γ₂
-- -- wkenᵀ Γ₁⊆Γ₂ (S.new x₂ t) (ok₁ , ok₂ , ok₃) | ⟨ M' , Δ' ⟩ , ⟨ x , x₁ ⟩ , H∈Γ = (M' , {!Δ'!}) , ( {!H∈Γ!} , wkenᵀ Γ₁⊆Γ₂ t ok₃)
-- wkenᵀ Γ₁⊆Γ₂ (S.new∙ x t) ()
-- wkenᵀ Γ₁⊆Γ₂ S.#[ x ] ok = T.tt
-- wkenᵀ Γ₁⊆Γ₂ S.#[ x ]ᴰ ok = T.tt
-- wkenᵀ Γ₁⊆Γ₂ (S.fork l⊑h t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
-- wkenᵀ Γ₁⊆Γ₂ (S.fork∙ l⊑h t) ()
-- wkenᵀ Γ₁⊆Γ₂ (S.deepDup t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
-- wkenᵀ Γ₁⊆Γ₂ S.∙ ()

-- wkenᴱ : ∀ {l π ls₁ ls₂} {Δ : Heap l π} {Γ₁ : Heaps ls₁} {Γ₂ : Heaps ls₂} -> Γ₁ ⊆ᴴ Γ₂ -> validᴴ Γ₁ Δ -> validᴴ Γ₂ Δ
-- wkenᴱ {Δ = S.[]} Γ₁⊆Γ₂ Δᴱ = tt
-- wkenᴱ {Δ = just t S.∷ Δ} Γ₁⊆Γ₂  (tⱽ , Δᴱ) = wkenᵀ Γ₁⊆Γ₂ t tⱽ , wkenᴱ {Δ = Δ} Γ₁⊆Γ₂ Δᴱ
-- wkenᴱ {Δ = nothing S.∷ Δ} Γ₁⊆Γ₂  Δᴱ = wkenᴱ {Δ = Δ} Γ₁⊆Γ₂  Δᴱ
-- wkenᴱ {Δ = S.∙} _ ()

-- -- wkenᴹ : ∀ {l} {M₁ M₂ : Memory l} -> lengthᴹ M₁ ≤ lengthᴹ M₂ -> validᴹ M₁ -> validᴹ M₂
-- -- wkenᴹ {M₂ = S.[]} x x₁ = tt
-- -- wkenᴹ {M₂ = cᴸ S.∷ M₂} x x₁ = {!!}
-- -- wkenᴹ {M₁ = S.[]} {S.∙} z≤n x₁ = {!!}  -- No! :-(
-- -- wkenᴹ {M₁ = cᴸ S.∷ M₁} {S.∙} () x₁
-- -- wkenᴹ {M₁ = S.∙} {S.∙} z≤n ()

-- wkenᴴ₂ : ∀ {l ls₁ ls₂} {Γ₁ : Heaps ls₁} {Γ₂ : Heaps ls₂} {H : Heap∙ l} -> Γ₁ ⊆ᴴ Γ₂ -> validᴴ₂ Γ₁ H -> validᴴ₂ Γ₂ H
-- wkenᴴ₂ {H = S.⟨ Δ ⟩} Γ₁⊆Γ₂ (a , b) = a , wkenᴱ {Δ = Δ} Γ₁⊆Γ₂ b
-- wkenᴴ₂ {H = S.∙} _ ()

-- wkenᴴ₂' : ∀ {l ls₁ ls₂} {Γ₁ : Heaps ls₁} {Γ₂ : Heaps ls₂} {H₁ H₂ : Heap l} -> Γ₁ ⊆ᴴ Γ₂ -> H₁ ⊆'ᴴ H₂ -> validᴴ₂ Γ₁ H₁ -> validᴴ₂ Γ₂ H₂
-- wkenᴴ₂' a ⟨ x , x₁ ⟩ (proj₁ , proj₂) = {!!} , {!!}
-- wkenᴴ₂' a ∙ ()
-- {H = S.⟨ M , Δ ⟩} Γ₁⊆Γ₂ (a , b) = a , wkenᴱ {Δ = Δ} Γ₁⊆Γ₂ b
-- wkenᴴ₂' {H = S.∙} _ ()

-- wkenᴴ : ∀ {ls₁ ls₂} {Γ₁ : Heaps ls₁} {Γ₂ : Heaps ls₂} -> Γ₁ ⊆ᴴ Γ₂ -> validᴴ Γ₁ -> validᴴ Γ₂
-- wkenᴴ nil x = tt
-- wkenᴴ (cons x x₁) (proj₁ , proj₂) = (wkenᴴ₂' (cons x x₁) x proj₁) , wkenᴴ x₁ proj₂
-- wkenᴴ {Γ₁ = Γ₁} (drop x) x₁ = {!!} , (wkenᴴ x x₁)

-- validᴴ₀ : ∀ {ls : List Label} {{us : valid-𝓛 ls}} -> validᴴ {ls} Γ₀
-- validᴴ₀ {T.[]} = tt
-- validᴴ₀ {x T.∷ ls} = (tt , tt) , validᴴ₀

-- S₀ : ∀ {l τ} -> Stack l τ τ
-- S₀ = []

-- validˢ₀ : ∀ {l τ ls} -> (Γ : Heaps ls) -> validˢ Γ (S₀ {l} {τ})
-- validˢ₀ Γ = tt

-- P₀ : ∀ {ls l τ π} {{us : valid-𝓛 ls}} -> Term π τ -> Program l ls τ
-- P₀ {{us = us}} t = mkP Γ₀ t S₀

-- -- Initial configurations are valid given a valid initial term,
-- -- i.e. it does not have no free variables and references.
-- validᴾ₀ : ∀ {τ l ls} {t : Term [] τ} {{us : valid-𝓛 ls}} -> validᵀ (Γ₀ {{us}}) t -> validᴾ (P₀ {l = l} {{us}} t)
-- validᴾ₀ vᵀ = validᴴ₀ , vᵀ , tt

--------------------------------------------------------------------------------

import Sequential.Semantics as SS
open SS 𝓛

open import Relation.Binary.PropositionalEquality

-- valid-memberᴴ : ∀ {l ls} {Γ : Heaps ls} {H : Heap l} -> validᴴ Γ -> l ↦ H ∈ᴴ Γ -> validᴴ₂ Γ H
-- valid-memberᴴ (proj₁ , proj₂) S.here = proj₁
-- valid-memberᴴ (proj₁ , proj₂) (S.there l∈Γ) = wkenᴴ₂ (drop refl-⊆ᴴ) (valid-memberᴴ proj₂ l∈Γ)

-- valid-memberᴱ : ∀ {l τ π₁ π₂ ls} {Ms : Memories ls} {Δ : Heap l π₁} {t : Term π₂ τ} {x : τ ∈⟨ l ⟩ᴿ π₁} -> validᴴ Ms Δ -> x ↦ t ∈ᴴ Δ -> validᵀ Ms t
-- valid-memberᴱ {x = T.⟪ τ∈π ⟫} = {!!} -- aux
--   -- where aux : ∀ {l τ π₁ π₂ ls} {Ms : Memories ls} {Δ : Heap l π₁} {t : Term π₂ τ} {x : τ ∈⟨ l ⟩ π₁} -> validᴴ Ms Δ -> Memberᴴ (just t) x Δ -> validᵀ Ms t
--   --       aux (proj₁ , proj₂) S.here = proj₁
--   --       aux {Δ = just x S.∷ Δ} (_ , Δⱽ) (S.there t∈Δ) = aux Δⱽ t∈Δ
--   --       aux {Δ = nothing S.∷ Δ} Δⱽ (S.there t∈Δ) = aux Δⱽ t∈Δ

-- valid-newᴹ : ∀ {l τ} (c : Cell l τ) (M : Memory l) -> validᴹ M -> validᴹ (newᴹ c M) × (lengthᴹ M ≤ lengthᴹ (newᴹ c M))
-- valid-newᴹ c S.[] ok-M = tt , z≤n
-- valid-newᴹ c (cᴸ S.∷ M) ok-M = P.map id s≤s (valid-newᴹ c M ok-M)
-- valid-newᴹ c S.∙ ()

-- valid-writeᴹ : ∀ {l τ} {c : Cell l τ} {M M' : Memory l} {n} -> M' ≔ M [ n ↦ c ]ᴹ -> validᴹ M -> validᴹ M' × lengthᴹ M ≤ lengthᴹ M'
-- valid-writeᴹ {M = _ ∷ M} S.here Mⱽ = Mⱽ , s≤s refl-≤
-- valid-writeᴹ (S.there u) Mⱽ = P.map id s≤s (valid-writeᴹ u Mⱽ)

-- valid-new-Addr : ∀ {l ls τ} {Ms Ms' : Memories ls} {M : Memory l} -> validᴹ M -> (c : Cell l τ) ->
--               (uˢ : Ms' ≔ Ms [ l ↦ newᴹ c M ]ˢ) -> validAddr (lookupˢ (updateˢ-∈ uˢ) Ms') (lengthᴹ M)
-- valid-new-Addr {M = M} Mᵛ c (S.there uᴴ) = valid-new-Addr {M = M} Mᵛ c uᴴ
-- valid-new-Addr {M = M} Mᵛ c S.here = aux {c = c} {M = M} Mᵛ
--  where aux : ∀ {l τ} {c : Cell l τ} {M : Memory l} -> validᴹ M -> lengthᴹ M < lengthᴹ (newᴹ c M)
--        aux {M = S.[]} M≠∙ = s≤s z≤n
--        aux {M = cᴸ S.∷ M} M≠∙ = s≤s (aux {M = M} M≠∙)
--        aux {M = S.∙} ()


-- update-valid-Addr : ∀ {l} {M₁ M₂ : Memory l} {n : ℕ} -> validAddr M₁ n ->
--                     validᴹ M₁ -> validᴹ M₂ -> lengthᴹ M₁ ≤ lengthᴹ M₂ -> validAddr M₂ n
-- update-valid-Addr {_} {M₁} {M₂} aⱽ Mⱽ₁ Mⱽ₂ M₁≤M₂ = trans-≤ aⱽ M₁≤M₂

-- newᴹ-≤ : ∀ {l τ} (M : Memory l) (c : Cell l τ) -> lengthᴹ M ≤ lengthᴹ (newᴹ c M)
-- newᴹ-≤ S.[] c = z≤n
-- newᴹ-≤ (cᴸ S.∷ M) c = s≤s (newᴹ-≤ M c)
-- newᴹ-≤ S.∙ c = refl-≤

-- -- newᴴ-≤ : ∀ {l ls} {M₁ M₂ : Heaps ls} {M₁ M₂ : Memory l} {Δ : Heap l π} -> l ↦ ⟨ Δ ⟩ ∈ᴱ Γ₁ -> Γ₂ ≔ Γ₁ [ l ↦ ⟨ Δ ⟩ ]ᴱ ->
-- --            (lengthᴹ M₁) ≤ (lengthᴹ M₂) ->
-- --           (∀ {l} -> (l∈ls : l ∈ ls) ->
-- --              lengthᴹ (lookupˢ l∈ls Γ₁) ≤ lengthᴹ (lookupˢ l∈ls Γ₂))
-- -- newᴴ-≤ = ?
-- -- S.here S.here M₁≤M₂ T.here = M₁≤M₂
-- -- newᴴ-≤ S.here S.here _ (T.there l∈ls) = refl-≤
-- -- newᴴ-≤ {l} S.here (S.there {u = u} y) = ⊥-elim (∈-not-unique (updateᴱ-∈ y) u)
-- -- newᴴ-≤ (S.there {u = u} x) S.here = ⊥-elim (∈-not-unique (memberᴱ-∈ x) u)
-- -- newᴴ-≤ {Γ₁ = S.⟨ x , x₁ ⟩ S.∷ Γ₁} (S.there x₂) (S.there y) _ T.here = refl-≤
-- -- newᴴ-≤ {Γ₁ = S.∙ S.∷ Γ₁} (S.there x) (S.there y) _ T.here = refl-≤
-- -- newᴴ-≤ (S.there x) (S.there y) M₁≤M₂ (T.there z) = newᴴ-≤ x y M₁≤M₂ z

-- update-validᵀ : ∀ {l π  τ ls} {Ms₁ Ms₂ : Memories ls} {M₁ M₂ : Memory l} ->
--                 l ↦ M₁ ∈ˢ Ms₁ ->
--                 Ms₂ ≔ Ms₁ [ l ↦ M₁ ]ˢ -> (lengthᴹ M₁) ≤ (lengthᴹ M₂) -> (t : Term π τ) -> validᵀ Ms₁ t -> validᵀ Ms₂ t
-- update-validᵀ l∈Γ u M₁≤M₂ S.（） tⱽ = tt
-- update-validᵀ l∈Γ u M₁≤M₂ S.True tⱽ = tt
-- update-validᵀ l∈Γ u M₁≤M₂ S.False tⱽ = tt
-- update-validᵀ l∈Γ u M₁≤M₂ (S.Id t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
-- update-validᵀ l∈Γ u M₁≤M₂ (S.unId t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
-- update-validᵀ l∈Γ u M₁≤M₂ (S.Var τ∈π) tⱽ = tt
-- update-validᵀ l∈Γ u M₁≤M₂ (S.Abs t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
-- update-validᵀ l∈Γ u M₁≤M₂ (S.App t t₁) (tⱽ , t₁ⱽ) = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ , update-validᵀ l∈Γ u M₁≤M₂ t₁ t₁ⱽ
-- update-validᵀ l∈Γ u M₁≤M₂ (S.If t Then t₁ Else t₂) (tⱽ , t₁ⱽ , t₂ⱽ)
--   = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ , update-validᵀ l∈Γ u M₁≤M₂ t₁ t₁ⱽ , update-validᵀ l∈Γ u M₁≤M₂ t₂ t₂ⱽ
-- update-validᵀ l∈Γ u M₁≤M₂ (S.Return l₁ t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
-- update-validᵀ l∈Γ u M₁≤M₂ (t S.>>= t₁) (tⱽ , t₁ⱽ) = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ , update-validᵀ l∈Γ u M₁≤M₂ t₁ t₁ⱽ
-- update-validᵀ l∈Γ u M₁≤M₂ (S.Mac l₁ t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
-- update-validᵀ {τ = Res .l₁ （）} l∈Γ u M₁≤M₂ (S.Res l₁ t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
-- update-validᵀ {τ = Res .l₁ Bool} l∈Γ u M₁≤M₂ (S.Res l₁ t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
-- update-validᵀ {τ = Res .l₁ (τ => τ₁)} l∈Γ u M₁≤M₂ (S.Res l₁ t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
-- update-validᵀ {τ = Res .l₂ (Mac l₁ τ)} l∈Γ u M₁≤M₂ (S.Res l₂ t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
-- update-validᵀ {τ = Res .l₂ (Res l₁ τ)} l∈Γ u M₁≤M₂ (S.Res l₂ t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
-- update-validᵀ {τ = Res .l₁ (Id τ)} l∈Γ u M₁≤M₂ (S.Res l₁ t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
-- update-validᵀ {τ = Res .l₁ Addr} l∈Γ u M₁≤M₂ (S.Res l₁ (S.unId t)) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
-- update-validᵀ {τ = Res .l₁ Addr} l∈Γ u M₁≤M₂ (S.Res l₁ (S.Var τ∈π)) tⱽ = tt
-- update-validᵀ {τ = Res .l₁ Addr} l∈Γ u M₁≤M₂ (S.Res l₁ (S.App t t₁)) (tⱽ , t₁ⱽ) = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ , update-validᵀ l∈Γ u M₁≤M₂ t₁ t₁ⱽ
-- update-validᵀ {τ = Res .l₁ Addr} l∈Γ u M₁≤M₂ (S.Res l₁ (S.If t Then t₁ Else t₂)) (tⱽ , t₁ⱽ , t₂ⱽ)
--   = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ , update-validᵀ l∈Γ u M₁≤M₂ t₁ t₁ⱽ , update-validᵀ l∈Γ u M₁≤M₂ t₂ t₂ⱽ
-- update-validᵀ {τ = Res .l₁ Addr} l∈Γ u M₁≤M₂ (S.Res l₁ S.#[ n ]) (l∈ls , tⱽ) = l∈ls , trans-≤ tⱽ {!!} -- (newᴴ-≤ l∈Γ u M₁≤M₂ l∈ls)
-- update-validᵀ {τ = Res .l₁ Addr} l∈Γ u M₁≤M₂ (S.Res l₁ S.#[ n ]ᴰ) (l∈ls , tⱽ) = l∈ls , trans-≤ tⱽ {!!} -- (newᴴ-≤ l∈Γ u M₁≤M₂ l∈ls)
-- update-validᵀ {τ = Res .l₁ Addr} l∈Γ u M₁≤M₂ (S.Res l₁ (S.deepDup t)) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
-- update-validᵀ {τ = Res .l₁ Addr} l∈Γ u M₁≤M₂ (S.Res l₁ S.∙) ()
-- update-validᵀ l∈Γ u M₁≤M₂ (S.label l⊑h t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
-- update-validᵀ l∈Γ u M₁≤M₂ (S.label∙ l⊑h t) ()
-- update-validᵀ l∈Γ u M₁≤M₂ (S.unlabel l⊑h t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
-- update-validᵀ l∈Γ u M₁≤M₂ (S.read x t) tⱽ =  update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
-- update-validᵀ l∈Γ u M₁≤M₂ (S.write x t t₁) (tⱽ , t₁ⱽ) = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ ,  update-validᵀ l∈Γ u M₁≤M₂ t₁ t₁ⱽ
-- update-validᵀ l∈Γ u M₁≤M₂ (S.write∙ x t t₁) ()
-- update-validᵀ l∈Γ u M₁≤M₂ (S.new x t) ok = {!!} -- (ok , tⱽ) = {!!} -- ok , update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
-- update-validᵀ l∈Γ u M₁≤M₂ (S.new∙ x t) ()
-- update-validᵀ l∈Γ u M₁≤M₂ S.#[ x ] tⱽ = tt
-- update-validᵀ l∈Γ u M₁≤M₂ S.#[ x ]ᴰ tⱽ = tt
-- update-validᵀ l∈Γ u M₁≤M₂ (S.fork l⊑h t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
-- update-validᵀ l∈Γ u M₁≤M₂ (S.fork∙ l⊑h t) ()
-- update-validᵀ l∈Γ u M₁≤M₂ (S.deepDup t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
-- update-validᵀ l∈Γ u M₁≤M₂ S.∙ ()

-- update-validᶜ : ∀ {l π l' ls τ₁ τ₂} {C : Cont l' π τ₁ τ₂} {Ms₁ Ms₂ : Memories ls} {M₁ M₂ : Memory l} ->
--                 l ↦ M₁ ∈ˢ Ms₁ ->
--                 Ms₂ ≔ Ms₁ [ l ↦ M₂ ]ˢ -> (lengthᴹ M₁) ≤ (lengthᴹ M₂)
--                 -> validᶜ Ms₁ C -> validᶜ Ms₂ C
-- update-validᶜ {C = S.Var τ∈π} l∈Γ u M₁≤M₂ Cⱽ = tt
-- update-validᶜ {C = S.# τ∈π} l∈Γ u M₁≤M₂ Cⱽ = tt
-- update-validᶜ {C = S.Then t₁ Else t₂} l∈Γ u M₁≤M₂ (proj₁ , proj₂) = {!!} -- (update-validᵀ l∈Γ u M₁≤M₂ t₁ proj₁) , (update-validᵀ l∈Γ u M₁≤M₂ t₂ proj₂)
-- update-validᶜ {C = S.Bind t} l∈Γ u M₁≤M₂ Cⱽ = {!!} -- update-validᵀ l∈Γ u M₁≤M₂ t Cⱽ
-- update-validᶜ {C = S.unlabel p} l∈Γ u M₁≤M₂ Cⱽ = tt
-- update-validᶜ {C = S.unId} l∈Γ u M₁≤M₂ Cⱽ = tt
-- update-validᶜ {C = S.write x τ∈π} l∈Γ u M₁≤M₂ Cⱽ = tt
-- update-validᶜ {C = S.write∙ x τ∈π} l∈Γ u M₁≤M₂ ()
-- update-validᶜ {C = S.read x} l∈Γ u M₁≤M₂ Cⱽ = tt

-- update-validˢ : ∀ {l π l' ls τ₁ τ₂} {S : Stack l' π τ₁ τ₂} {Ms Ms' : Memories ls} {M₁ M₂ : Memory l} ->
--                   l ↦ M₁ ∈ˢ Ms ->
--                   Ms' ≔ Ms [ l ↦ M₂ ]ˢ -> (lengthᴹ M₁) ≤ (lengthᴹ M₂)
--                 -> validˢ Ms S -> validˢ Ms' S
-- update-validˢ {S = S.[]} l∈Γ u M₁≤M₂ Sⱽ = tt
-- update-validˢ {S = C S.∷ S} l∈Γ u M₁≤M₂ (Cⱽ , Sⱽ) = update-validᶜ {C = C} l∈Γ u M₁≤M₂ Cⱽ , (update-validˢ l∈Γ u M₁≤M₂ Sⱽ)
-- update-validˢ {S = S.∙} l∈Γ u M₁≤M₂ ()

-- -- update-⊆ᴴ : ∀ {l π ls} {Γ Γ' : Heaps ls} {Δ : Heap l π} {M₁ M₂ : Memory l} ->
-- --               l ↦ ⟨ Δ ⟩ ∈ᴴ Γ ->
-- --                 Γ' ≔ Γ [ l ↦ ⟨ Δ ⟩ ]ᴴ ->
-- --                 (lengthᴹ M₁) ≤ (lengthᴹ M₂) ->
-- --                 Γ ⊆ᴴ Γ'
-- -- update-⊆ᴴ S.here S.here M₁≤M₂ = ?
-- -- cons (⟨ M₁≤M₂ , refl-⊆ᴱ ⟩) refl-⊆ᴴ
-- -- update-⊆ᴴ S.here (S.there {u = u} uᴴ) M₁≤M₂ = ⊥-elim (∈-not-unique (update-∈ uᴴ) u)
-- -- update-⊆ᴴ (S.there {u = u} l∈Δ) S.here M₁≤M₂ = ⊥-elim (∈-not-unique (member-∈ l∈Δ) u)
-- -- update-⊆ᴴ (S.there l∈Δ) (S.there u₁) M₁≤M₂ = cons refl-⊆'ᴴ (update-⊆ᴴ l∈Δ u₁ M₁≤M₂)

-- -- update-validᴴ : ∀ {l π ls} {Γ Γ' : Heaps ls} {Δ : Heap l π} {M₁ M₂ : Memory l} ->
-- --                   l ↦ ⟨ Δ ⟩ ∈ᴴ Γ ->
-- --                   Γ' ≔ Γ [ l ↦ ⟨ Δ ⟩ ]ᴴ ->
-- --                   (lengthᴹ M₁) ≤ (lengthᴹ M₂) ->
-- --                   validᴹ M₂ ->
-- --                   validᴴ Γ -> validᴴ Γ'
-- -- update-validᴴ = ?
-- -- {Γ = _ ∷ Γ} {Δ = Δ} {M₁} {M₂} = ?
-- -- S.here S.here M₁≤M₂ M₂ⱽ ((proj₁ , proj₂) , proj₃)
-- --   = (M₂ⱽ , wkenᴱ {Δ = Δ} (cons (⟨ M₁≤M₂ , refl-⊆ᴱ ⟩) refl-⊆ᴴ) proj₂ ) , proj₃
-- -- update-validᴴ {Γ = S._∷_ {{u}} _ _} S.here (S.there b) M₁≤M₂ M₂ⱽ Γⱽ = ⊥-elim (∈-not-unique (update-∈ b) u)
-- -- update-validᴴ {Γ = S._∷_ {{u}} _ _} (S.there a) S.here M₁≤M₂ M₂ⱽ Γⱽ = ⊥-elim (∈-not-unique (member-∈ a) u)
-- -- update-validᴴ {Γ = S.⟨ M' , Δ' ⟩ S.∷ Γ} (S.there a) (S.there b) M₁≤M₂ M₂ⱽ ((proj₁ , proj₂) , proj₃)
-- --   = (proj₁ , wkenᴱ {Δ = Δ'} (update-⊆ᴴ (there a) (there b) M₁≤M₂) proj₂) , (update-validᴴ a b M₁≤M₂ M₂ⱽ proj₃)
-- -- update-validᴴ {Γ = S.∙ S.∷ Γ} (S.there a) (S.there b) M₁≤M₂ M₂ⱽ (() , proj₂)



-- -- This does not go because I need to restrict Γ to get to the memory where the update occurs
-- -- which may make some references invalid.
-- -- update-valid'ᴴ : ∀ {l π₁ π₂ ls ls'} {Γ Γ' : Heaps ls} {Γ'' : Heaps ls'} {Δ₁ : Heap l π₁} {Δ₂ : Heap l π₂} {M : Memory l} ->
-- --                   l ↦ ⟨ M , Δ₁ ⟩ ∈ᴴ Γ ->
-- --                   Γ' ≔ Γ [ l ↦ ⟨ M , Δ₂ ⟩ ]ᴴ ->
-- --                   validᴴ Γ -> Γ ⊆ᴴ Γ'' -> validᴴ Γ'' Δ₂ -> validᴴ Γ'
-- -- update-valid'ᴴ S.here S.here Γⱽ Γ⊆ᴴΓ'' Δ₂ⱽ = {!!}
-- -- update-valid'ᴴ S.here (S.there {u = u} uᴴ) Γⱽ _ Δ₂ⱽ = ⊥-elim (∈-not-unique (update-∈ uᴴ) u)
-- -- update-valid'ᴴ (S.there {u = u} l∈Γ) S.here Γⱽ _ Δ₂ⱽ = ⊥-elim (∈-not-unique (member-∈ l∈Γ) u)
-- -- update-valid'ᴴ {Γ = S.⟨ x , x₁ ⟩ S.∷ Γ} (S.there l∈Γ) (S.there u₁) (proj₁ , proj₂) Γ⊆ᴴΓ'' Δ₂ⱽ = {!!} , (update-valid'ᴴ l∈Γ u₁ proj₂ {!drop ?!}  Δ₂ⱽ)
-- -- update-valid'ᴴ {Γ = S.∙ S.∷ Γ} (S.there l∈Γ) (S.there u₁) (() , proj₂) Δ₂ⱽ


-- -- valid⇝ : ∀ {l τ π₁ π₂ τ₁ τ₂} {t₁ : Term π₁ τ₁} {t₂ : Term π₂ τ₂} {Δ₁ : Heap l π₁} {Δ₂ : Heap l π₂} {S₁ : Stack l τ₁ τ} {S₂ : Stack l τ₂ τ}
-- --             {M : Memory l} -> l ↦ ⟨ M , Δ₁ ⟩ Γ ->
-- --            {!!} -> {!!} ⇝ {!!} -> {!!}
-- -- valid⇝ = {!!}

-- valid⟼ : ∀ {ls τ l} {p₁ p₂ : Program l ls τ} -> validᴾ p₁ -> p₁ ⟼ p₂ -> validᴾ p₂
-- valid⟼ = {!!}
-- -- (proj₁ , proj₂ , proj₃ ) (SS.Pure l∈Γ step uᴴ) = FIXME
-- --   where postulate FIXME : ∀ {a} {A : Set a} -> A
-- --         with valid-memberᴴ proj₁ l∈Γ
-- -- ... | Mⱽ , Δⱽ = {!!} , ({!!} , {!!})
-- -- valid⟼ (proj₁ , proj₃ , proj₂) (SS.New {M = M} {τ∈π = τ∈π} {l⊑h = l⊑h} H∈Γ uᴴ) = ?
-- -- -- with valid-memberᴴ proj₁ H∈Γ
-- -- -- ... | Mⱽ , Δⱽ with valid-newᴹ ∥ l⊑h ,  τ∈π ∥ M Mⱽ
-- -- -- ... | M'ⱽ , ok-Addr = update-validᴴ H∈Γ uᴴ ok-Addr M'ⱽ proj₁ , (((updateᴱ-∈ uᴴ) , valid-new-Addr {M = M} Mⱽ ∥ l⊑h ,  τ∈π ∥ uᴴ) , update-validˢ H∈Γ uᴴ (newᴹ
-- -- -- -≤ M ∥ l⊑h ,  τ∈π ∥) proj₂)
-- -- valid⟼ (proj₁ , () , proj₂) SS.New∙
-- -- valid⟼ (proj₁ , proj₂ , proj₃ , proj₄) (SS.Write₂ H∈Γ uᴹ uᴴ) = ?
-- -- -- with valid-memberᴴ proj₁ H∈Γ
-- -- -- ... | Mⱽ , Δⱽ with valid-writeᴹ uᴹ Mⱽ
-- -- -- ... | M'ⱽ , M₁≤M₂ = (update-validᴴ H∈Γ uᴴ M₁≤M₂ M'ⱽ proj₁) , (tt , (update-validˢ H∈Γ uᴴ M₁≤M₂ proj₄))
-- -- valid⟼ (proj₁ , proj₂ , proj₃ , proj₄) (SS.Writeᴰ₂ H∈Γ uᴹ uᴴ) = ?
-- -- -- with valid-memberᴴ proj₁ H∈Γ
-- -- -- ... | Mⱽ , Δⱽ with valid-writeᴹ uᴹ Mⱽ
-- -- -- ... | M'ⱽ , M₁≤M₂ = (update-validᴴ H∈Γ uᴴ M₁≤M₂ M'ⱽ proj₁) , (tt , (update-validˢ H∈Γ uᴴ M₁≤M₂ proj₄))
-- -- valid⟼ (proj₁ , proj₃ , () , proj₂) SS.Write∙₂
-- -- valid⟼ (proj₁ , proj₃ , proj₂ , proj₄) (SS.Read₂ l∈Γ n∈M) = proj₁ , (T.tt , proj₄)
-- -- valid⟼ (proj₁ , proj₂ , proj₃ , proj₄) (SS.Readᴰ₂ L∈Γ n∈M) = proj₁ , T.tt , proj₄
-- -- --... |  Δⱽ  = proj₁ , (valid-memberᴱ {Δ = Δ} {x = τ∈π} Δⱽ t∈Δ , proj₂)
-- -- valid⟼ () SS.Hole
