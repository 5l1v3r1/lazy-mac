import Lemmas as L₁
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
validᵀ {ls} {π = π} Ms (S.new {h = H} x t) = H ∈ ls × validᵀ Ms t
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

--------------------------------------------------------------------------------

open import Relation.Binary as B
open B.DecTotalOrder Data.Nat.decTotalOrder hiding (_≤_) renaming (trans to trans-≤ ; refl to refl-≤)

open import Function

data _⊆ᴹ_ : ∀ {ls₁ ls₂} -> Memories ls₁ -> Memories ls₂ -> Set where
  nil : [] ⊆ᴹ []
  cons : ∀ {ls₁ ls₂ l} {u₁ : Unique l ls₁} {u₂ : Unique l ls₂} {Ms₁ : Memories ls₁} {Ms₂ : Memories ls₂} {M₁ M₂ : Memory l}
         -> lengthᴹ M₁ ≤ lengthᴹ M₂ -> Ms₁ ⊆ᴹ Ms₂ -> (M₁ ∷ Ms₁) ⊆ᴹ (M₂ ∷ Ms₂)
  drop : ∀ {ls₁ ls₂ l} {u₂ : Unique l ls₂} {Ms₁ : Memories ls₁} {Ms₂ : Memories ls₂} {M : Memory l}
           -> Ms₁ ⊆ᴹ Ms₂ -> Ms₁ ⊆ᴹ (M ∷ Ms₂)

-- refl-⊆ᴱ : ∀ {π l} {Δ : Heap l π} -> Δ ⊆ᴱ Δ
-- refl-⊆ᴱ {Δ = S.[]} = nil
-- refl-⊆ᴱ {Δ = t S.∷ Δ} = cons refl-⊆ᴱ
-- refl-⊆ᴱ {Δ = S.∙} = ∙

-- refl-⊆'ᴴ : ∀ {l} {H : Heap∙ l} -> H ⊆∙ᴴ H
-- refl-⊆'ᴴ {H = S.⟨ x₁ ⟩} = ? --  ⟨ refl-≤ , refl-⊆ᴱ ⟩
-- refl-⊆'ᴴ {H = S.∙} = ∙

refl-⊆ᴹ : ∀ {ls} {Ms : Memories ls} -> Ms ⊆ᴹ Ms
refl-⊆ᴹ {Ms = S.[]} = nil
refl-⊆ᴹ {Ms = x S.∷ Ms} = cons refl-≤ refl-⊆ᴹ

open import Function

wken-Addr : ∀ {ls₁ ls₂ l} {Ms₁ : Memories ls₁} {Ms₂ : Memories ls₂} {n : ℕ} ->
              Ms₁ ⊆ᴹ Ms₂ -> (l∈ls₁ : l ∈ ls₁) -> validAddr (lookupˢ l∈ls₁ Ms₁) n ->
                            Σ (l ∈ ls₂) (λ l∈ls₂ -> validAddr (lookupˢ l∈ls₂ Ms₂) n)
wken-Addr nil () d
wken-Addr (cons x a) T.here d = here , (trans-≤ d x)
wken-Addr (cons x a) (T.there b) d = P.map there id (wken-Addr a b d)
wken-Addr (drop a) b d = P.map there id (wken-Addr a b d)

⊆ᴹ-⊆ : ∀ {ls₁ ls₂} {Ms₁ : Memories ls₁} {Ms₂ : Memories ls₂} -> Ms₁ ⊆ᴹ Ms₂ -> ls₁ ⊆ ls₂
⊆ᴹ-⊆ nil = T.base
⊆ᴹ-⊆ (cons x x₁) = T.cons (⊆ᴹ-⊆ x₁)
⊆ᴹ-⊆ (drop x) = T.drop (⊆ᴹ-⊆ x)

wkenᵀ : ∀ {π τ ls₁ ls₂} {Ms₁ : Memories ls₁} {Ms₂ : Memories ls₂} -> Ms₁ ⊆ᴹ Ms₂ -> (t : Term π τ) -> validᵀ Ms₁ t -> validᵀ Ms₂ t
wkenᵀ Ms₁⊆Ms₂ S.（） ok = T.tt
wkenᵀ Ms₁⊆Ms₂ S.True ok = T.tt
wkenᵀ Ms₁⊆Ms₂ S.False ok = T.tt
wkenᵀ Ms₁⊆Ms₂ (S.Id t) ok = wkenᵀ Ms₁⊆Ms₂ t ok
wkenᵀ Ms₁⊆Ms₂ (S.unId t) ok = wkenᵀ Ms₁⊆Ms₂ t ok
wkenᵀ Ms₁⊆Ms₂ (S.Var τ∈π) ok = T.tt
wkenᵀ Ms₁⊆Ms₂ (S.Abs t) ok = wkenᵀ Ms₁⊆Ms₂ t ok
wkenᵀ Ms₁⊆Ms₂ (S.App t t₁) (proj₁ , proj₂) = (wkenᵀ Ms₁⊆Ms₂ t proj₁) , (wkenᵀ Ms₁⊆Ms₂ t₁ proj₂)
wkenᵀ Ms₁⊆Ms₂ (S.If t Then t₁ Else t₂) (proj₁ , proj₂ , proj₃) = (wkenᵀ Ms₁⊆Ms₂ t proj₁) , ((wkenᵀ Ms₁⊆Ms₂ t₁ proj₂) , (wkenᵀ Ms₁⊆Ms₂ t₂ proj₃))
wkenᵀ Ms₁⊆Ms₂ (S.Return l₁ t) ok = wkenᵀ Ms₁⊆Ms₂ t ok
wkenᵀ Ms₁⊆Ms₂ (t S.>>= t₁) (proj₁ , proj₂) = (wkenᵀ Ms₁⊆Ms₂ t proj₁) , (wkenᵀ Ms₁⊆Ms₂ t₁ proj₂)
wkenᵀ Ms₁⊆Ms₂ (S.Mac l₁ t) ok = wkenᵀ Ms₁⊆Ms₂ t ok
wkenᵀ {τ = T.Res .l₁ T.（）} Ms₁⊆Ms₂ (S.Res l₁ t) ok = wkenᵀ Ms₁⊆Ms₂ t ok
wkenᵀ {τ = T.Res .l₁ T.Bool} Ms₁⊆Ms₂ (S.Res l₁ t) ok = wkenᵀ Ms₁⊆Ms₂ t ok
wkenᵀ {τ = T.Res .l₁ (τ T.=> τ₁)} Ms₁⊆Ms₂ (S.Res l₁ t) ok = wkenᵀ Ms₁⊆Ms₂ t ok
wkenᵀ {τ = T.Res .l₂ (T.Mac l₁ τ)} Ms₁⊆Ms₂ (S.Res l₂ t) ok = wkenᵀ Ms₁⊆Ms₂ t ok
wkenᵀ {τ = T.Res .l₂ (T.Res l₁ τ)} Ms₁⊆Ms₂ (S.Res l₂ t) ok = wkenᵀ Ms₁⊆Ms₂ t ok
wkenᵀ {τ = T.Res .l₁ (T.Id τ)} Ms₁⊆Ms₂ (S.Res l₁ t) ok = wkenᵀ Ms₁⊆Ms₂ t ok
wkenᵀ {τ = T.Res .l₁ T.Addr} Ms₁⊆Ms₂ (S.Res l₁ t) (proj₁ , proj₂ , proj₃ , proj₄) with wken-Addr Ms₁⊆Ms₂ proj₁ proj₄
... | l∈ls₂ , isValid = l∈ls₂ , (proj₂ , (proj₃ , isValid))
wkenᵀ Ms₁⊆Ms₂ (S.label l⊑h t) ok = wkenᵀ Ms₁⊆Ms₂ t ok
wkenᵀ Ms₁⊆Ms₂ (S.label∙ l⊑h t) ()
wkenᵀ Ms₁⊆Ms₂ (S.unlabel l⊑h t) ok = wkenᵀ Ms₁⊆Ms₂ t ok
wkenᵀ Ms₁⊆Ms₂ (S.read x t) ok = wkenᵀ Ms₁⊆Ms₂ t ok
wkenᵀ Ms₁⊆Ms₂ (S.write x t t₁) (proj₁ , proj₂) = (wkenᵀ Ms₁⊆Ms₂ t proj₁) , (wkenᵀ Ms₁⊆Ms₂ t₁ proj₂)
wkenᵀ Ms₁⊆Ms₂ (S.write∙ x t t₁) ()
wkenᵀ Ms₁⊆Ms₂ (S.new x t) (h∈ls , ok₃) = L₁.wken-∈ (⊆ᴹ-⊆ Ms₁⊆Ms₂) h∈ls , (wkenᵀ Ms₁⊆Ms₂ t ok₃)
wkenᵀ Ms₁⊆Ms₂ (S.new∙ x t) ()
wkenᵀ Ms₁⊆Ms₂ S.#[ x ] ok = T.tt
wkenᵀ Ms₁⊆Ms₂ S.#[ x ]ᴰ ok = T.tt
wkenᵀ Ms₁⊆Ms₂ (S.fork l⊑h t) ok = wkenᵀ Ms₁⊆Ms₂ t ok
wkenᵀ Ms₁⊆Ms₂ (S.fork∙ l⊑h t) ()
wkenᵀ Ms₁⊆Ms₂ (S.deepDup t) ok = wkenᵀ Ms₁⊆Ms₂ t ok
wkenᵀ Ms₁⊆Ms₂ S.∙ ()

wkenᴹᵀ : ∀ {ls₁ ls₂ π τ} {Ms₁ : Memories ls₁} {Ms₂ : Memories ls₂} {mt : Maybe (Term π τ)} -> Ms₁ ⊆ᴹ Ms₂ -> validᴹᵀ Ms₁ mt -> validᴹᵀ Ms₂ mt
wkenᴹᵀ {mt = just x} Ms₁⊆Ms₂ v = wkenᵀ Ms₁⊆Ms₂ x v
wkenᴹᵀ {mt = nothing} Ms₁⊆Ms₂ v = T.tt

wkenᴱ : ∀ {l π ls₁ ls₂} {Δ : Heap l π} {Ms₁ : Memories ls₁} {Ms₂ : Memories ls₂} -> Ms₁ ⊆ᴹ Ms₂ -> validᴴ Ms₁ Δ -> validᴴ Ms₂ Δ
wkenᴱ {Δ = S.[]} Ms₁⊆Ms₂ Δᴱ = tt
wkenᴱ {Δ = mt S.∷ Δ} Ms₁⊆Ms₂  (mtⱽ  , Δᴱ) = wkenᴹᵀ {mt = mt} Ms₁⊆Ms₂ mtⱽ  , wkenᴱ {Δ = Δ} Ms₁⊆Ms₂ Δᴱ
wkenᴱ {Δ = S.∙} _ ()

-- wkenᴹ : ∀ {l} {M₁ M₂ : Memory l} -> lengthᴹ M₁ ≤ lengthᴹ M₂ -> validᴹ M₁ -> validᴹ M₂
-- wkenᴹ {M₂ = S.[]} x x₁ = tt
-- wkenᴹ {M₂ = cᴸ S.∷ M₂} x x₁ = {!!}
-- wkenᴹ {M₁ = S.[]} {S.∙} z≤n x₁ = {!!}  -- No! :-(
-- wkenᴹ {M₁ = cᴸ S.∷ M₁} {S.∙} () x₁
-- wkenᴹ {M₁ = S.∙} {S.∙} z≤n ()

wkenᴴ∙ : ∀ {l ls₁ ls₂} {Ms₁ : Memories ls₁} {Ms₂ : Memories ls₂} {H : Heap∙ l} -> Ms₁ ⊆ᴹ Ms₂ -> validᴴ∙ Ms₁ H -> validᴴ∙ Ms₂ H
wkenᴴ∙ {H = S.⟨ Δ ⟩} Ms₁⊆Ms₂ x = wkenᴱ {Δ = Δ} Ms₁⊆Ms₂ x
wkenᴴ∙ {H = S.∙} _ ()

-- wkenᴴ : ∀ {ls₁ ls₂} {Ms₁ : Heaps ls₁} {Ms₂ : Heaps ls₂} -> Ms₁ ⊆ᴹ Ms₂ -> validᴴ Ms₁ -> validᴴ Ms₂
-- wkenᴴ nil x = tt
-- wkenᴴ (cons x x₁) (proj₁ , proj₂) = (wkenᴴ₂' (cons x x₁) x proj₁) , wkenᴴ x₁ proj₂
-- wkenᴴ {Ms₁ = Ms₁} (drop x) x₁ = {!!} , (wkenᴴ x x₁)

map-wkenᴴ : ∀ {ls ls₁ ls₂} {Ms₁ : Memories ls₁} {Ms₂ : Memories ls₂} {Γ : Heaps ls} -> Ms₁ ⊆ᴹ Ms₂ -> map-validᴴ Ms₁ Γ -> map-validᴴ Ms₂ Γ
map-wkenᴴ {Γ = S.[]} Ms₁⊆Ms₂ v = T.tt
map-wkenᴴ {Γ = H S.∷ Γ} Ms₁⊆Ms₂ v = (wkenᴴ∙ {H = H} Ms₁⊆Ms₂ (proj₁ v)) , (map-wkenᴴ Ms₁⊆Ms₂ (proj₂ v))

--------------------------------------------------------------------------------
-- Initial Valid configurations

-- TODO move to different module?

Ms₀ : {{ls : List Label}} {{us : valid-𝓛 ls}} -> Memories ls
Ms₀ {{[]}} {{_}} = []
Ms₀ {{l ∷ ls}} {{u , us}} = [] ∷ Ms₀

map-validᴹ₀ : ∀ {ls : List Label} {{us : valid-𝓛 ls}} -> map-validᴹ (Ms₀ {{ls}})
map-validᴹ₀ {T.[]} = tt
map-validᴹ₀ {x T.∷ ls} = tt , map-validᴹ₀

Γ₀ : {{ls  : List Label}} {{us : valid-𝓛 ls}} -> Heaps ls
Γ₀ {{T.[]}} {{T.tt}} = S.[]
Γ₀ {{x T.∷ ls}} {{proj₁ , proj₂}} = ⟨ [] ⟩ S.∷ Γ₀

map-validᴴ₀ : ∀ {ls : List Label} {{us : valid-𝓛 ls}} -> map-validᴴ (Ms₀ {{ls}}) (Γ₀ {{ls}})
map-validᴴ₀ {T.[]} = T.tt
map-validᴴ₀ {_ T.∷ ls} {{_ , us}} = T.tt , map-wkenᴴ (drop refl-⊆ᴹ) (map-validᴴ₀ {ls})

S₀ : ∀ {l τ} -> Stack l [] τ τ
S₀ = []

validˢ₀ : ∀ {l τ ls} -> (Ms : Memories ls) -> validˢ Ms (S₀ {l} {τ})
validˢ₀ Ms = tt

TS₀ : ∀ {l τ} -> Term [] τ -> TS∙ l τ
TS₀ t = mkTS t S₀

P₀ : ∀ {ls l τ} {{us : valid-𝓛 ls}} -> Term [] τ -> Program l ls τ
P₀ {{us = us}} t = mkP Ms₀ Γ₀ (TS₀ t)

-- Initial configurations are valid given a valid initial term,
-- i.e. it does not have no free variables and references.
validᴾ₀ : ∀ {τ l ls} {t : Term [] τ} {{us : valid-𝓛 ls}} -> validᵀ (Ms₀ {{ls}}) t -> validᴾ (P₀ {l = l} {{us}} t)
validᴾ₀ vᵀ = map-validᴹ₀ , (map-validᴴ₀ , (vᵀ , tt))

valid-∈ᴱ : ∀ {l ls₁ ls₂} {Ms : Memories ls₁} {Γ : Heaps ls₂} {Δ : Heap∙ l} -> map-validᴴ Ms Γ -> l ↦ Δ ∈ᴱ Γ -> validᴴ∙ Ms Δ
valid-∈ᴱ (proj₁ , proj₂) S.here = proj₁
valid-∈ᴱ (proj₁ , proj₂) (S.there y₁) = valid-∈ᴱ proj₂ y₁

--------------------------------------------------------------------------------

import Sequential.Semantics as SS
open SS 𝓛

open import Relation.Binary.PropositionalEquality

-- valid-memberᴴ : ∀ {l ls} {Ms : Heaps ls} {H : Heap l} -> validᴴ Ms -> l ↦ H ∈ᴴ Ms -> validᴴ₂ Ms H
-- valid-memberᴴ (proj₁ , proj₂) S.here = proj₁
-- valid-memberᴴ (proj₁ , proj₂) (S.there l∈Ms) = wkenᴴ₂ (drop refl-⊆ᴹ) (valid-memberᴴ proj₂ l∈Ms)

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

-- -- newᴴ-≤ : ∀ {l ls} {M₁ M₂ : Heaps ls} {M₁ M₂ : Memory l} {Δ : Heap l π} -> l ↦ ⟨ Δ ⟩ ∈ᴱ Ms₁ -> Ms₂ ≔ Ms₁ [ l ↦ ⟨ Δ ⟩ ]ᴱ ->
-- --            (lengthᴹ M₁) ≤ (lengthᴹ M₂) ->
-- --           (∀ {l} -> (l∈ls : l ∈ ls) ->
-- --              lengthᴹ (lookupˢ l∈ls Ms₁) ≤ lengthᴹ (lookupˢ l∈ls Ms₂))
-- -- newᴴ-≤ = ?
-- -- S.here S.here M₁≤M₂ T.here = M₁≤M₂
-- -- newᴴ-≤ S.here S.here _ (T.there l∈ls) = refl-≤
-- -- newᴴ-≤ {l} S.here (S.there {u = u} y) = ⊥-elim (∈-not-unique (updateᴱ-∈ y) u)
-- -- newᴴ-≤ (S.there {u = u} x) S.here = ⊥-elim (∈-not-unique (memberᴱ-∈ x) u)
-- -- newᴴ-≤ {Ms₁ = S.⟨ x , x₁ ⟩ S.∷ Ms₁} (S.there x₂) (S.there y) _ T.here = refl-≤
-- -- newᴴ-≤ {Ms₁ = S.∙ S.∷ Ms₁} (S.there x) (S.there y) _ T.here = refl-≤
-- -- newᴴ-≤ (S.there x) (S.there y) M₁≤M₂ (T.there z) = newᴴ-≤ x y M₁≤M₂ z

-- update-validᵀ : ∀ {l π  τ ls} {Ms₁ Ms₂ : Memories ls} {M₁ M₂ : Memory l} ->
--                 l ↦ M₁ ∈ˢ Ms₁ ->
--                 Ms₂ ≔ Ms₁ [ l ↦ M₁ ]ˢ -> (lengthᴹ M₁) ≤ (lengthᴹ M₂) -> (t : Term π τ) -> validᵀ Ms₁ t -> validᵀ Ms₂ t
-- update-validᵀ l∈Ms u M₁≤M₂ S.（） tⱽ = tt
-- update-validᵀ l∈Ms u M₁≤M₂ S.True tⱽ = tt
-- update-validᵀ l∈Ms u M₁≤M₂ S.False tⱽ = tt
-- update-validᵀ l∈Ms u M₁≤M₂ (S.Id t) tⱽ = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ
-- update-validᵀ l∈Ms u M₁≤M₂ (S.unId t) tⱽ = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ
-- update-validᵀ l∈Ms u M₁≤M₂ (S.Var τ∈π) tⱽ = tt
-- update-validᵀ l∈Ms u M₁≤M₂ (S.Abs t) tⱽ = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ
-- update-validᵀ l∈Ms u M₁≤M₂ (S.App t t₁) (tⱽ , t₁ⱽ) = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ , update-validᵀ l∈Ms u M₁≤M₂ t₁ t₁ⱽ
-- update-validᵀ l∈Ms u M₁≤M₂ (S.If t Then t₁ Else t₂) (tⱽ , t₁ⱽ , t₂ⱽ)
--   = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ , update-validᵀ l∈Ms u M₁≤M₂ t₁ t₁ⱽ , update-validᵀ l∈Ms u M₁≤M₂ t₂ t₂ⱽ
-- update-validᵀ l∈Ms u M₁≤M₂ (S.Return l₁ t) tⱽ = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ
-- update-validᵀ l∈Ms u M₁≤M₂ (t S.>>= t₁) (tⱽ , t₁ⱽ) = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ , update-validᵀ l∈Ms u M₁≤M₂ t₁ t₁ⱽ
-- update-validᵀ l∈Ms u M₁≤M₂ (S.Mac l₁ t) tⱽ = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ
-- update-validᵀ {τ = Res .l₁ （）} l∈Ms u M₁≤M₂ (S.Res l₁ t) tⱽ = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ
-- update-validᵀ {τ = Res .l₁ Bool} l∈Ms u M₁≤M₂ (S.Res l₁ t) tⱽ = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ
-- update-validᵀ {τ = Res .l₁ (τ => τ₁)} l∈Ms u M₁≤M₂ (S.Res l₁ t) tⱽ = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ
-- update-validᵀ {τ = Res .l₂ (Mac l₁ τ)} l∈Ms u M₁≤M₂ (S.Res l₂ t) tⱽ = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ
-- update-validᵀ {τ = Res .l₂ (Res l₁ τ)} l∈Ms u M₁≤M₂ (S.Res l₂ t) tⱽ = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ
-- update-validᵀ {τ = Res .l₁ (Id τ)} l∈Ms u M₁≤M₂ (S.Res l₁ t) tⱽ = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ
-- update-validᵀ {τ = Res .l₁ Addr} l∈Ms u M₁≤M₂ (S.Res l₁ (S.unId t)) tⱽ = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ
-- update-validᵀ {τ = Res .l₁ Addr} l∈Ms u M₁≤M₂ (S.Res l₁ (S.Var τ∈π)) tⱽ = tt
-- update-validᵀ {τ = Res .l₁ Addr} l∈Ms u M₁≤M₂ (S.Res l₁ (S.App t t₁)) (tⱽ , t₁ⱽ) = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ , update-validᵀ l∈Ms u M₁≤M₂ t₁ t₁ⱽ
-- update-validᵀ {τ = Res .l₁ Addr} l∈Ms u M₁≤M₂ (S.Res l₁ (S.If t Then t₁ Else t₂)) (tⱽ , t₁ⱽ , t₂ⱽ)
--   = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ , update-validᵀ l∈Ms u M₁≤M₂ t₁ t₁ⱽ , update-validᵀ l∈Ms u M₁≤M₂ t₂ t₂ⱽ
-- update-validᵀ {τ = Res .l₁ Addr} l∈Ms u M₁≤M₂ (S.Res l₁ S.#[ n ]) (l∈ls , tⱽ) = l∈ls , trans-≤ tⱽ {!!} -- (newᴴ-≤ l∈Ms u M₁≤M₂ l∈ls)
-- update-validᵀ {τ = Res .l₁ Addr} l∈Ms u M₁≤M₂ (S.Res l₁ S.#[ n ]ᴰ) (l∈ls , tⱽ) = l∈ls , trans-≤ tⱽ {!!} -- (newᴴ-≤ l∈Ms u M₁≤M₂ l∈ls)
-- update-validᵀ {τ = Res .l₁ Addr} l∈Ms u M₁≤M₂ (S.Res l₁ (S.deepDup t)) tⱽ = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ
-- update-validᵀ {τ = Res .l₁ Addr} l∈Ms u M₁≤M₂ (S.Res l₁ S.∙) ()
-- update-validᵀ l∈Ms u M₁≤M₂ (S.label l⊑h t) tⱽ = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ
-- update-validᵀ l∈Ms u M₁≤M₂ (S.label∙ l⊑h t) ()
-- update-validᵀ l∈Ms u M₁≤M₂ (S.unlabel l⊑h t) tⱽ = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ
-- update-validᵀ l∈Ms u M₁≤M₂ (S.read x t) tⱽ =  update-validᵀ l∈Ms u M₁≤M₂ t tⱽ
-- update-validᵀ l∈Ms u M₁≤M₂ (S.write x t t₁) (tⱽ , t₁ⱽ) = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ ,  update-validᵀ l∈Ms u M₁≤M₂ t₁ t₁ⱽ
-- update-validᵀ l∈Ms u M₁≤M₂ (S.write∙ x t t₁) ()
-- update-validᵀ l∈Ms u M₁≤M₂ (S.new x t) ok = {!!} -- (ok , tⱽ) = {!!} -- ok , update-validᵀ l∈Ms u M₁≤M₂ t tⱽ
-- update-validᵀ l∈Ms u M₁≤M₂ (S.new∙ x t) ()
-- update-validᵀ l∈Ms u M₁≤M₂ S.#[ x ] tⱽ = tt
-- update-validᵀ l∈Ms u M₁≤M₂ S.#[ x ]ᴰ tⱽ = tt
-- update-validᵀ l∈Ms u M₁≤M₂ (S.fork l⊑h t) tⱽ = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ
-- update-validᵀ l∈Ms u M₁≤M₂ (S.fork∙ l⊑h t) ()
-- update-validᵀ l∈Ms u M₁≤M₂ (S.deepDup t) tⱽ = update-validᵀ l∈Ms u M₁≤M₂ t tⱽ
-- update-validᵀ l∈Ms u M₁≤M₂ S.∙ ()

-- update-validᶜ : ∀ {l π l' ls τ₁ τ₂} {C : Cont l' π τ₁ τ₂} {Ms₁ Ms₂ : Memories ls} {M₁ M₂ : Memory l} ->
--                 l ↦ M₁ ∈ˢ Ms₁ ->
--                 Ms₂ ≔ Ms₁ [ l ↦ M₂ ]ˢ -> (lengthᴹ M₁) ≤ (lengthᴹ M₂)
--                 -> validᶜ Ms₁ C -> validᶜ Ms₂ C
-- update-validᶜ {C = S.Var τ∈π} l∈Ms u M₁≤M₂ Cⱽ = tt
-- update-validᶜ {C = S.# τ∈π} l∈Ms u M₁≤M₂ Cⱽ = tt
-- update-validᶜ {C = S.Then t₁ Else t₂} l∈Ms u M₁≤M₂ (proj₁ , proj₂) = {!!} -- (update-validᵀ l∈Ms u M₁≤M₂ t₁ proj₁) , (update-validᵀ l∈Ms u M₁≤M₂ t₂ proj₂)
-- update-validᶜ {C = S.Bind t} l∈Ms u M₁≤M₂ Cⱽ = {!!} -- update-validᵀ l∈Ms u M₁≤M₂ t Cⱽ
-- update-validᶜ {C = S.unlabel p} l∈Ms u M₁≤M₂ Cⱽ = tt
-- update-validᶜ {C = S.unId} l∈Ms u M₁≤M₂ Cⱽ = tt
-- update-validᶜ {C = S.write x τ∈π} l∈Ms u M₁≤M₂ Cⱽ = tt
-- update-validᶜ {C = S.write∙ x τ∈π} l∈Ms u M₁≤M₂ ()
-- update-validᶜ {C = S.read x} l∈Ms u M₁≤M₂ Cⱽ = tt

-- update-validˢ : ∀ {l π l' ls τ₁ τ₂} {S : Stack l' π τ₁ τ₂} {Ms Ms' : Memories ls} {M₁ M₂ : Memory l} ->
--                   l ↦ M₁ ∈ˢ Ms ->
--                   Ms' ≔ Ms [ l ↦ M₂ ]ˢ -> (lengthᴹ M₁) ≤ (lengthᴹ M₂)
--                 -> validˢ Ms S -> validˢ Ms' S
-- update-validˢ {S = S.[]} l∈Ms u M₁≤M₂ Sⱽ = tt
-- update-validˢ {S = C S.∷ S} l∈Ms u M₁≤M₂ (Cⱽ , Sⱽ) = update-validᶜ {C = C} l∈Ms u M₁≤M₂ Cⱽ , (update-validˢ l∈Ms u M₁≤M₂ Sⱽ)
-- update-validˢ {S = S.∙} l∈Ms u M₁≤M₂ ()

-- -- update-⊆ᴹ : ∀ {l π ls} {Ms Ms' : Heaps ls} {Δ : Heap l π} {M₁ M₂ : Memory l} ->
-- --               l ↦ ⟨ Δ ⟩ ∈ᴴ Ms ->
-- --                 Ms' ≔ Ms [ l ↦ ⟨ Δ ⟩ ]ᴴ ->
-- --                 (lengthᴹ M₁) ≤ (lengthᴹ M₂) ->
-- --                 Ms ⊆ᴹ Ms'
-- -- update-⊆ᴹ S.here S.here M₁≤M₂ = ?
-- -- cons (⟨ M₁≤M₂ , refl-⊆ᴱ ⟩) refl-⊆ᴹ
-- -- update-⊆ᴹ S.here (S.there {u = u} uᴴ) M₁≤M₂ = ⊥-elim (∈-not-unique (update-∈ uᴴ) u)
-- -- update-⊆ᴹ (S.there {u = u} l∈Δ) S.here M₁≤M₂ = ⊥-elim (∈-not-unique (member-∈ l∈Δ) u)
-- -- update-⊆ᴹ (S.there l∈Δ) (S.there u₁) M₁≤M₂ = cons refl-⊆'ᴴ (update-⊆ᴹ l∈Δ u₁ M₁≤M₂)

-- -- update-validᴴ : ∀ {l π ls} {Ms Ms' : Heaps ls} {Δ : Heap l π} {M₁ M₂ : Memory l} ->
-- --                   l ↦ ⟨ Δ ⟩ ∈ᴴ Ms ->
-- --                   Ms' ≔ Ms [ l ↦ ⟨ Δ ⟩ ]ᴴ ->
-- --                   (lengthᴹ M₁) ≤ (lengthᴹ M₂) ->
-- --                   validᴹ M₂ ->
-- --                   validᴴ Ms -> validᴴ Ms'
-- -- update-validᴴ = ?
-- -- {Ms = _ ∷ Ms} {Δ = Δ} {M₁} {M₂} = ?
-- -- S.here S.here M₁≤M₂ M₂ⱽ ((proj₁ , proj₂) , proj₃)
-- --   = (M₂ⱽ , wkenᴱ {Δ = Δ} (cons (⟨ M₁≤M₂ , refl-⊆ᴱ ⟩) refl-⊆ᴹ) proj₂ ) , proj₃
-- -- update-validᴴ {Ms = S._∷_ {{u}} _ _} S.here (S.there b) M₁≤M₂ M₂ⱽ Msⱽ = ⊥-elim (∈-not-unique (update-∈ b) u)
-- -- update-validᴴ {Ms = S._∷_ {{u}} _ _} (S.there a) S.here M₁≤M₂ M₂ⱽ Msⱽ = ⊥-elim (∈-not-unique (member-∈ a) u)
-- -- update-validᴴ {Ms = S.⟨ M' , Δ' ⟩ S.∷ Ms} (S.there a) (S.there b) M₁≤M₂ M₂ⱽ ((proj₁ , proj₂) , proj₃)
-- --   = (proj₁ , wkenᴱ {Δ = Δ'} (update-⊆ᴹ (there a) (there b) M₁≤M₂) proj₂) , (update-validᴴ a b M₁≤M₂ M₂ⱽ proj₃)
-- -- update-validᴴ {Ms = S.∙ S.∷ Ms} (S.there a) (S.there b) M₁≤M₂ M₂ⱽ (() , proj₂)



-- -- This does not go because I need to restrict Ms to get to the memory where the update occurs
-- -- which may make some references invalid.
-- -- update-valid'ᴴ : ∀ {l π₁ π₂ ls ls'} {Ms Ms' : Heaps ls} {Ms'' : Heaps ls'} {Δ₁ : Heap l π₁} {Δ₂ : Heap l π₂} {M : Memory l} ->
-- --                   l ↦ ⟨ M , Δ₁ ⟩ ∈ᴴ Ms ->
-- --                   Ms' ≔ Ms [ l ↦ ⟨ M , Δ₂ ⟩ ]ᴴ ->
-- --                   validᴴ Ms -> Ms ⊆ᴹ Ms'' -> validᴴ Ms'' Δ₂ -> validᴴ Ms'
-- -- update-valid'ᴴ S.here S.here Msⱽ Ms⊆ᴹMs'' Δ₂ⱽ = {!!}
-- -- update-valid'ᴴ S.here (S.there {u = u} uᴴ) Msⱽ _ Δ₂ⱽ = ⊥-elim (∈-not-unique (update-∈ uᴴ) u)
-- -- update-valid'ᴴ (S.there {u = u} l∈Ms) S.here Msⱽ _ Δ₂ⱽ = ⊥-elim (∈-not-unique (member-∈ l∈Ms) u)
-- -- update-valid'ᴴ {Ms = S.⟨ x , x₁ ⟩ S.∷ Ms} (S.there l∈Ms) (S.there u₁) (proj₁ , proj₂) Ms⊆ᴹMs'' Δ₂ⱽ = {!!} , (update-valid'ᴴ l∈Ms u₁ proj₂ {!drop ?!}  Δ₂ⱽ)
-- -- update-valid'ᴴ {Ms = S.∙ S.∷ Ms} (S.there l∈Ms) (S.there u₁) (() , proj₂) Δ₂ⱽ


-- -- valid⇝ : ∀ {l τ π₁ π₂ τ₁ τ₂} {t₁ : Term π₁ τ₁} {t₂ : Term π₂ τ₂} {Δ₁ : Heap l π₁} {Δ₂ : Heap l π₂} {S₁ : Stack l τ₁ τ} {S₂ : Stack l τ₂ τ}
-- --             {M : Memory l} -> l ↦ ⟨ M , Δ₁ ⟩ Ms ->
-- --            {!!} -> {!!} ⇝ {!!} -> {!!}
-- -- valid⇝ = {!!}

-- valid⟼ : ∀ {ls τ l} {p₁ p₂ : Program l ls τ} -> validᴾ p₁ -> p₁ ⟼ p₂ -> validᴾ p₂
-- valid⟼ = {!!}
-- -- (proj₁ , proj₂ , proj₃ ) (SS.Pure l∈Ms step uᴴ) = FIXME
-- --   where postulate FIXME : ∀ {a} {A : Set a} -> A
-- --         with valid-memberᴴ proj₁ l∈Ms
-- -- ... | Mⱽ , Δⱽ = {!!} , ({!!} , {!!})
-- -- valid⟼ (proj₁ , proj₃ , proj₂) (SS.New {M = M} {τ∈π = τ∈π} {l⊑h = l⊑h} H∈Ms uᴴ) = ?
-- -- -- with valid-memberᴴ proj₁ H∈Ms
-- -- -- ... | Mⱽ , Δⱽ with valid-newᴹ ∥ l⊑h ,  τ∈π ∥ M Mⱽ
-- -- -- ... | M'ⱽ , ok-Addr = update-validᴴ H∈Ms uᴴ ok-Addr M'ⱽ proj₁ , (((updateᴱ-∈ uᴴ) , valid-new-Addr {M = M} Mⱽ ∥ l⊑h ,  τ∈π ∥ uᴴ) , update-validˢ H∈Ms uᴴ (newᴹ
-- -- -- -≤ M ∥ l⊑h ,  τ∈π ∥) proj₂)
-- -- valid⟼ (proj₁ , () , proj₂) SS.New∙
-- -- valid⟼ (proj₁ , proj₂ , proj₃ , proj₄) (SS.Write₂ H∈Ms uᴹ uᴴ) = ?
-- -- -- with valid-memberᴴ proj₁ H∈Ms
-- -- -- ... | Mⱽ , Δⱽ with valid-writeᴹ uᴹ Mⱽ
-- -- -- ... | M'ⱽ , M₁≤M₂ = (update-validᴴ H∈Ms uᴴ M₁≤M₂ M'ⱽ proj₁) , (tt , (update-validˢ H∈Ms uᴴ M₁≤M₂ proj₄))
-- -- valid⟼ (proj₁ , proj₂ , proj₃ , proj₄) (SS.Writeᴰ₂ H∈Ms uᴹ uᴴ) = ?
-- -- -- with valid-memberᴴ proj₁ H∈Ms
-- -- -- ... | Mⱽ , Δⱽ with valid-writeᴹ uᴹ Mⱽ
-- -- -- ... | M'ⱽ , M₁≤M₂ = (update-validᴴ H∈Ms uᴴ M₁≤M₂ M'ⱽ proj₁) , (tt , (update-validˢ H∈Ms uᴴ M₁≤M₂ proj₄))
-- -- valid⟼ (proj₁ , proj₃ , () , proj₂) SS.Write∙₂
-- -- valid⟼ (proj₁ , proj₃ , proj₂ , proj₄) (SS.Read₂ l∈Ms n∈M) = proj₁ , (T.tt , proj₄)
-- -- valid⟼ (proj₁ , proj₂ , proj₃ , proj₄) (SS.Readᴰ₂ L∈Ms n∈M) = proj₁ , T.tt , proj₄
-- -- --... |  Δⱽ  = proj₁ , (valid-memberᴱ {Δ = Δ} {x = τ∈π} Δⱽ t∈Δ , proj₂)
-- -- valid⟼ () SS.Hole
