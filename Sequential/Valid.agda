import Lemmas as L₁
import Lattice as L

module Sequential.Valid (𝓛 : L.Lattice) where

import Types as T hiding (wken-∈)
open T 𝓛

import Sequential.Calculus as S renaming (⟨_,_,_⟩ to mkP ; ⟨_,_⟩ to mkTS)
open S 𝓛 hiding (wkenˢ ; wkenᴴ ; wkenᶜ)

open import Data.Nat
open import Data.Empty
open import Data.Product as P
open import Data.Maybe

data ValidAddr {l} : Memory l -> ℕ -> Ty -> Set where
  here : ∀ {τ} {M : Memory l} {c : Cell l τ} -> ValidAddr (c ∷ M) 0 τ
  there : ∀ {n τ τ'} {c : Cell l τ'} {M : Memory l} -> ValidAddr M n τ -> ValidAddr (c ∷ M) (suc n) τ

data IsAddr {π τ} : Term π (Addr τ) -> ℕ -> Set where
  is#[_] : (n : ℕ) -> IsAddr #[ n ] n
  is#[_]ᴰ : (n : ℕ) -> IsAddr #[ n ]ᴰ n

-- A valid term contains only valid references, that contain a valid address.
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
validᵀ {ls} {τ = Res .l (Addr τ)} Ms (S.Res l t) = Σ (l ∈ ls) (λ l∈ls -> ∃ (λ n -> IsAddr t n × ValidAddr (lookupˢ l∈ls Ms) n τ))
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
validᵀ {ls} Ms (S.fork {h = H} l⊑h t) = H ∈ ls × validᵀ Ms t
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

data _⊆ᴹ_ {l : Label} : Memory l -> Memory l -> Set where
  ∙ : ∙ ⊆ᴹ ∙
  nil : ∀ {M} -> [] ⊆ᴹ M
  cons : ∀ {τ M₁ M₂} {c₁ c₂ : Cell l τ} -> M₁ ⊆ᴹ M₂ -> (c₁ ∷ M₁) ⊆ᴹ (c₂ ∷ M₂)

data _⊆ˢ_ : ∀ {ls₁ ls₂} -> Memories ls₁ -> Memories ls₂ -> Set where
  nil : [] ⊆ˢ []
  cons : ∀ {ls₁ ls₂ l} {u₁ : Unique l ls₁} {u₂ : Unique l ls₂} {Ms₁ : Memories ls₁} {Ms₂ : Memories ls₂} {M₁ M₂ : Memory l}
         -> M₁ ⊆ᴹ M₂ -> Ms₁ ⊆ˢ Ms₂ -> (M₁ ∷ Ms₁) ⊆ˢ (M₂ ∷ Ms₂)
  drop : ∀ {ls₁ ls₂ l} {u₂ : Unique l ls₂} {Ms₁ : Memories ls₁} {Ms₂ : Memories ls₂} {M : Memory l}
           -> Ms₁ ⊆ˢ Ms₂ -> Ms₁ ⊆ˢ (M ∷ Ms₂)

refl-⊆ᴹ : ∀ {l} {M : Memory l} -> M ⊆ᴹ M
refl-⊆ᴹ {M = S.[]} = nil
refl-⊆ᴹ {M = cᴸ S.∷ M} = cons refl-⊆ᴹ
refl-⊆ᴹ {M = S.∙} = ∙

refl-⊆ˢ : ∀ {ls} {Ms : Memories ls} -> Ms ⊆ˢ Ms
refl-⊆ˢ {Ms = S.[]} = nil
refl-⊆ˢ {Ms = x S.∷ Ms} = cons refl-⊆ᴹ refl-⊆ˢ

open import Function

-- wken-Addr

wken-Addr : ∀ {n l τ} {M₁ M₂ : Memory l} -> M₁ ⊆ᴹ M₂ -> ValidAddr M₁ n τ -> ValidAddr M₂ n τ
wken-Addr (cons x) here = here
wken-Addr (cons x) (there y) = there (wken-Addr x y)

⊆ˢ-⊆ : ∀ {ls₁ ls₂} {Ms₁ : Memories ls₁} {Ms₂ : Memories ls₂} -> Ms₁ ⊆ˢ Ms₂ -> ls₁ ⊆ ls₂
⊆ˢ-⊆ nil = T.base
⊆ˢ-⊆ (cons x x₁) = T.cons (⊆ˢ-⊆ x₁)
⊆ˢ-⊆ (drop x) = T.drop (⊆ˢ-⊆ x)


wken-lookupˢ : ∀ {l ls₁ ls₂} {Ms₁ : Memories ls₁} {Ms₂ : Memories ls₂} -> (Ms₁⊆Ms₂ : Ms₁ ⊆ˢ Ms₂) (l∈ls : l ∈ ls₁)
               -> lookupˢ l∈ls Ms₁ ⊆ᴹ lookupˢ (L₁.wken-∈ (⊆ˢ-⊆ Ms₁⊆Ms₂) l∈ls) Ms₂
wken-lookupˢ (cons x x₁) L₁.here = x
wken-lookupˢ (cons x₁ x) (L₁.there l∈ls) = wken-lookupˢ x l∈ls
wken-lookupˢ (drop x) y = wken-lookupˢ x y

wkenᵀ : ∀ {π τ ls₁ ls₂} {Ms₁ : Memories ls₁} {Ms₂ : Memories ls₂} -> Ms₁ ⊆ˢ Ms₂ -> (t : Term π τ) -> validᵀ Ms₁ t -> validᵀ Ms₂ t
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
wkenᵀ {τ = T.Res .l₁ (T.Addr τ)} Ms₁⊆Ms₂ (S.Res l₁ t) (l∈ls₁ , n , isA , isV)
  = (L₁.wken-∈ (⊆ˢ-⊆ Ms₁⊆Ms₂) l∈ls₁) , (n , (isA , (wken-Addr (wken-lookupˢ Ms₁⊆Ms₂ l∈ls₁) isV)))
wkenᵀ Ms₁⊆Ms₂ (S.label l⊑h t) ok = wkenᵀ Ms₁⊆Ms₂ t ok
wkenᵀ Ms₁⊆Ms₂ (S.label∙ l⊑h t) ()
wkenᵀ Ms₁⊆Ms₂ (S.unlabel l⊑h t) ok = wkenᵀ Ms₁⊆Ms₂ t ok
wkenᵀ Ms₁⊆Ms₂ (S.read x t) ok = wkenᵀ Ms₁⊆Ms₂ t ok
wkenᵀ Ms₁⊆Ms₂ (S.write x t t₁) (proj₁ , proj₂) = (wkenᵀ Ms₁⊆Ms₂ t proj₁) , (wkenᵀ Ms₁⊆Ms₂ t₁ proj₂)
wkenᵀ Ms₁⊆Ms₂ (S.write∙ x t t₁) ()
wkenᵀ Ms₁⊆Ms₂ (S.new x t) (h∈ls , ok₃) = L₁.wken-∈ (⊆ˢ-⊆ Ms₁⊆Ms₂) h∈ls , (wkenᵀ Ms₁⊆Ms₂ t ok₃)
wkenᵀ Ms₁⊆Ms₂ (S.new∙ x t) ()
wkenᵀ Ms₁⊆Ms₂ S.#[ x ] ok = T.tt
wkenᵀ Ms₁⊆Ms₂ S.#[ x ]ᴰ ok = T.tt
wkenᵀ Ms₁⊆Ms₂ (S.fork l⊑h t) (h∈ls , ok) = L₁.wken-∈ (⊆ˢ-⊆ Ms₁⊆Ms₂) h∈ls , wkenᵀ Ms₁⊆Ms₂ t ok
wkenᵀ Ms₁⊆Ms₂ (S.fork∙ l⊑h t) ()
wkenᵀ Ms₁⊆Ms₂ (S.deepDup t) ok = wkenᵀ Ms₁⊆Ms₂ t ok
wkenᵀ Ms₁⊆Ms₂ S.∙ ()

wkenᴹᵀ : ∀ {ls₁ ls₂ π τ} {Ms₁ : Memories ls₁} {Ms₂ : Memories ls₂} {mt : Maybe (Term π τ)} -> Ms₁ ⊆ˢ Ms₂ -> validᴹᵀ Ms₁ mt -> validᴹᵀ Ms₂ mt
wkenᴹᵀ {mt = just x} Ms₁⊆Ms₂ v = wkenᵀ Ms₁⊆Ms₂ x v
wkenᴹᵀ {mt = nothing} Ms₁⊆Ms₂ v = T.tt

wkenᴴ : ∀ {l π ls₁ ls₂} {Δ : Heap l π} {Ms₁ : Memories ls₁} {Ms₂ : Memories ls₂} -> Ms₁ ⊆ˢ Ms₂ -> validᴴ Ms₁ Δ -> validᴴ Ms₂ Δ
wkenᴴ {Δ = S.[]} Ms₁⊆Ms₂ Δᴱ = tt
wkenᴴ {Δ = mt S.∷ Δ} Ms₁⊆Ms₂  (mtⱽ  , Δᴱ) = wkenᴹᵀ {mt = mt} Ms₁⊆Ms₂ mtⱽ  , wkenᴴ {Δ = Δ} Ms₁⊆Ms₂ Δᴱ
wkenᴴ {Δ = S.∙} _ ()

wkenᶜ : ∀ {ls₁ ls₂ l π τ₁ τ₂} {C : Cont l π τ₁ τ₂} {Ms₁ : Memories ls₁} {Ms₂ : Memories ls₂} -> Ms₁ ⊆ˢ Ms₂ -> validᶜ Ms₁ C -> validᶜ Ms₂ C
wkenᶜ {C = S.Var τ∈π} Ms₁⊆Ms₂ Cᵛ = T.tt
wkenᶜ {C = S.# τ∈π} Ms₁⊆Ms₂ Cᵛ = T.tt
wkenᶜ {C = S.Then x Else x₁} Ms₁⊆Ms₂ Cᵛ = (wkenᵀ Ms₁⊆Ms₂ x (proj₁ Cᵛ)) , (wkenᵀ Ms₁⊆Ms₂ x₁ (proj₂ Cᵛ))
wkenᶜ {C = S.Bind x} Ms₁⊆Ms₂ Cᵛ = wkenᵀ Ms₁⊆Ms₂ x Cᵛ
wkenᶜ {C = S.unlabel p} Ms₁⊆Ms₂ Cᵛ = T.tt
wkenᶜ {C = S.unId} Ms₁⊆Ms₂ Cᵛ = T.tt
wkenᶜ {C = S.write x τ∈π} Ms₁⊆Ms₂ Cᵛ = T.tt
wkenᶜ {C = S.write∙ x τ∈π} Ms₁⊆Ms₂ ()
wkenᶜ {C = S.read x} Ms₁⊆Ms₂ Cᵛ = T.tt

wkenˢ : ∀ {ls₁ ls₂ l π τ₁ τ₂} {S : Stack l π τ₁ τ₂} {Ms₁ : Memories ls₁} {Ms₂ : Memories ls₂} -> Ms₁ ⊆ˢ Ms₂ -> validˢ Ms₁ S -> validˢ Ms₂ S
wkenˢ {S = S.[]} Ms₁⊆Ms₂ Sᵛ = T.tt
wkenˢ {S = C S.∷ S} Ms₁⊆Ms₂ (proj₁ , proj₂) = (wkenᶜ {C = C} Ms₁⊆Ms₂ proj₁) , (wkenˢ Ms₁⊆Ms₂ proj₂)
wkenˢ {S = S.∙} Ms₁⊆Ms₂ ()

wkenTS∙ : ∀ {l τ} {ls₁ ls₂} {Ms₁ : Memories ls₁} {Ms₂ : Memories ls₂} {Ts : TS∙ l τ} -> Ms₁ ⊆ˢ Ms₂ -> validTS∙ Ms₁ Ts -> validTS∙ Ms₂ Ts
wkenTS∙ {Ts = S.mkTS t S} x v = wkenᵀ x t (proj₁ v) , wkenˢ x (proj₂ v)
wkenTS∙ {Ts = S.∙} x ()

-- wkenᴹ : ∀ {l} {M₁ M₂ : Memory l} -> M₁ ⊆ᴹ M₂ -> validᴹ M₁ -> validᴹ M₂
-- wkenᴹ ∙ ()
-- wkenᴹ nil isV = {!!}
-- wkenᴹ (cons M₁⊆M₂) isV = {!!}

wkenᴴ∙ : ∀ {l ls₁ ls₂} {Ms₁ : Memories ls₁} {Ms₂ : Memories ls₂} {H : Heap∙ l} -> Ms₁ ⊆ˢ Ms₂ -> validᴴ∙ Ms₁ H -> validᴴ∙ Ms₂ H
wkenᴴ∙ {H = S.⟨ Δ ⟩} Ms₁⊆Ms₂ x = wkenᴴ {Δ = Δ} Ms₁⊆Ms₂ x
wkenᴴ∙ {H = S.∙} _ ()

-- wkenᴴ : ∀ {ls₁ ls₂} {Ms₁ : Heaps ls₁} {Ms₂ : Heaps ls₂} -> Ms₁ ⊆ˢ Ms₂ -> validᴴ Ms₁ -> validᴴ Ms₂
-- wkenᴴ nil x = tt
-- wkenᴴ (cons x x₁) (proj₁ , proj₂) = (wkenᴴ₂' (cons x x₁) x proj₁) , wkenᴴ x₁ proj₂
-- wkenᴴ {Ms₁ = Ms₁} (drop x) x₁ = {!!} , (wkenᴴ x x₁)

map-wkenᴴ : ∀ {ls ls₁ ls₂} {Ms₁ : Memories ls₁} {Ms₂ : Memories ls₂} {Γ : Heaps ls} -> Ms₁ ⊆ˢ Ms₂ -> map-validᴴ Ms₁ Γ -> map-validᴴ Ms₂ Γ
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
map-validᴴ₀ {_ T.∷ ls} {{_ , us}} = T.tt , map-wkenᴴ (drop refl-⊆ˢ) (map-validᴴ₀ {ls})

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

open import Relation.Binary.PropositionalEquality hiding (subst ; [_])

valid-wkenᵀ : ∀ {τ π₁ π₂ ls} {Ms : Memories ls} {{t : Term π₁ τ}} -> validᵀ Ms t -> (π₁⊆π₂ : π₁ ⊆ π₂) -> validᵀ Ms (wken t π₁⊆π₂)
valid-wkenᵀ {{t = S.（）}} v π₁⊆π₂ = T.tt
valid-wkenᵀ {{t = S.True}} v π₁⊆π₂ = T.tt
valid-wkenᵀ {{t = S.False}} v π₁⊆π₂ = T.tt
valid-wkenᵀ {{t = S.Id t}} v π₁⊆π₂ = valid-wkenᵀ v π₁⊆π₂
valid-wkenᵀ {{t = S.unId t}} v π₁⊆π₂ = valid-wkenᵀ v π₁⊆π₂
valid-wkenᵀ {{t = S.Var τ∈π}} v π₁⊆π₂ = T.tt
valid-wkenᵀ {{t = S.Abs t}} v π₁⊆π₂ = valid-wkenᵀ v (L₁.cons π₁⊆π₂)
valid-wkenᵀ {{t = S.App t t₁}} (proj₁ , proj₂) π₁⊆π₂ = valid-wkenᵀ proj₁ π₁⊆π₂ , valid-wkenᵀ proj₂ π₁⊆π₂
valid-wkenᵀ {{t = S.If t Then t₁ Else t₂}} (v₁ , v₂ , v₃)  π₁⊆π₂ = valid-wkenᵀ v₁ π₁⊆π₂ , valid-wkenᵀ v₂ π₁⊆π₂ , valid-wkenᵀ v₃ π₁⊆π₂
valid-wkenᵀ {{t = S.Return l t}} v π₁⊆π₂ = valid-wkenᵀ v π₁⊆π₂
valid-wkenᵀ {{t = t S.>>= t₁}} (v₁ , v₂) π₁⊆π₂ = valid-wkenᵀ v₁ π₁⊆π₂ , valid-wkenᵀ v₂ π₁⊆π₂
valid-wkenᵀ {{t = S.Mac l t}} v π₁⊆π₂ = valid-wkenᵀ v π₁⊆π₂
valid-wkenᵀ {T.Res l T.（）} {{t = S.Res .l t}} v π₁⊆π₂ = valid-wkenᵀ v π₁⊆π₂
valid-wkenᵀ {T.Res l T.Bool} {{t = S.Res .l t}} v π₁⊆π₂ = valid-wkenᵀ v π₁⊆π₂
valid-wkenᵀ {T.Res l (τ T.=> τ₁)} {{t = S.Res .l t}} v π₁⊆π₂ = valid-wkenᵀ v π₁⊆π₂
valid-wkenᵀ {T.Res l₁ (T.Mac l τ)} {{t = S.Res .l₁ t}} v π₁⊆π₂ = valid-wkenᵀ v π₁⊆π₂
valid-wkenᵀ {T.Res l₁ (T.Res l τ)} {{t = S.Res .l₁ t}} v π₁⊆π₂ = valid-wkenᵀ v π₁⊆π₂
valid-wkenᵀ {T.Res l (T.Id τ)} {{t = S.Res .l t}} v π₁⊆π₂ = valid-wkenᵀ v π₁⊆π₂
valid-wkenᵀ {T.Res l (T.Addr τ)} {{t = S.Res .l .(S.#[ proj₂ ])}} (proj₁ , proj₂ , is#[ .proj₂ ] , v) π₁⊆π₂
  = proj₁ , (proj₂ , (is#[ proj₂ ]  , v))
valid-wkenᵀ {T.Res l (T.Addr τ)} {{t = S.Res .l .(S.#[ proj₂ ]ᴰ)}} (proj₁ , proj₂ , is#[ .proj₂ ]ᴰ , v) π₁⊆π₂
  = proj₁ , (proj₂ , (is#[ proj₂ ]ᴰ , v))
valid-wkenᵀ {{t = S.label l⊑h t}} v π₁⊆π₂ = valid-wkenᵀ v π₁⊆π₂
valid-wkenᵀ {{t = S.label∙ l⊑h t}} () π₁⊆π₂
valid-wkenᵀ {{t = S.unlabel l⊑h t}} v π₁⊆π₂ = valid-wkenᵀ v π₁⊆π₂
valid-wkenᵀ {{t = S.read x t}} v π₁⊆π₂ = valid-wkenᵀ v π₁⊆π₂
valid-wkenᵀ {{t = S.write x t t₁}} (v₁ , v₂) π₁⊆π₂ = valid-wkenᵀ v₁ π₁⊆π₂ , valid-wkenᵀ v₂ π₁⊆π₂
valid-wkenᵀ {{t = S.write∙ x t t₁}} () π₁⊆π₂
valid-wkenᵀ {{t = S.new x t}} (l∈ls , v) π₁⊆π₂ = l∈ls , valid-wkenᵀ v π₁⊆π₂
valid-wkenᵀ {{t = S.new∙ x t}} () π₁⊆π₂
valid-wkenᵀ {{t = S.#[ x ]}} v π₁⊆π₂ = T.tt
valid-wkenᵀ {{t = S.#[ x ]ᴰ}} v π₁⊆π₂ = T.tt
valid-wkenᵀ {{t = S.fork l⊑h t}} (h∈ls , v) π₁⊆π₂ = h∈ls , valid-wkenᵀ v π₁⊆π₂
valid-wkenᵀ {{t = S.fork∙ l⊑h t}} () π₁⊆π₂
valid-wkenᵀ {{t = S.deepDup t}} v π₁⊆π₂ = valid-wkenᵀ v π₁⊆π₂
valid-wkenᵀ {{t = S.∙}} () π₁⊆π₂

valid-wkenᶜ : ∀ {τ₁ τ₂ l π₁ π₂ ls} {Ms : Memories ls} {C : Cont l π₁ τ₁ τ₂} -> validᶜ Ms C -> (π₁⊆π₂ : π₁ ⊆ π₂) -> validᶜ Ms (S.wkenᶜ 𝓛 C π₁⊆π₂)
valid-wkenᶜ {C = S.Var τ∈π} v π₁⊆π₂ = T.tt
valid-wkenᶜ {C = S.# τ∈π} v π₁⊆π₂ = T.tt
valid-wkenᶜ {C = S.Then t Else t₁} (v₁ , v₂) π₁⊆π₂ = valid-wkenᵀ {{t = t}} v₁ π₁⊆π₂ , valid-wkenᵀ {{t = t₁}} v₂ π₁⊆π₂
valid-wkenᶜ {C = S.Bind t} v π₁⊆π₂ = valid-wkenᵀ v π₁⊆π₂
valid-wkenᶜ {C = S.unlabel p} v π₁⊆π₂ = T.tt
valid-wkenᶜ {C = S.unId} v π₁⊆π₂ = T.tt
valid-wkenᶜ {C = S.write x τ∈π} v π₁⊆π₂ = T.tt
valid-wkenᶜ {C = S.write∙ x τ∈π} () π₁⊆π₂
valid-wkenᶜ {C = S.read x} v π₁⊆π₂ = T.tt

valid-wkenˢ : ∀ {τ₁ τ₂ l π₁ π₂ ls} {Ms : Memories ls} {S : Stack l π₁ τ₁ τ₂} -> validˢ Ms S -> (π₁⊆π₂ : π₁ ⊆ π₂) -> validˢ Ms (S.wkenˢ 𝓛 S π₁⊆π₂)
valid-wkenˢ {S = S.[]} v π₁⊆π₂ = T.tt
valid-wkenˢ {S = C S.∷ S} (proj₁ , proj₂) π₁⊆π₂ = (valid-wkenᶜ {C = C} proj₁ π₁⊆π₂) , (valid-wkenˢ proj₂ π₁⊆π₂)
valid-wkenˢ {S = S.∙} v π₁⊆π₂ = v

valid-subst : ∀ {π τ τ' ls} {Ms : Memories ls} {t₁ : Term π τ} {t₂ : Term (τ ∷ π) τ'} -> validᵀ Ms t₁ -> validᵀ Ms t₂ -> validᵀ Ms (subst t₁ t₂)
valid-subst {π} {Ms = Ms} {t₁'} {t₂'} = aux [] π t₁' t₂'
  where aux' : ∀ {l} {α β} (π₁ π₂ : Context) (t₁ : Term π₂ β) (x : α ∈⟨ l ⟩ (π₁ ++ [ β ] ++ π₂)) -> validᵀ Ms t₁ -> validᵀ Ms (var-subst π₁ π₂ t₁ x)
        aux' T.[] π₂ t₁ T.⟪ L₁.here ⟫ isV = isV
        aux' T.[] π₂ t₁ T.⟪ L₁.there τ∈π ⟫ isV = tt
        aux' (_ T.∷ π₁) π₂ t₁ ⟪ here ⟫ isV = tt
        aux' {l} (_ T.∷ π₁) π₂ t₁ ⟪ there x ⟫ isV with aux' {l} π₁ π₂ t₁ ⟪ x ⟫ isV
        ... | r = valid-wkenᵀ {{ var-subst π₁ π₂ t₁ ⟪ x ⟫ }} r (drop refl-⊆)

        aux : ∀ {τ α} (π₁ π₂ : Context) (t₁ : Term π₂ α) (t₂ : Term (π₁ ++ [ α ] ++ π₂) τ) ->
                      validᵀ Ms t₁ -> validᵀ Ms t₂ -> validᵀ Ms (tm-subst π₁ π₂ t₁ t₂)
        aux π₁ π₂ t₁ S.（） v₁ v₂ = T.tt
        aux π₁ π₂ t₁ S.True v₁ v₂ = T.tt
        aux π₁ π₂ t₁ S.False v₁ v₂ = T.tt
        aux π₁ π₂ t₁ (S.Id t₂) v₁ v₂ = aux π₁ π₂ t₁ t₂ v₁ v₂
        aux π₁ π₂ t₁ (S.unId t₂) v₁ v₂ = aux π₁ π₂ t₁ t₂ v₁ v₂
        aux π₁ π₂ t₁ (S.Var T.⟪ τ∈π ⟫) v₁ v₂ = aux' π₁ π₂ t₁ ⟪ ∈ᴿ-∈ τ∈π ⟫ v₁
        aux π₁ π₂ t₁ (S.Abs t₂) v₁ v₂ = aux (_ T.∷ π₁) π₂ t₁ t₂ v₁ v₂
        aux π₁ π₂ t₁ (S.App t₂ t₃) v₁ v₂ = aux π₁ π₂ t₁ t₂ v₁ (proj₁ v₂) , aux π₁ π₂ t₁ t₃ v₁ (proj₂ v₂)
        aux π₁ π₂ t₁ (S.If t₂ Then t₃ Else t₄) v₁ (proj₁ , proj₂ , proj₃)
          = aux π₁ π₂ t₁ t₂ v₁ proj₁ , aux π₁ π₂ t₁ t₃ v₁ proj₂ , aux π₁ π₂ t₁ t₄ v₁ proj₃
        aux π₁ π₂ t₁ (S.Return l t₂) v₁ v₂ = aux π₁ π₂ t₁ t₂ v₁ v₂
        aux π₁ π₂ t₁ (t₂ S.>>= t₃) v₁ v₂ = aux π₁ π₂ t₁ t₂ v₁ (proj₁ v₂) , aux π₁ π₂ t₁ t₃ v₁ (proj₂ v₂)
        aux π₁ π₂ t₁ (S.Mac l t₂) v₁ v₂ = aux π₁ π₂ t₁ t₂ v₁ v₂
        aux {T.Res .l T.（）} π₁ π₂ t₁ (S.Res l t₂) v₁ v₂ = aux π₁ π₂ t₁ t₂ v₁ v₂
        aux {T.Res .l T.Bool} π₁ π₂ t₁ (S.Res l t₂) v₁ v₂ = aux π₁ π₂ t₁ t₂ v₁ v₂
        aux {T.Res .l (τ T.=> τ₁)} π₁ π₂ t₁ (S.Res l t₂) v₁ v₂ = aux π₁ π₂ t₁ t₂ v₁ v₂
        aux {T.Res .l₁ (T.Mac l τ)} π₁ π₂ t₁ (S.Res l₁ t₂) v₁ v₂ = aux π₁ π₂ t₁ t₂ v₁ v₂
        aux {T.Res .l₁ (T.Res l τ)} π₁ π₂ t₁ (S.Res l₁ t₂) v₁ v₂ = aux π₁ π₂ t₁ t₂ v₁ v₂
        aux {T.Res .l (T.Id τ)} π₁ π₂ t₁ (S.Res l t₂) v₁ v₂ = aux π₁ π₂ t₁ t₂ v₁ v₂
        aux {T.Res .l (T.Addr τ)} π₁ π₂ t₁ (S.Res l .(S.#[ n ])) v₁ (l∈ls , n , is#[ .n ] , isV) = l∈ls , n , is#[ n ] , isV
        aux {T.Res .l (T.Addr τ)} π₁ π₂ t₁ (S.Res l .(S.#[ n ]ᴰ)) v₁ (l∈ls , n , is#[ .n ]ᴰ , isV) = l∈ls , n , is#[ n ]ᴰ , isV
        aux π₁ π₂ t₁ (S.label l⊑h t₂) v₁ v₂ = aux π₁ π₂ t₁ t₂ v₁ v₂
        aux π₁ π₂ t₁ (S.label∙ l⊑h t₂) v₁ ()
        aux π₁ π₂ t₁ (S.unlabel l⊑h t₂) v₁ v₂ = aux π₁ π₂ t₁ t₂ v₁ v₂
        aux π₁ π₂ t₁ (S.read x t₂) v₁ v₂ = aux π₁ π₂ t₁ t₂ v₁ v₂
        aux π₁ π₂ t₁ (S.write x t₂ t₃) v₁ (proj₁ , proj₂) = aux π₁ π₂ t₁ t₂ v₁ proj₁ , aux π₁ π₂ t₁ t₃ v₁ proj₂
        aux π₁ π₂ t₁ (S.write∙ x t₂ t₃) v₁ ()
        aux π₁ π₂ t₁ (S.new x t₂) v₁ v₂ = (proj₁ v₂) , (aux π₁ π₂ t₁ t₂ v₁ (proj₂ v₂))
        aux π₁ π₂ t₁ (S.new∙ x t₂) v₁ ()
        aux π₁ π₂ t₁ S.#[ x ] v₁ v₂ = tt
        aux π₁ π₂ t₁ S.#[ x ]ᴰ v₁ v₂ = tt
        aux π₁ π₂ t₁ (S.fork l⊑h t₂) v₁ (h∈ls , v₂) = h∈ls , aux π₁ π₂ t₁ t₂ v₁ v₂
        aux π₁ π₂ t₁ (S.fork∙ l⊑h t₂) v₁ ()
        aux π₁ π₂ t₁ (S.deepDup t₂) v₁ v₂ = aux π₁ π₂ t₁ t₂ v₁ v₂
        aux π₁ π₂ t₁ S.∙ v₁ ()

open import Relation.Nullary

valid-deepDupᵀ : ∀ {π τ ls} {{t : Term π τ}} {Ms : Memories ls} -> validᵀ Ms t -> validᵀ Ms (deepDupᵀ t)
valid-deepDupᵀ {{t}} {Ms} v = aux [] t v
  where aux : ∀ {τ π} -> (vs : Vars π) (t : Term π τ) -> validᵀ Ms t -> validᵀ Ms (dup-ufv vs t)
        aux vs S.（） v₁ = T.tt
        aux vs S.True v₁ = T.tt
        aux vs S.False v₁ = T.tt
        aux vs (S.Id t₁) v₁ = aux vs t₁ v₁
        aux vs (S.unId t₁) v₁ = aux vs t₁ v₁
        aux vs (S.Var τ∈π) v₁ with memberⱽ (∈ᴿ-∈ (T.τ∈π τ∈π)) vs
        ... | yes _ = T.tt
        ... | no _ = T.tt
        aux vs (S.Abs t₁) v₁ = aux (L₁.here S.∷ mapⱽ L₁.there vs) t₁ v₁
        aux vs (S.App t₁ t₂) (v₁ , v₂) = aux vs t₁ v₁ , aux vs t₂ v₂
        aux vs (S.If t₁ Then t₂ Else t₃) (v₁ , v₂ , v₃) = aux vs t₁ v₁ , aux vs t₂ v₂ , aux vs t₃ v₃
        aux vs (S.Return l t₁) v₁ = aux vs t₁ v₁
        aux vs (t₁ S.>>= t₂) (v₁ , v₂) = aux vs t₁ v₁ , aux vs t₂ v₂
        aux vs (S.Mac l t₁) v₁ = aux vs t₁ v₁
        aux {T.Res .l T.（）} vs (S.Res l t₁) v₁ = aux vs t₁ v₁
        aux {T.Res .l T.Bool} vs (S.Res l t₁) v₁ = aux vs t₁ v₁
        aux {T.Res .l (τ T.=> τ₁)} vs (S.Res l t₁) v₁ = aux vs t₁ v₁
        aux {T.Res .l₁ (T.Mac l τ)} vs (S.Res l₁ t₁) v₁ = aux vs t₁ v₁
        aux {T.Res .l₁ (T.Res l τ)} vs (S.Res l₁ t₁) v₁ = aux vs t₁ v₁
        aux {T.Res .l (T.Id τ)} vs (S.Res l t₁) v₁ = aux vs t₁ v₁
        aux {T.Res .l (T.Addr τ)} vs (S.Res l .(S.#[ v₂ ])) (v₁ , v₂ , is#[ .v₂ ] , v₄) = v₁ , v₂ , is#[ v₂ ]ᴰ , v₄
        aux {T.Res .l (T.Addr τ)} vs (S.Res l .(S.#[ v₂ ]ᴰ)) (v₁ , v₂ , is#[ .v₂ ]ᴰ , v₄) = v₁ , v₂ , is#[ v₂ ]ᴰ , v₄
        aux vs (S.label l⊑h t₁) v₁ = aux vs t₁ v₁
        aux vs (S.label∙ l⊑h t₁) ()
        aux vs (S.unlabel l⊑h t₁) v₁ = aux vs t₁ v₁
        aux vs (S.read x t₁) v₁ = aux vs t₁ v₁
        aux vs (S.write x t₁ t₂) (v₁ , v₂) = aux vs t₁ v₁ , aux vs t₂ v₂
        aux vs (S.write∙ x t₁ t₂) ()
        aux vs (S.new x t₁) (h∈ls , v₁) = h∈ls , aux vs t₁ v₁
        aux vs (S.new∙ x t₁) ()
        aux vs S.#[ x ] v₁ = T.tt
        aux vs S.#[ x ]ᴰ v₁ = T.tt
        aux vs (S.fork l⊑h t₁) (h∈ls , v₁) = h∈ls , aux vs t₁ v₁
        aux vs (S.fork∙ l⊑h t₁) ()
        aux vs (S.deepDup t₁) v₁ = v₁
        aux vs S.∙ ()

memberᴴ : ∀ {l ls τ π₁ π₂} {Ms : Memories ls} {Δ : Heap l π₂} {t : Term π₁ τ}
  -> (τ∈π : τ ∈⟨ l ⟩ᴿ π₂) -> validᴴ Ms Δ -> τ∈π ↦ t ∈ᴴ Δ -> validᵀ Ms t
memberᴴ ⟪ τ∈π ⟫ v t∈Δ = aux ⟪ ∈-∈ᴿ τ∈π ⟫ v t∈Δ
  where aux : ∀ {l ls τ π₁ π₂} {Ms : Memories ls} {Δ : Heap l π₂} {t : Term π₁ τ}
            -> (τ∈π : τ ∈⟨ l ⟩ π₂) -> validᴴ Ms Δ -> Memberᴴ (just t) τ∈π Δ -> validᵀ Ms t
        aux .(T.⟪ L₁.here ⟫) y S.here = proj₁ y
        aux ._ y (S.there z) = aux T.⟪ _ ⟫ (proj₂ y) z

updateᴴ : ∀ {l ls τ π π'} {Ms : Memories ls} {Δ₁ Δ₂ : Heap l π} {mt : Maybe (Term π' τ)} ->
            {τ∈π : τ ∈⟨ l ⟩ π} -> validᴴ Ms Δ₁ -> validᴹᵀ Ms mt -> Updateᴴ mt τ∈π Δ₁ Δ₂ -> validᴴ Ms Δ₂
updateᴴ x y S.here = y , proj₂ x
updateᴴ (proj₁ , proj₂) y (S.there z) = proj₁ , updateᴴ proj₂ y z

valid⇝ : ∀ {l ls τ} {s₁ s₂ : State l τ} {Ms : Memories ls} -> valid-state Ms s₁ -> s₁ ⇝ s₂ -> valid-state Ms s₂
valid⇝ (Δⱽ , (proj₁ , proj₂) , Sᵛ) (SS.App₁ {t₁ = t₁}) = (proj₂ , Δⱽ) , (valid-wkenᵀ {{t = t₁}} proj₁ _ , (T.tt , valid-wkenˢ Sᵛ _))
valid⇝ (Δⱽ , tⱽ , proj₁ , proj₂) (SS.App₂ {t = t} α∈π) = Δⱽ , (valid-subst {t₂ = t} proj₁ tⱽ , proj₂)
valid⇝ (Δⱽ , tⱽ , Sᵛ) (SS.Var₁ τ∈π t∈Δ ¬val rᴴ) = updateᴴ Δⱽ tt rᴴ , (memberᴴ τ∈π Δⱽ t∈Δ , (T.tt , Sᵛ))
valid⇝ (Δⱽ , tⱽ , Sᵛ)  (SS.Var₁' τ∈π v∈Δ val) = Δⱽ , memberᴴ τ∈π Δⱽ v∈Δ , Sᵛ
valid⇝ (Δⱽ , tⱽ , Sᵛ)  (SS.Var₂ τ∈π val uᴴ) = updateᴴ Δⱽ tⱽ uᴴ , (tⱽ , (proj₂ Sᵛ))
valid⇝ (Δⱽ , (proj₁ , proj₂ , proj₃) , Sᵛ) SS.If = Δⱽ , proj₁ , (proj₂ , proj₃) , Sᵛ
valid⇝ (Δⱽ , tⱽ , (proj₁ , proj₃) , proj₂) SS.IfTrue = Δⱽ , proj₁ , proj₂
valid⇝ (Δⱽ , tⱽ , (proj₁ , proj₃) , proj₂) SS.IfFalse = Δⱽ , proj₁ , proj₂
valid⇝ (Δⱽ , tⱽ , Sᵛ) SS.Return = Δⱽ , tⱽ , Sᵛ
valid⇝ (Δⱽ , (proj₁ , proj₂) , Sᵛ) SS.Bind₁ = Δⱽ , proj₁ , proj₂ , Sᵛ
valid⇝ (Δⱽ , tⱽ , proj₁ , proj₂) SS.Bind₂ = Δⱽ , (proj₁ , tⱽ) , proj₂
valid⇝ (Δⱽ , tⱽ , Sᵛ) (SS.Label' p) = Δⱽ , tⱽ , Sᵛ
valid⇝ (Δⱽ , () , Sᵛ) (SS.Label'∙ p)
valid⇝ (Δⱽ , tⱽ , Sᵛ) (SS.Unlabel₁ p) = Δⱽ , tⱽ , T.tt , Sᵛ
valid⇝ (Δⱽ , tⱽ , Sᵛ) (SS.Unlabel₂ p) = Δⱽ , tⱽ , proj₂ Sᵛ
valid⇝ (Δⱽ , tⱽ , Sᵛ) SS.UnId₁ = Δⱽ , tⱽ , T.tt , Sᵛ
valid⇝ (Δⱽ , tⱽ , Sᵛ) SS.UnId₂ = Δⱽ , tⱽ , proj₂ Sᵛ
valid⇝ () SS.Hole₁
valid⇝ (Δⱽ , (l∈ls , tⱽ) , Sᵛ) (SS.New₁ ¬var) = (tⱽ , Δⱽ) , ((l∈ls , T.tt) , valid-wkenˢ Sᵛ _)
valid⇝ (Δⱽ , () , Sᵛ) (SS.New∙₁ ¬var)
valid⇝ (Δⱽ , (tⱽ₁ , tⱽ₂) , Sᵛ) SS.Write₁ = (tⱽ₂ , Δⱽ) , (valid-wkenᵀ tⱽ₁ _) , (T.tt , (valid-wkenˢ Sᵛ _))
valid⇝ (Δⱽ , () , Sᵛ) SS.Write∙₁
valid⇝ (Δⱽ , tⱽ , Sᵛ) SS.Read₁ = Δⱽ , tⱽ , T.tt , Sᵛ

memberᴱ : ∀ {ls ls' l} {Ms : Memories ls'} {Γ : Heaps ls} {H : Heap∙ l} -> map-validᴴ Ms Γ -> l ↦ H ∈ᴱ Γ -> validᴴ∙ Ms H
memberᴱ (proj₁ , proj₂) S.here = proj₁
memberᴱ (proj₁ , proj₂) (S.there u₁) = memberᴱ proj₂ u₁

updateᴱ : ∀ {ls ls' l} {Ms : Memories ls'} {Γ Γ' : Heaps ls} {H : Heap∙ l} ->
                map-validᴴ Ms Γ ->  validᴴ∙ Ms H -> Γ' ≔ Γ [ l ↦ H ]ᴱ ->  map-validᴴ Ms Γ'
updateᴱ (proj₁ , proj₂) Hⱽ S.here = Hⱽ , proj₂
updateᴱ (proj₁ , proj₂) Hⱽ (S.there u₁) = proj₁ , updateᴱ proj₂ Hⱽ u₁

memberˢ : ∀ {l ls} {Ms : Memories ls} {M : Memory l} -> map-validᴹ Ms -> l ↦ M ∈ˢ Ms -> validᴹ M
memberˢ v S.here = proj₁ v
memberˢ v (S.there M∈Ms) = memberˢ (proj₂ v) M∈Ms

updateˢ : ∀ {l ls} {Ms₁ Ms₂ : Memories ls} {M : Memory l} -> validᴹ M -> map-validᴹ Ms₁ -> Ms₂ ≔ Ms₁ [ l ↦ M ]ˢ -> map-validᴹ Ms₂
updateˢ v₁ v₂ S.here = v₁ , proj₂ v₂
updateˢ v₁ (proj₁ , proj₂) (S.there u₁) = proj₁ , updateˢ v₁ proj₂ u₁

valid-newᴹ : ∀ {l τ} {M : Memory l} (c : Cell l τ) -> validᴹ M -> validᴹ (newᴹ c M)
valid-newᴹ {M = S.[]} c v = T.tt
valid-newᴹ {M = cᴸ S.∷ M} c v = valid-newᴹ {M = M} c v
valid-newᴹ {M = S.∙} c ()

valid-writeᴹ : ∀ {n l τ} {c : Cell l τ} {M₁ M₂ : Memory l} -> validᴹ M₁ -> M₂ ≔ M₁ [ n ↦ c ]ᴹ -> validᴹ M₂
valid-writeᴹ v S.here = v
valid-writeᴹ v (S.there u) = valid-writeᴹ v u

newᴹ-⊆ᴹ : ∀ {l τ} {c : Cell l τ} {M : Memory l} -> M ⊆ᴹ newᴹ c M
newᴹ-⊆ᴹ {M = S.[]} = nil
newᴹ-⊆ᴹ {M = cᴸ S.∷ M} = cons newᴹ-⊆ᴹ
newᴹ-⊆ᴹ {M = S.∙} = ∙

newᴹ-⊆ˢ : ∀ {ls l τ} {M : Memory l} {c : Cell l τ} {Ms₁ Ms₂ : Memories ls} -> l ↦ M ∈ˢ Ms₁ -> Ms₂ ≔ Ms₁ [ l ↦ newᴹ c M ]ˢ -> Ms₁ ⊆ˢ Ms₂
newᴹ-⊆ˢ S.here S.here = cons newᴹ-⊆ᴹ refl-⊆ˢ
newᴹ-⊆ˢ S.here (S.there {u = u} y) = ⊥-elim (∈-not-unique (updateˢ-∈ y) u)
newᴹ-⊆ˢ (S.there {u = u} m) S.here = ⊥-elim (∈-not-unique (memberˢ-∈ m) u)
newᴹ-⊆ˢ (S.there m) (S.there u₁) = cons refl-⊆ᴹ (newᴹ-⊆ˢ m u₁)

writeᴹ-⊆ᴹ : ∀ {l τ n} {M₁ M₂ : Memory l} {c : Cell l τ} -> M₂ ≔ M₁ [ n ↦ c ]ᴹ -> M₁ ⊆ᴹ M₂
writeᴹ-⊆ᴹ S.here = cons refl-⊆ᴹ
writeᴹ-⊆ᴹ (S.there u) = cons (writeᴹ-⊆ᴹ u)

writeᴹ-⊆ˢ : ∀ {ls l} {M₁ M₂ : Memory l} {Ms₁ Ms₂ : Memories ls} ->
            l ↦ M₁ ∈ˢ Ms₁ -> Ms₂ ≔ Ms₁ [ l ↦ M₂ ]ˢ -> M₁ ⊆ᴹ M₂ -> Ms₁ ⊆ˢ Ms₂
writeᴹ-⊆ˢ S.here S.here M₁⊆M₂ = cons M₁⊆M₂ refl-⊆ˢ
writeᴹ-⊆ˢ S.here (S.there {u = u} y) M₁⊆M₂ = ⊥-elim (∈-not-unique (updateˢ-∈ y) u)
writeᴹ-⊆ˢ (S.there {u = u} l∈Ms) S.here M₁⊆M₂ = ⊥-elim (∈-not-unique (memberˢ-∈ l∈Ms) u)
writeᴹ-⊆ˢ (S.there l∈Ms) (S.there u₁) M₁⊆M₂ = cons refl-⊆ᴹ (writeᴹ-⊆ˢ l∈Ms u₁ M₁⊆M₂)

newᴹ-validAddr : ∀ {l τ} {M : Memory l} (c : Cell l τ) -> validᴹ M -> ValidAddr (newᴹ c M) (lengthᴹ M) τ
newᴹ-validAddr {M = S.[]} c v = here
newᴹ-validAddr {M = cᴸ S.∷ M} c v = there (newᴹ-validAddr {M = M} c v)
newᴹ-validAddr {M = S.∙} c ()

valid⟼ : ∀ {ls τ l} {p₁ p₂ : Program l ls τ} -> validᴾ p₁ -> p₁ ⟼ p₂ -> validᴾ p₂
valid⟼ (proj₁ , proj₂ , proj₃ , proj₄) (SS.Pure l∈Γ step uᴹ) with valid⇝ ((memberᴱ proj₂ l∈Γ) , (proj₃ , proj₄)) step
... | Δ₂ⱽ  , t₂ⱽ , S₂ⱽ = proj₁ , (updateᴱ proj₂ Δ₂ⱽ uᴹ , (t₂ⱽ , S₂ⱽ))
valid⟼ (Msⱽ , Γⱽ , (H∈ls , tⱽ) , Sⱽ) (SS.New {Γ = Γ} {M = M₁} {τ∈π = τ∈π} {l⊑H = l⊑H} H∈Ms uˢ) with newᴹ-⊆ˢ H∈Ms uˢ | memberˢ Msⱽ H∈Ms
... | Ms₁⊆Ms₂ | M₁ⱽ with valid-newᴹ {M = M₁} S.∥ l⊑H , τ∈π  ∥ M₁ⱽ
... | M₂ⱽ with newᴹ-validAddr {M = M₁} S.∥ l⊑H , τ∈π  ∥ M₁ⱽ
... | r rewrite lookupˢ-updateˢ-≡ H∈ls uˢ
  =  updateˢ M₂ⱽ Msⱽ uˢ , (map-wkenᴴ {Γ = Γ} Ms₁⊆Ms₂ Γⱽ , ((H∈ls , (lengthᴹ M₁) , (is#[ _ ] , r)) , wkenˢ Ms₁⊆Ms₂ Sⱽ))
valid⟼ (Msⱽ , Γⱽ , () , Sⱽ) SS.New∙
valid⟼ (Msⱽ , Γⱽ , tⱽ , Sⱽ) (SS.Write₂ {Γ = Γ} H∈Ms uᴹ uˢ) with writeᴹ-⊆ˢ H∈Ms uˢ (writeᴹ-⊆ᴹ uᴹ)
... | Ms₁⊆Ms₂ = (updateˢ (valid-writeᴹ (memberˢ Msⱽ H∈Ms) uᴹ) Msⱽ uˢ) , ((map-wkenᴴ {Γ = Γ} Ms₁⊆Ms₂ Γⱽ) , (tt , wkenˢ Ms₁⊆Ms₂ (proj₂ Sⱽ)))
valid⟼ (Msⱽ , Γⱽ , tⱽ , Sⱽ) (SS.Writeᴰ₂ {Γ = Γ} H∈Ms uᴹ uˢ) with writeᴹ-⊆ˢ H∈Ms uˢ (writeᴹ-⊆ᴹ uᴹ)
... | Ms₁⊆Ms₂ = (updateˢ (valid-writeᴹ (memberˢ Msⱽ H∈Ms) uᴹ) Msⱽ uˢ) , ((map-wkenᴴ {Γ = Γ} Ms₁⊆Ms₂ Γⱽ) , (tt , wkenˢ Ms₁⊆Ms₂ (proj₂ Sⱽ)))
valid⟼ (Msⱽ , Γⱽ , tⱽ , () , proj₂) SS.Write∙₂
valid⟼ (Msⱽ , Γⱽ , tⱽ , Sⱽ) (SS.Read₂ l∈Γ n∈M) = Msⱽ , Γⱽ , tt , proj₂ Sⱽ
valid⟼ (Msⱽ , Γⱽ , tⱽ , Sⱽ) (SS.Readᴰ₂ L∈Ms n∈M) = Msⱽ , Γⱽ , tt , proj₂ Sⱽ
valid⟼ (Msⱽ , Γⱽ , tⱽ , Sⱽ) (SS.DeepDup₁ ¬var l∈Γ uᴱ) = Msⱽ , updateᴱ Γⱽ (tⱽ , (memberᴱ Γⱽ l∈Γ)) uᴱ , tt , valid-wkenˢ Sⱽ _
valid⟼ (Msⱽ , Γⱽ , tt , Sⱽ) (SS.DeepDup₂ {t = t} τ∈π L∈Γ t∈Δ l∈Γ uᴱ) with memberᴱ Γⱽ l∈Γ | memberᴱ Γⱽ L∈Γ
... | Δˡⱽ | Δᴸⱽ  with memberᴴ τ∈π Δᴸⱽ t∈Δ
... | tⱽ = Msⱽ , updateᴱ Γⱽ (valid-deepDupᵀ {{t = t}} tⱽ , Δˡⱽ) uᴱ , tt , valid-wkenˢ Sⱽ _
valid⟼ (Msⱽ , Γⱽ , ()) SS.Hole

⟼-⊆ˢ : ∀ {ls τ l} {p₁ p₂ : Program l ls τ} -> p₁ ⟼ p₂ -> Ms p₁ ⊆ˢ Ms p₂
⟼-⊆ˢ (SS.Pure l∈Γ step uᴹ) = refl-⊆ˢ
⟼-⊆ˢ (SS.New H∈Ms uᴹ) = newᴹ-⊆ˢ H∈Ms uᴹ
⟼-⊆ˢ SS.New∙ = refl-⊆ˢ
⟼-⊆ˢ (SS.Write₂ H∈Ms uᴹ uˢ) = writeᴹ-⊆ˢ H∈Ms uˢ (writeᴹ-⊆ᴹ uᴹ)
⟼-⊆ˢ (SS.Writeᴰ₂ H∈Ms uᴹ uˢ) = writeᴹ-⊆ˢ H∈Ms uˢ (writeᴹ-⊆ᴹ uᴹ)
⟼-⊆ˢ SS.Write∙₂ = refl-⊆ˢ
⟼-⊆ˢ (SS.Read₂ l∈Γ n∈M) = refl-⊆ˢ
⟼-⊆ˢ (SS.Readᴰ₂ L∈Ms n∈M) = refl-⊆ˢ
⟼-⊆ˢ (SS.DeepDup₁ ¬var l∈Γ uᴱ) = refl-⊆ˢ
⟼-⊆ˢ (SS.DeepDup₂ τ∈π L∈Γ t∈Δ l∈Γ uᴱ) = refl-⊆ˢ
⟼-⊆ˢ SS.Hole = refl-⊆ˢ

--------------------------------------------------------------------------------

updateᴹ-valid : ∀ {l τ n} {M : Memory l} -> (c : Cell l τ) -> ValidAddr M n τ -> ∃ (λ M' -> M' ≔ M [ n ↦ c ]ᴹ)
updateᴹ-valid {M = S.[]} c ()
updateᴹ-valid {M = cᴸ S.∷ M} c here = _ , here
updateᴹ-valid {M = cᴸ S.∷ M} c (there isVA) = P.map (_∷_ _) there (updateᴹ-valid c isVA)
updateᴹ-valid {M = S.∙} c  ()

updataˢ-valid : ∀ {l ls} {M : Memory l} {Ms : Memories ls} -> l ∈ ls -> ∃ (λ Ms' -> Ms' ≔ Ms [ l ↦ M ]ˢ)
updataˢ-valid {Ms = M' ∷ Ms} T.here = _ ∷ Ms , here
updataˢ-valid {Ms = M' ∷ Ms} (T.there l∈ls) = P.map (_∷_ M') there (updataˢ-valid l∈ls)
