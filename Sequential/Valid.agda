import Lattice as L

module Sequential.Valid (𝓛 : L.Lattice) where

import Types as T hiding (wken-∈)
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
-- TODO the problem with this definition is that we use π in Env H π.
-- In our definition of Γ₁ ⊆ᴴ Γ₂ the environment may change (Δ₁ ⊆ Δ₂),
-- which means that Δ₂ : Env l π' such that π ⊆ π'.
-- Possible fixes:
-- 1) We could change the definition of Γ₁ ⊆ Γ₂ not to allow (Δ₁ ⊆ Δ₂), but keeping the same Δ
--    I think that this would not work out with the context rules that extends Δ, such as those in Pure
-- 2) Split memories and heap in two different mappings (like in the paper):
-- this would probably simplify the valid-preservation proof for pure (the memories remain all visible since
-- they are in a different mapping), the definition of validity for new (and write and read)
-- as they would not mention contexs π.
Validᵀ {π = π} Γ (S.new {h = H} x t) = Σ (Memory H × Env H π) (λ x -> H ↦ ⟨ proj₁ x , proj₂ x ⟩ ∈ᴴ Γ × validᵀ Γ t)
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
validᴴ S.[] = ⊤
validᴴ (x S.∷ Γ) = validᴴ₂ (x ∷ Γ) x × validᴴ Γ

valid-state : ∀ {l ls τ} -> Heaps ls -> State l τ -> Set
valid-state Γ (S.mkP Δ t S) = validᴱ Γ Δ × validᵀ Γ t × validˢ Γ S
valid-state _ S.∙ = ⊥

validᴾ : ∀ {l ls τ} -> Program l ls τ -> Set
validᴾ (S.mkP Γ t S ) = validᴴ Γ × (validᵀ Γ t) × (validˢ Γ S)
validᴾ S.∙ = ⊥

valid-𝓛 : (ls : List Label) -> Set
valid-𝓛 [] = ⊤
valid-𝓛 (l ∷ ls) = Unique l ls × valid-𝓛 ls

Γ₀ : {ls : List Label} {{us : valid-𝓛 ls}} -> Heaps ls
Γ₀ {[]} {{_}} = []
Γ₀ {l ∷ ls} {{u , us}} = ⟨ [] , [] ⟩ ∷ Γ₀

--------------------------------------------------------------------------------

open import Relation.Binary as B
open B.DecTotalOrder Data.Nat.decTotalOrder hiding (_≤_) renaming (trans to trans-≤ ; refl to refl-≤)


open import Function

-- TODO might need more assuptions in cons, such both are valid (in Rule Var₂)
data _⊆ᴱ_ {l} : ∀ {π₁ π₂} -> Env l π₁ -> Env l π₂ -> Set where
  nil : [] ⊆ᴱ []
  cons : ∀ {π τ} {mt₁ mt₂ : Maybe (Term π τ)} {Δ₁ Δ₂ : Env l π} -> Δ₁ ⊆ᴱ Δ₂ -> (mt₁ ∷ Δ₁) ⊆ᴱ (mt₂ ∷ Δ₂)
  drop : ∀ {π τ} {mt : Maybe (Term π τ)} {Δ₁ Δ₂ : Env l π} -> Δ₁ ⊆ᴱ Δ₂ -> Δ₁ ⊆ᴱ (mt ∷ Δ₂ )
  ∙ : ∀ {π} -> (∙ {{π}}) ⊆ᴱ (∙ {{π}})

data _⊆'ᴴ_ {l} : Heap l -> Heap l -> Set where
 ⟨_,_⟩  : ∀ {π₁ π₂} {M₁ M₂ : Memory l} {Δ₁ : Env l π₁} {Δ₂ : Env l π₂} ->
         lengthᴹ M₁ ≤ lengthᴹ M₂ -> Δ₁ ⊆ᴱ Δ₂ -> ⟨ M₁ , Δ₁ ⟩ ⊆'ᴴ ⟨ M₂ , Δ₂ ⟩
 ∙ : ∙ ⊆'ᴴ ∙

data _⊆ᴴ_ : ∀ {ls₁ ls₂} -> Heaps ls₁ -> Heaps ls₂ -> Set where
  nil : [] ⊆ᴴ []
  cons : ∀ {ls₁ ls₂ l} {u₁ : Unique l ls₁} {u₂ : Unique l ls₂} {Γ₁ : Heaps ls₁} {Γ₂ : Heaps ls₂} {H₁ H₂ : Heap l}
         -> H₁ ⊆'ᴴ H₂ -> Γ₁ ⊆ᴴ Γ₂ -> (H₁ ∷ Γ₁) ⊆ᴴ (H₂ ∷ Γ₂)
  drop : ∀ {ls₁ ls₂ l} {u₂ : Unique l ls₂} {Γ₁ : Heaps ls₁} {Γ₂ : Heaps ls₂} {H : Heap l}
           -> Γ₁ ⊆ᴴ Γ₂ -> Γ₁ ⊆ᴴ (H ∷ Γ₂)

refl-⊆ᴱ : ∀ {π l} {Δ : Env l π} -> Δ ⊆ᴱ Δ
refl-⊆ᴱ {Δ = S.[]} = nil
refl-⊆ᴱ {Δ = t S.∷ Δ} = cons refl-⊆ᴱ
refl-⊆ᴱ {Δ = S.∙} = ∙

refl-⊆'ᴴ : ∀ {l} {H : Heap l} -> H ⊆'ᴴ H
refl-⊆'ᴴ {H = S.⟨ x , x₁ ⟩} = ⟨ refl-≤ , refl-⊆ᴱ ⟩
refl-⊆'ᴴ {H = S.∙} = ∙

refl-⊆ᴴ : ∀ {ls} {Γ : Heaps ls} -> Γ ⊆ᴴ Γ
refl-⊆ᴴ {Γ = S.[]} = nil
refl-⊆ᴴ {Γ = x S.∷ Γ} = cons refl-⊆'ᴴ refl-⊆ᴴ

open import Function

wken-Addr : ∀ {ls₁ ls₂ l} {Γ₁ : Heaps ls₁} {Γ₂ : Heaps ls₂} {n : ℕ} ->
              Γ₁ ⊆ᴴ Γ₂ -> Σ (l ∈ ls₁) (λ l∈ls₁ -> validAddr (lookupᴹ l∈ls₁ Γ₁) n) -> Σ (l ∈ ls₂) (λ l∈ls₂ -> validAddr (lookupᴹ l∈ls₂ Γ₂) n)
wken-Addr nil (() , proj₂)
wken-Addr (cons ⟨ x , x₁ ⟩ Γ₁⊆Γ₂) (T.here , proj₂) = here , trans-≤ proj₂ x
wken-Addr (cons ∙ Γ₁⊆Γ₂) (T.here , proj₂) = here , proj₂
wken-Addr (cons x Γ₁⊆Γ₂) (T.there proj₁ , proj₂) = P.map there id (wken-Addr Γ₁⊆Γ₂ (proj₁ , proj₂))
wken-Addr (drop Γ₁⊆Γ₂) (proj₁ , proj₂) = P.map there id (wken-Addr Γ₁⊆Γ₂ (proj₁ , proj₂))

wken-∈ : ∀ {l ls₁ ls₂} {Γ₁ : Heaps ls₁} {Γ₂ : Heaps ls₂}-> l ∈ ls₁ -> Γ₁ ⊆ᴴ Γ₂ -> l ∈ ls₂
wken-∈ T.here (cons x Γ₁⊆Γ₂) = here
wken-∈ T.here (drop Γ₁⊆Γ₂) = there (wken-∈ here Γ₁⊆Γ₂)
wken-∈ (T.there l∈ls) (cons x Γ₁⊆Γ₂) = there (wken-∈ l∈ls Γ₁⊆Γ₂)
wken-∈ (T.there l∈ls) (drop Γ₁⊆Γ₂) = there (wken-∈ (there l∈ls) Γ₁⊆Γ₂)

wkenᵁ : ∀ {l ls₁ ls₂} {Γ₁ : Heaps ls₁} {Γ₂ : Heaps ls₂} {H₁ : Heap l}
      -> l ↦ H₁ ∈ᴴ Γ₁ -> Γ₁ ⊆ᴴ Γ₂ -> Σ (Heap l) (λ H₂ -> H₁ ⊆'ᴴ H₂ × l ↦ H₂ ∈ᴴ Γ₂)
wkenᵁ S.here (cons x Γ₁⊆Γ₂) = _ , (x , here)
wkenᵁ S.here (drop Γ₁⊆Γ₂) = P.map id (P.map id there) (wkenᵁ here Γ₁⊆Γ₂)
wkenᵁ (S.there x) (cons x₁ Γ₁⊆Γ₂) = P.map id (P.map id there) (wkenᵁ x Γ₁⊆Γ₂)
wkenᵁ (S.there x) (drop Γ₁⊆Γ₂) = P.map id (P.map id there) (wkenᵁ (there x) Γ₁⊆Γ₂)

wkenᵀ : ∀ {π τ ls₁ ls₂} {Γ₁ : Heaps ls₁} {Γ₂ : Heaps ls₂} -> Γ₁ ⊆ᴴ Γ₂ -> (t : Term π τ) -> validᵀ Γ₁ t -> validᵀ Γ₂ t
wkenᵀ Γ₁⊆Γ₂ S.（） ok = T.tt
wkenᵀ Γ₁⊆Γ₂ S.True ok = T.tt
wkenᵀ Γ₁⊆Γ₂ S.False ok = T.tt
wkenᵀ Γ₁⊆Γ₂ (S.Id t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
wkenᵀ Γ₁⊆Γ₂ (S.unId t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
wkenᵀ Γ₁⊆Γ₂ (S.Var τ∈π) ok = T.tt
wkenᵀ Γ₁⊆Γ₂ (S.Abs t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
wkenᵀ Γ₁⊆Γ₂ (S.App t t₁) (proj₁ , proj₂) = (wkenᵀ Γ₁⊆Γ₂ t proj₁) , (wkenᵀ Γ₁⊆Γ₂ t₁ proj₂)
wkenᵀ Γ₁⊆Γ₂ (S.If t Then t₁ Else t₂) (proj₁ , proj₂ , proj₃) = (wkenᵀ Γ₁⊆Γ₂ t proj₁) , ((wkenᵀ Γ₁⊆Γ₂ t₁ proj₂) , (wkenᵀ Γ₁⊆Γ₂ t₂ proj₃))
wkenᵀ Γ₁⊆Γ₂ (S.Return l₁ t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
wkenᵀ Γ₁⊆Γ₂ (t S.>>= t₁) (proj₁ , proj₂) = (wkenᵀ Γ₁⊆Γ₂ t proj₁) , (wkenᵀ Γ₁⊆Γ₂ t₁ proj₂)
wkenᵀ Γ₁⊆Γ₂ (S.Mac l₁ t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
wkenᵀ {τ = T.Res .l₁ T.（）} Γ₁⊆Γ₂ (S.Res l₁ t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
wkenᵀ {τ = T.Res .l₁ T.Bool} Γ₁⊆Γ₂ (S.Res l₁ t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
wkenᵀ {τ = T.Res .l₁ (τ T.=> τ₁)} Γ₁⊆Γ₂ (S.Res l₁ t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
wkenᵀ {τ = T.Res .l₂ (T.Mac l₁ τ)} Γ₁⊆Γ₂ (S.Res l₂ t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
wkenᵀ {τ = T.Res .l₂ (T.Res l₁ τ)} Γ₁⊆Γ₂ (S.Res l₂ t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
wkenᵀ {τ = T.Res .l₁ (T.Id τ)} Γ₁⊆Γ₂ (S.Res l₁ t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
wkenᵀ {τ = T.Res .l₁ T.Addr} Γ₁⊆Γ₂ (S.Res l₁ (S.unId t)) ok = wkenᵀ Γ₁⊆Γ₂ t ok
wkenᵀ {τ = T.Res .l₁ T.Addr} Γ₁⊆Γ₂ (S.Res l₁ (S.Var τ∈π)) ok = tt
wkenᵀ {τ = T.Res .l₁ T.Addr} Γ₁⊆Γ₂ (S.Res l₁ (S.App t t₁))  (proj₁ , proj₂) = (wkenᵀ Γ₁⊆Γ₂ t proj₁) , (wkenᵀ Γ₁⊆Γ₂ t₁ proj₂)
wkenᵀ {τ = T.Res .l₁ T.Addr} Γ₁⊆Γ₂ (S.Res l₁ (S.If t Then t₁ Else t₂))
  (proj₁ , proj₂ , proj₃) = (wkenᵀ Γ₁⊆Γ₂ t proj₁) , ((wkenᵀ Γ₁⊆Γ₂ t₁ proj₂) , (wkenᵀ Γ₁⊆Γ₂ t₂ proj₃))
wkenᵀ {τ = T.Res .l₁ T.Addr} Γ₁⊆Γ₂ (S.Res l₁ S.#[ x ]) v = wken-Addr Γ₁⊆Γ₂ v
wkenᵀ {τ = T.Res .l₁ T.Addr} Γ₁⊆Γ₂ (S.Res l₁ S.#[ x ]ᴰ) v = wken-Addr Γ₁⊆Γ₂ v
wkenᵀ {τ = T.Res .l₁ T.Addr} Γ₁⊆Γ₂ (S.Res l₁ (S.deepDup t)) ok = wkenᵀ Γ₁⊆Γ₂ t ok
wkenᵀ {τ = T.Res .l₁ T.Addr} Γ₁⊆Γ₂ (S.Res l₁ S.∙) ()
wkenᵀ Γ₁⊆Γ₂ (S.label l⊑h t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
wkenᵀ Γ₁⊆Γ₂ (S.label∙ l⊑h t) ()
wkenᵀ Γ₁⊆Γ₂ (S.unlabel l⊑h t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
wkenᵀ Γ₁⊆Γ₂ (S.read x t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
wkenᵀ Γ₁⊆Γ₂ (S.write x t t₁) (proj₁ , proj₂) = (wkenᵀ Γ₁⊆Γ₂ t proj₁) , (wkenᵀ Γ₁⊆Γ₂ t₁ proj₂)
wkenᵀ Γ₁⊆Γ₂ (S.write∙ x t t₁) ()
wkenᵀ Γ₁⊆Γ₂ (S.new x t) (ok₁ , ok₂ , ok₃) with wkenᵁ ok₂ Γ₁⊆Γ₂
wkenᵀ Γ₁⊆Γ₂ (S.new x₂ t) (ok₁ , ok₂ , ok₃) | ⟨ M' , Δ' ⟩ , ⟨ x , x₁ ⟩ , H∈Γ = (M' , {!Δ'!}) , ( {!H∈Γ!} , wkenᵀ Γ₁⊆Γ₂ t ok₃)
wkenᵀ Γ₁⊆Γ₂ (S.new∙ x t) ()
wkenᵀ Γ₁⊆Γ₂ S.#[ x ] ok = T.tt
wkenᵀ Γ₁⊆Γ₂ S.#[ x ]ᴰ ok = T.tt
wkenᵀ Γ₁⊆Γ₂ (S.fork l⊑h t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
wkenᵀ Γ₁⊆Γ₂ (S.fork∙ l⊑h t) ()
wkenᵀ Γ₁⊆Γ₂ (S.deepDup t) ok = wkenᵀ Γ₁⊆Γ₂ t ok
wkenᵀ Γ₁⊆Γ₂ S.∙ ()

wkenᴱ : ∀ {l π ls₁ ls₂} {Δ : Env l π} {Γ₁ : Heaps ls₁} {Γ₂ : Heaps ls₂} -> Γ₁ ⊆ᴴ Γ₂ -> validᴱ Γ₁ Δ -> validᴱ Γ₂ Δ
wkenᴱ {Δ = S.[]} Γ₁⊆Γ₂ Δᴱ = tt
wkenᴱ {Δ = just t S.∷ Δ} Γ₁⊆Γ₂  (tⱽ , Δᴱ) = wkenᵀ Γ₁⊆Γ₂ t tⱽ , wkenᴱ {Δ = Δ} Γ₁⊆Γ₂ Δᴱ
wkenᴱ {Δ = nothing S.∷ Δ} Γ₁⊆Γ₂  Δᴱ = wkenᴱ {Δ = Δ} Γ₁⊆Γ₂  Δᴱ
wkenᴱ {Δ = S.∙} _ ()

-- wkenᴹ : ∀ {l} {M₁ M₂ : Memory l} -> lengthᴹ M₁ ≤ lengthᴹ M₂ -> validᴹ M₁ -> validᴹ M₂
-- wkenᴹ {M₂ = S.[]} x x₁ = tt
-- wkenᴹ {M₂ = cᴸ S.∷ M₂} x x₁ = {!!}
-- wkenᴹ {M₁ = S.[]} {S.∙} z≤n x₁ = {!!}  -- No! :-(
-- wkenᴹ {M₁ = cᴸ S.∷ M₁} {S.∙} () x₁
-- wkenᴹ {M₁ = S.∙} {S.∙} z≤n ()

wkenᴴ₂ : ∀ {l ls₁ ls₂} {Γ₁ : Heaps ls₁} {Γ₂ : Heaps ls₂} {H : Heap l} -> Γ₁ ⊆ᴴ Γ₂ -> validᴴ₂ Γ₁ H -> validᴴ₂ Γ₂ H
wkenᴴ₂ {H = S.⟨ M , Δ ⟩} Γ₁⊆Γ₂ (a , b) = a , wkenᴱ {Δ = Δ} Γ₁⊆Γ₂ b
wkenᴴ₂ {H = S.∙} _ ()

-- wkenᴴ₂' : ∀ {l ls₁ ls₂} {Γ₁ : Heaps ls₁} {Γ₂ : Heaps ls₂} {H₁ H₂ : Heap l} -> Γ₁ ⊆ᴴ Γ₂ -> H₁ ⊆'ᴴ H₂ -> validᴴ₂ Γ₁ H₁ -> validᴴ₂ Γ₂ H₂
-- wkenᴴ₂' a ⟨ x , x₁ ⟩ (proj₁ , proj₂) = {!!} , {!!}
-- wkenᴴ₂' a ∙ ()
-- {H = S.⟨ M , Δ ⟩} Γ₁⊆Γ₂ (a , b) = a , wkenᴱ {Δ = Δ} Γ₁⊆Γ₂ b
-- wkenᴴ₂' {H = S.∙} _ ()

-- wkenᴴ : ∀ {ls₁ ls₂} {Γ₁ : Heaps ls₁} {Γ₂ : Heaps ls₂} -> Γ₁ ⊆ᴴ Γ₂ -> validᴴ Γ₁ -> validᴴ Γ₂
-- wkenᴴ nil x = tt
-- wkenᴴ (cons x x₁) (proj₁ , proj₂) = (wkenᴴ₂' (cons x x₁) x proj₁) , wkenᴴ x₁ proj₂
-- wkenᴴ {Γ₁ = Γ₁} (drop x) x₁ = {!!} , (wkenᴴ x x₁)

validᴴ₀ : ∀ {ls : List Label} {{us : valid-𝓛 ls}} -> validᴴ {ls} Γ₀
validᴴ₀ {T.[]} = tt
validᴴ₀ {x T.∷ ls} = (tt , tt) , validᴴ₀

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

valid-memberᴴ : ∀ {l ls} {Γ : Heaps ls} {H : Heap l} -> validᴴ Γ -> l ↦ H ∈ᴴ Γ -> validᴴ₂ Γ H
valid-memberᴴ (proj₁ , proj₂) S.here = proj₁
valid-memberᴴ (proj₁ , proj₂) (S.there l∈Γ) = wkenᴴ₂ (drop refl-⊆ᴴ) (valid-memberᴴ proj₂ l∈Γ)

valid-memberᴱ : ∀ {l τ π₁ π₂ ls} {Γ : Heaps ls} {Δ : Env l π₁} {t : Term π₂ τ} {x : τ ∈⟨ l ⟩ᴿ π₁} -> validᴱ Γ Δ -> x ↦ t ∈ᴱ Δ -> validᵀ Γ t
valid-memberᴱ {x = T.⟪ τ∈π ⟫} = aux
  where aux : ∀ {l τ π₁ π₂ ls} {Γ : Heaps ls} {Δ : Env l π₁} {t : Term π₂ τ} {x : τ ∈⟨ l ⟩ π₁} -> validᴱ Γ Δ -> Memberᴱ (just t) x Δ -> validᵀ Γ t
        aux (proj₁ , proj₂) S.here = proj₁
        aux {Δ = just x S.∷ Δ} (_ , Δⱽ) (S.there t∈Δ) = aux Δⱽ t∈Δ
        aux {Δ = nothing S.∷ Δ} Δⱽ (S.there t∈Δ) = aux Δⱽ t∈Δ

valid-newᴹ : ∀ {l τ} (c : Cell l τ) (M : Memory l) -> validᴹ M -> validᴹ (newᴹ c M) × (lengthᴹ M ≤ lengthᴹ (newᴹ c M))
valid-newᴹ c S.[] ok-M = tt , z≤n
valid-newᴹ c (cᴸ S.∷ M) ok-M = P.map id s≤s (valid-newᴹ c M ok-M)
valid-newᴹ c S.∙ ()

valid-writeᴹ : ∀ {l τ} {c : Cell l τ} {M M' : Memory l} {n} -> M' ≔ M [ n ↦ c ]ᴹ -> validᴹ M -> validᴹ M' × lengthᴹ M ≤ lengthᴹ M'
valid-writeᴹ {M = _ ∷ M} S.here Mⱽ = Mⱽ , s≤s refl-≤
valid-writeᴹ (S.there u) Mⱽ = P.map id s≤s (valid-writeᴹ u Mⱽ)

valid-new-Addr : ∀ {l ls τ π} {Γ Γ' : Heaps ls} {Δ : Env l π} {M : Memory l} -> validᴹ M -> (c : Cell l τ) ->
              (uᴴ : Γ' ≔ Γ [ l ↦ ⟨ newᴹ c M , Δ ⟩ ]ᴴ) -> validAddr (lookupᴹ (update-∈ uᴴ) Γ') (lengthᴹ M)
valid-new-Addr {M = M} Mᵛ c (S.there uᴴ) = valid-new-Addr {M = M} Mᵛ c uᴴ
valid-new-Addr {M = M} Mᵛ c S.here = aux {c = c} {M = M} Mᵛ
 where aux : ∀ {l τ} {c : Cell l τ} {M : Memory l} -> validᴹ M -> lengthᴹ M < lengthᴹ (newᴹ c M)
       aux {M = S.[]} M≠∙ = s≤s z≤n
       aux {M = cᴸ S.∷ M} M≠∙ = s≤s (aux {M = M} M≠∙)
       aux {M = S.∙} ()


update-valid-Addr : ∀ {l} {M₁ M₂ : Memory l} {n : ℕ} -> validAddr M₁ n ->
                    validᴹ M₁ -> validᴹ M₂ -> lengthᴹ M₁ ≤ lengthᴹ M₂ -> validAddr M₂ n
update-valid-Addr {_} {M₁} {M₂} aⱽ Mⱽ₁ Mⱽ₂ M₁≤M₂ = trans-≤ aⱽ M₁≤M₂

newᴹ-≤ : ∀ {l τ} (M : Memory l) (c : Cell l τ) -> lengthᴹ M ≤ lengthᴹ (newᴹ c M)
newᴹ-≤ S.[] c = z≤n
newᴹ-≤ (cᴸ S.∷ M) c = s≤s (newᴹ-≤ M c)
newᴹ-≤ S.∙ c = refl-≤

newᴴ-≤ : ∀ {l π ls} {Γ₁ Γ₂ : Heaps ls} {M₁ M₂ : Memory l} {Δ : Env l π} -> l ↦ ⟨ M₁ , Δ ⟩ ∈ᴴ Γ₁ -> Γ₂ ≔ Γ₁ [ l ↦ ⟨ M₂ , Δ ⟩ ]ᴴ ->
           (lengthᴹ M₁) ≤ (lengthᴹ M₂) ->
          (∀ {l} -> (l∈ls : l ∈ ls) ->
             lengthᴹ (lookupᴹ l∈ls Γ₁) ≤ lengthᴹ (lookupᴹ l∈ls Γ₂))
newᴴ-≤ S.here S.here M₁≤M₂ T.here = M₁≤M₂
newᴴ-≤ S.here S.here _ (T.there l∈ls) = refl-≤
newᴴ-≤ {l} S.here (S.there {u = u} y) = ⊥-elim (∈-not-unique (update-∈ y) u)
newᴴ-≤ (S.there {u = u} x) S.here = ⊥-elim (∈-not-unique (member-∈ x) u)
newᴴ-≤ {Γ₁ = S.⟨ x , x₁ ⟩ S.∷ Γ₁} (S.there x₂) (S.there y) _ T.here = refl-≤
newᴴ-≤ {Γ₁ = S.∙ S.∷ Γ₁} (S.there x) (S.there y) _ T.here = refl-≤
newᴴ-≤ (S.there x) (S.there y) M₁≤M₂ (T.there z) = newᴴ-≤ x y M₁≤M₂ z

update-validᵀ : ∀ {l π  π'  τ ls} {Γ Γ' : Heaps ls} {Δ : Env l π} {M₁ M₂ : Memory l} ->
                l ↦ ⟨ M₁ , Δ ⟩ ∈ᴴ Γ ->
                Γ' ≔ Γ [ l ↦ ⟨ M₂ , Δ ⟩ ]ᴴ -> (lengthᴹ M₁) ≤ (lengthᴹ M₂) -> (t : Term π' τ) -> validᵀ Γ t -> validᵀ Γ' t
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
update-validᵀ l∈Γ u M₁≤M₂ (S.new x t) (ok , tⱽ) = {!!} -- ok , update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ l∈Γ u M₁≤M₂ (S.new∙ x t) ()
update-validᵀ l∈Γ u M₁≤M₂ S.#[ x ] tⱽ = tt
update-validᵀ l∈Γ u M₁≤M₂ S.#[ x ]ᴰ tⱽ = tt
update-validᵀ l∈Γ u M₁≤M₂ (S.fork l⊑h t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ l∈Γ u M₁≤M₂ (S.fork∙ l⊑h t) ()
update-validᵀ l∈Γ u M₁≤M₂ (S.deepDup t) tⱽ = update-validᵀ l∈Γ u M₁≤M₂ t tⱽ
update-validᵀ l∈Γ u M₁≤M₂ S.∙ ()

update-validᶜ : ∀ {l π l' ls τ₁ τ₂} {C : Cont l' τ₁ τ₂} {Γ Γ' : Heaps ls} {Δ : Env l π} {M₁ M₂ : Memory l} ->
                l ↦ ⟨ M₁ , Δ ⟩ ∈ᴴ Γ ->
                Γ' ≔ Γ [ l ↦ ⟨ M₂ , Δ ⟩ ]ᴴ -> (lengthᴹ M₁) ≤ (lengthᴹ M₂)
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
                  Γ' ≔ Γ [ l ↦ ⟨ M₂ , Δ ⟩ ]ᴴ -> (lengthᴹ M₁) ≤ (lengthᴹ M₂)
                -> validˢ Γ S -> validˢ Γ' S
update-validˢ {S = S.[]} l∈Γ u M₁≤M₂ Sⱽ = tt
update-validˢ {S = C S.∷ S} l∈Γ u M₁≤M₂ (Cⱽ , Sⱽ) = update-validᶜ {C = C} l∈Γ u M₁≤M₂ Cⱽ , (update-validˢ l∈Γ u M₁≤M₂ Sⱽ)
update-validˢ {S = S.∙} l∈Γ u M₁≤M₂ ()

update-⊆ᴴ : ∀ {l π ls} {Γ Γ' : Heaps ls} {Δ : Env l π} {M₁ M₂ : Memory l} ->
              l ↦ ⟨ M₁ , Δ ⟩ ∈ᴴ Γ ->
                Γ' ≔ Γ [ l ↦ ⟨ M₂ , Δ ⟩ ]ᴴ ->
                (lengthᴹ M₁) ≤ (lengthᴹ M₂) ->
                Γ ⊆ᴴ Γ'
update-⊆ᴴ S.here S.here M₁≤M₂ = cons (⟨ M₁≤M₂ , refl-⊆ᴱ ⟩) refl-⊆ᴴ
update-⊆ᴴ S.here (S.there {u = u} uᴴ) M₁≤M₂ = ⊥-elim (∈-not-unique (update-∈ uᴴ) u)
update-⊆ᴴ (S.there {u = u} l∈Δ) S.here M₁≤M₂ = ⊥-elim (∈-not-unique (member-∈ l∈Δ) u)
update-⊆ᴴ (S.there l∈Δ) (S.there u₁) M₁≤M₂ = cons refl-⊆'ᴴ (update-⊆ᴴ l∈Δ u₁ M₁≤M₂)

update-validᴴ : ∀ {l π ls} {Γ Γ' : Heaps ls} {Δ : Env l π} {M₁ M₂ : Memory l} ->
                  l ↦ ⟨ M₁ , Δ ⟩ ∈ᴴ Γ ->
                  Γ' ≔ Γ [ l ↦ ⟨ M₂ , Δ ⟩ ]ᴴ ->
                  (lengthᴹ M₁) ≤ (lengthᴹ M₂) ->
                  validᴹ M₂ ->
                  validᴴ Γ -> validᴴ Γ'
update-validᴴ {Γ = _ ∷ Γ} {Δ = Δ} {M₁} {M₂} S.here S.here M₁≤M₂ M₂ⱽ ((proj₁ , proj₂) , proj₃)
  = (M₂ⱽ , wkenᴱ {Δ = Δ} (cons (⟨ M₁≤M₂ , refl-⊆ᴱ ⟩) refl-⊆ᴴ) proj₂ ) , proj₃
update-validᴴ {Γ = S._∷_ {{u}} _ _} S.here (S.there b) M₁≤M₂ M₂ⱽ Γⱽ = ⊥-elim (∈-not-unique (update-∈ b) u)
update-validᴴ {Γ = S._∷_ {{u}} _ _} (S.there a) S.here M₁≤M₂ M₂ⱽ Γⱽ = ⊥-elim (∈-not-unique (member-∈ a) u)
update-validᴴ {Γ = S.⟨ M' , Δ' ⟩ S.∷ Γ} (S.there a) (S.there b) M₁≤M₂ M₂ⱽ ((proj₁ , proj₂) , proj₃)
  = (proj₁ , wkenᴱ {Δ = Δ'} (update-⊆ᴴ (there a) (there b) M₁≤M₂) proj₂) , (update-validᴴ a b M₁≤M₂ M₂ⱽ proj₃)
update-validᴴ {Γ = S.∙ S.∷ Γ} (S.there a) (S.there b) M₁≤M₂ M₂ⱽ (() , proj₂)



-- This does not go because I need to restrict Γ to get to the memory where the update occurs
-- which may make some references invalid.
-- update-valid'ᴴ : ∀ {l π₁ π₂ ls ls'} {Γ Γ' : Heaps ls} {Γ'' : Heaps ls'} {Δ₁ : Env l π₁} {Δ₂ : Env l π₂} {M : Memory l} ->
--                   l ↦ ⟨ M , Δ₁ ⟩ ∈ᴴ Γ ->
--                   Γ' ≔ Γ [ l ↦ ⟨ M , Δ₂ ⟩ ]ᴴ ->
--                   validᴴ Γ -> Γ ⊆ᴴ Γ'' -> validᴱ Γ'' Δ₂ -> validᴴ Γ'
-- update-valid'ᴴ S.here S.here Γⱽ Γ⊆ᴴΓ'' Δ₂ⱽ = {!!}
-- update-valid'ᴴ S.here (S.there {u = u} uᴴ) Γⱽ _ Δ₂ⱽ = ⊥-elim (∈-not-unique (update-∈ uᴴ) u)
-- update-valid'ᴴ (S.there {u = u} l∈Γ) S.here Γⱽ _ Δ₂ⱽ = ⊥-elim (∈-not-unique (member-∈ l∈Γ) u)
-- update-valid'ᴴ {Γ = S.⟨ x , x₁ ⟩ S.∷ Γ} (S.there l∈Γ) (S.there u₁) (proj₁ , proj₂) Γ⊆ᴴΓ'' Δ₂ⱽ = {!!} , (update-valid'ᴴ l∈Γ u₁ proj₂ {!drop ?!}  Δ₂ⱽ)
-- update-valid'ᴴ {Γ = S.∙ S.∷ Γ} (S.there l∈Γ) (S.there u₁) (() , proj₂) Δ₂ⱽ


-- valid⇝ : ∀ {l τ π₁ π₂ τ₁ τ₂} {t₁ : Term π₁ τ₁} {t₂ : Term π₂ τ₂} {Δ₁ : Env l π₁} {Δ₂ : Env l π₂} {S₁ : Stack l τ₁ τ} {S₂ : Stack l τ₂ τ}
--             {M : Memory l} -> l ↦ ⟨ M , Δ₁ ⟩ Γ ->
--            {!!} -> {!!} ⇝ {!!} -> {!!}
-- valid⇝ = {!!}

valid⟼ : ∀ {ls τ l} {p₁ p₂ : Program l ls τ} -> validᴾ p₁ -> p₁ ⟼ p₂ -> validᴾ p₂
valid⟼ (proj₁ , proj₂ , proj₃ ) (SS.Pure l∈Γ step uᴴ) = FIXME
  where postulate FIXME : ∀ {a} {A : Set a} -> A
--         with valid-memberᴴ proj₁ l∈Γ
-- ... | Mⱽ , Δⱽ = {!!} , ({!!} , {!!})
valid⟼ (proj₁ , proj₃ , proj₂) (SS.New {M = M} {τ∈π = τ∈π} {l⊑h = l⊑h} H∈Γ uᴴ) with valid-memberᴴ proj₁ H∈Γ
... | Mⱽ , Δⱽ with valid-newᴹ ∥ l⊑h ,  τ∈π ∥ M Mⱽ
... | M'ⱽ , ok-Addr = update-validᴴ H∈Γ uᴴ ok-Addr M'ⱽ proj₁ , (((update-∈ uᴴ) , valid-new-Addr {M = M} Mⱽ ∥ l⊑h ,  τ∈π ∥ uᴴ) , update-validˢ H∈Γ uᴴ (newᴹ-≤ M ∥ l⊑h ,  τ∈π ∥) proj₂)
valid⟼ (proj₁ , () , proj₂) SS.New∙
valid⟼ (proj₁ , proj₂ , proj₃ , proj₄) (SS.Write₂ H∈Γ uᴹ uᴴ) with valid-memberᴴ proj₁ H∈Γ
... | Mⱽ , Δⱽ with valid-writeᴹ uᴹ Mⱽ
... | M'ⱽ , M₁≤M₂ = (update-validᴴ H∈Γ uᴴ M₁≤M₂ M'ⱽ proj₁) , (tt , (update-validˢ H∈Γ uᴴ M₁≤M₂ proj₄))
valid⟼ (proj₁ , proj₂ , proj₃ , proj₄) (SS.Writeᴰ₂ H∈Γ uᴹ uᴴ) with valid-memberᴴ proj₁ H∈Γ
... | Mⱽ , Δⱽ with valid-writeᴹ uᴹ Mⱽ
... | M'ⱽ , M₁≤M₂ = (update-validᴴ H∈Γ uᴴ M₁≤M₂ M'ⱽ proj₁) , (tt , (update-validˢ H∈Γ uᴴ M₁≤M₂ proj₄))
valid⟼ (proj₁ , proj₃ , () , proj₂) SS.Write∙₂
valid⟼ (proj₁ , proj₃ , proj₂ , proj₄) (SS.Read₂ l∈Γ n∈M) = proj₁ , (T.tt , proj₄)
valid⟼ (proj₁ , proj₂ , proj₃ , proj₄) (SS.Readᴰ₂ L∈Γ n∈M) = proj₁ , T.tt , proj₄
valid⟼ (proj₁ , proj₃ , proj₂) (SS.DeepDupˢ {Δ = Δ} {τ∈π = τ∈π} L⊏l L∈Γ t∈Δ) with valid-memberᴴ proj₁ L∈Γ
... | Mⱽ , Δⱽ  = proj₁ , (valid-memberᴱ {Δ = Δ} {x = τ∈π} Δⱽ t∈Δ , proj₂)
valid⟼ () SS.Hole
