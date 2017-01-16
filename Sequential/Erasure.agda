open import Types
import Lattice
open Lattice.Lattice 𝓛 renaming (_≟_ to _≟ᴸ_)

module Sequential.Erasure (A : Label) where  -- A is the security level of the attacker

open import Sequential.Calculus
open import Sequential.Semantics
open import Data.Sum

-- A view over sensitive (secret) computation types.
-- lᴬ is the attacker's security level
data Secret : Ty -> Set where
  Macᴴ : ∀ {h τ} -> (h⋤lᴬ : h ⋤ A) -> Secret (Mac h τ)
  -- Resᴴ is not here because it is always erased homomorphically
  -- like Public types, except for the constructor Res.


-- A view over insensitive (public) types.
-- lᴬ is the attacker's security level
data Public : Ty -> Set where
  Macᴸ : ∀ {τ l} -> (l⊑lᴬ : l ⊑ A) -> Public (Mac l τ)
  Res : ∀ {τ l} -> (l⊑?lᴬ : Dec (l ⊑ A)) -> Public (Res l τ)
  （） : Public （）
  Bool : Public Bool
  Id : ∀ {τ} ->  Public (Id τ)
  Fun : ∀ {α β} -> Public (α => β)

-- Secret and insensitive are mutually exclusive
secretNotPublic : ∀ {τ} -> Secret τ -> Public τ -> ⊥
secretNotPublic (Macᴴ ¬p) (Macᴸ p) = ¬p p

Level : Ty -> Set
Level τ = (Secret τ) ⊎ (Public τ)

isSecret? : (τ : Ty) -> Level τ
isSecret? （） = inj₂ （）
isSecret? Bool = inj₂ Bool
isSecret? (τ => τ₁) = inj₂ Fun
isSecret? (Mac l τ) with l ⊑? A
isSecret? (Mac l τ) | yes p = inj₂ (Macᴸ p)
isSecret? (Mac l τ) | no ¬p = inj₁ (Macᴴ ¬p)
isSecret? (Res l τ) = inj₂ (Res (l ⊑? A))
isSecret? (Id τ) = inj₂ Id

--------------------------------------------------------------------------------

open import Data.Product

-- level : Ty -> Set
-- level （） = ⊤
-- level Bool = ⊤
-- level (τ => τ₁) = level τ × level τ₁
-- level (Mac l τ) = (Dec (l ⊑ A)) × (level τ)
-- level (Res l τ) = (Dec (l ⊑ A)) × (level τ)
-- level (Id τ) = level τ

-- level[_] : (τ : Ty) -> level τ
-- level[ （） ] = tt
-- level[ Bool ] = tt
-- level[ τ => τ₁ ] = level[ τ ] , level[ τ₁ ]
-- level[ Mac l τ ] = (l ⊑? A) , level[ τ ]
-- level[ Res l τ ] = (l ⊑? A) , level[ τ ]
-- level[ Id τ ] = level[ τ ]

εᵗ : ∀ {τ n } {π : Context n} -> Level τ -> Term π τ -> Term π τ
εᵗ x （） = （）
εᵗ x True = True
εᵗ x False = False
εᵗ x (Id t) = Id (εᵗ (isSecret? _) t)
εᵗ (inj₁ x) (unId t) = ∙
εᵗ (inj₂ y) (unId t) = unId (εᵗ (inj₂ Id) t)
εᵗ x (Var x∈π) = Var x∈π  -- Can we kill variables as well?
εᵗ _ (Abs x t) = Abs x (εᵗ (isSecret? _) t)
εᵗ (inj₁ x) (App t t₁) = ∙
εᵗ (inj₂ y) (App t t₁) = App (εᵗ (inj₂ Fun) t) (εᵗ (isSecret? _) t₁)
εᵗ (inj₁ x) (If t Then t₁ Else t₂) = ∙
εᵗ (inj₂ y) (If t Then t₁ Else t₂) = If (εᵗ (inj₂ Bool) t) Then (εᵗ (inj₂ y) t₁) Else (εᵗ (inj₂ y) t₂)
εᵗ (inj₁ x) (Return l t) = ∙
εᵗ (inj₂ y) (Return l t) = Return l (εᵗ (isSecret? _) t)
εᵗ (inj₁ x) (t >>= t₁) = ∙
εᵗ (inj₂ (Macᴸ l⊑lᴬ)) (t >>= t₁) = εᵗ (inj₂ (Macᴸ l⊑lᴬ)) t >>= (εᵗ (inj₂ Fun) t₁)
εᵗ (inj₁ x) (Mac l t) = ∙
εᵗ (inj₂ y) (Mac l t) = Mac l (εᵗ (isSecret? _) t)
εᵗ (inj₁ ()) (Res l t)
εᵗ (inj₂ (Res (yes p))) (Res l t) = Res l (εᵗ (isSecret? _) t)
εᵗ (inj₂ (Res (no ¬p))) (Res l t) = Res l ∙
εᵗ (inj₁ x) (label L⊑H t) = ∙
εᵗ (inj₂ (Macᴸ l⊑lᴬ)) (label {h = H} L⊑H t) with H ⊑? A
εᵗ (inj₂ (Macᴸ l⊑lᴬ)) (label L⊑H t) | yes p = label L⊑H (εᵗ (isSecret? _) t)
εᵗ (inj₂ (Macᴸ l⊑lᴬ)) (label L⊑H t) | no ¬p = label∙ L⊑H (εᵗ (isSecret? _) t)
εᵗ (inj₁ x) (label∙ L⊑H t) = ∙
εᵗ (inj₂ y) (label∙ L⊑H t) = label∙ L⊑H (εᵗ (isSecret? _) t)
εᵗ (inj₁ x) (unlabel l⊑h t) = ∙
εᵗ (inj₂ (Macᴸ L⊑A)) (unlabel {α = τ} L⊑H t) with isSecret? τ
εᵗ (inj₂ (Macᴸ L⊑A)) (unlabel L⊑H t) | inj₁ x = unlabel∙ L⊑H (εᵗ (isSecret? _) t)
εᵗ (inj₂ (Macᴸ L⊑A)) (unlabel L⊑H t) | inj₂ y = unlabel L⊑H (εᵗ (isSecret? _) t) -- This should be only inj₂ due to transitivity
εᵗ (inj₁ _) (unlabel∙ L⊑H t) = ∙
εᵗ (inj₂ (Macᴸ L⊑A)) (unlabel∙ L⊑H t) = unlabel∙ L⊑H (εᵗ (isSecret? _) t)
εᵗ (inj₁ x) (fork l⊑h t) = ∙
εᵗ (inj₂ y) (fork l⊑h t) = fork l⊑h (εᵗ (isSecret? _) t)
εᵗ x (deepDup x₁) = deepDup x₁ -- Must be consistent with Var
εᵗ x ∙ = ∙

εᵀ : ∀ {τ n } {π : Context n} -> Term π τ -> Term π τ
εᵀ {τ} t = εᵗ (isSecret? _) t

--------------------------------------------------------------------------------

open import Data.Product as P
open import Data.Maybe as M
open import Function

-- Point-wise erasure of a RawEnv
εᴿ : ∀ {n} {π : Context n} -> RawEnv π -> RawEnv π
εᴿ M n with M n
εᴿ M n₁ | τ , mt = τ , M.map εᵀ mt

-- Constant mapping to ∙ (it can be modified and this is a problem)
-- We need the old environment for the type
∙ᴿ : ∀ {n} {π : Context n} -> RawEnv π -> RawEnv π
∙ᴿ M n = proj₁ (M n) , just ∙

εᴱ : ∀ {l n} {π : Context n} -> Dec (l ⊑ A) ->  Env l π -> Env l π
εᴱ {_} {lᴬ} (yes p) (RE x) = RE (εᴿ x)
εᴱ (no ¬p) (RE x) = RE (∙ᴿ x)  -- Here I should have a different Env that is not updateable

-- Heap Erasure Function
εʰ : Heap -> Heap
εʰ Γ l with Γ l
εʰ Γ l | n , π , Δ = n , π , εᴱ (l ⊑? A) Δ
--------------------------------------------------------------------------------

εᶜ : ∀ {τ₁ τ₂ l} -> Cont l τ₁ τ₂ -> Cont l τ₁ τ₂
εᶜ (Var x∈π) = Var x∈π
εᶜ (# x∈π) = # x∈π
εᶜ {τ₂ = τ₂} (Then t₁ Else t₂) = Then (εᵀ t₁) Else εᵀ t₂
εᶜ {τ₁ = Mac .l α} {τ₂ = Mac l β} (Bind t) = Bind (εᵀ t)
εᶜ (unlabel {τ = τ} p) with isSecret? τ
εᶜ (unlabel p) | inj₁ x = unlabel∙ p
εᶜ (unlabel p) | inj₂ y = unlabel p
εᶜ (unlabel∙ p) = unlabel∙ p
εᶜ unId = unId

-- This definition is inconvinient because we inspect the result of calling εˢ,
-- hence it is not clear to Agda that it is homomorphic.
-- I propose to use the Stack label as an approximation
-- of the sensitivity of the computation.
-- For instance unId :: >>= t :: [] : Stack H, is a stack that at some point will yield
-- a computation Mac H.
--

-- Plan
-- 1) Add labels to Cont
-- 2) Tie Cont l in the >>= and unlabel constructor.
-- 3) Erase terms to ∙ if the the label of the stack is H.
-- 4) The label of the stack corresponds to the security level of the term under evaluation
--    How can we enforce that ?

-- Fully homomorphic erasure on stack
εˢ : ∀ {τ₁ τ₂ l} -> Stack l τ₁ τ₂ -> Stack l τ₁ τ₂
εˢ [] = []
εˢ (c ∷ S) = (εᶜ c) ∷ εˢ S
εˢ ∙ = ∙

-- εᴷ : ∀ {τ₁ τ₂ l} -> Stack l τ₁ τ₂ -> Stack l τ₁ τ₂
-- εᴷ S = εˢ (isSecret? _) (isSecret? _) S

--------------------------------------------------------------------------------

ε : ∀ {l τ} -> Level (Mac l τ) ->  State l (Mac l τ) -> State l (Mac l τ)
ε {l} {τ} (inj₁ ¬p) (⟨_,_,_⟩ {π = π} Γ t S) = ⟨ (εʰ Γ) , ∙ {π = π} {{Mac l τ}} , ∙ ⟩
ε (inj₂ p) ⟨ Γ , t , S ⟩ = ⟨ (εʰ Γ) , εᵀ t , εˢ S ⟩

--------------------------------------------------------------------------------

{-

Homomorphic erasure function for MAC H and stack does works for Bind₁ but not for Bind₂

Bind₁:
(Γ , t₁ >>= t₂ , S) → (Γ , t₁ , >>= t₂ : S)

(ε(Γ) , ε(t₁) >>= ε(t₂) , ε(S)) → (ε(Γ) , ε(t₁) , >>= ε(t₂) : ε(S))

Bind₂:
(Γ , Mac t₁ , >>= t₂ : S) → (Γ , t₂ t₁ , S)

(ε(Γ) , Mac ∙ , >>= ε(t₂) : ε(S)) ↛ (ε(Γ) , ε(t₂) ε(t₁) , ε(S))  -- t₁ ≠ ∙

-}

-- ε-sim' : ∀ {l n n' τ₁ τ₂}{π : Context n} {π' : Context n'} {S : Stack l τ₁ τ₂} {t₁ : Term π τ₁} {t₂ : Term π' τ₁'} ->

-- This is the proof that it is impossible to turn a high computation into a low one
-- We need this lemma to discharge those cases in which the Stack produce a Mac L
-- computation but the current term under evaluation has type Mac H.
lemma : ∀ {l h τ₁ τ₂} -> A ⊑ l -> A ⋤ h -> Stack l (Mac h τ₁) (Mac l τ₂) -> ⊥
lemma A⊑L A⋤H [] = ⊥-elim (A⋤H A⊑L)
lemma A⊑L A⋤H (# x∈π ∷ S) = lemma A⊑L A⋤H S
lemma A⊑L A⋤H (Bind x ∷ S) = lemma A⊑L A⋤H S
lemma {L} {H} A⊑L A⋤H ∙ with L ⊑? H
lemma A⊑L A⋤H ∙ | yes L⊑H = trans-⋢ A⊑L A⋤H L⊑H
lemma A⊑L A⋤H ∙ | no L⋤H = {!trans-⋢!} -- Is it the case that H ⋤ L -> L ⊑ H ?


lemma' : ∀ {l h τ₁ τ₂} -> Secret (Mac h τ₁) -> Public (Mac l τ₂) -> Stack l (Mac h τ₁) (Mac l τ₂) -> ⊥
lemma' (Macᴴ h⋤lᴬ) (Macᴸ l⊑lᴬ) [] = ⊥-elim (h⋤lᴬ l⊑lᴬ)
lemma' x y (# x∈π ∷ S) = lemma' x y S
lemma' (Macᴴ h⋤lᴬ) (Macᴸ l⊑lᴬ) (Bind x₁ ∷ S) = lemma' (Macᴴ h⋤lᴬ) (Macᴸ l⊑lᴬ) S
lemma' (Macᴴ h⋤lᴬ) (Macᴸ l⊑lᴬ) ∙ = {!!} -- Is it the case that H ⋤ L -> L ⊑ H ?

-- Simulation Property
-- Note that I fixed the type of the whole configuration to be Mac l τ, in order
-- to tie the security level of the computation to that of the stack.
-- It is also with the fact that all of these computations will be threads
-- in the concurrent semantics.
-- Since the actual term under evaluation can have any type the property
-- is still sufficiently general.
ε-sim : ∀ {l τ} (s₁ s₂ : State l (Mac l τ)) (x : Level (Mac l τ)) -> s₁ ⇝ s₂ -> ε x s₁ ⇝ ε x s₂
-- Here we need to reason about where variables are pushed
ε-sim ⟨ x , ._ , x₂ ⟩ ⟨ ._ , x₄ , .(Var here ∷ x₂) ⟩ (inj₁ _) (App₁ Δ∈Γ) = {!!}
ε-sim ⟨ Γ , ._ , .(Var x∈π ∷ x₅) ⟩ ⟨ .Γ , ._ , x₅ ⟩ (inj₁ _) (App₂ y∈π x∈π) = Hole
ε-sim ⟨ Γ , .(Var x∈π) , x₂ ⟩ ⟨ ._ , x₄ , .(# x∈π ∷ x₂) ⟩ (inj₁ _) (Var₁ Δ∈Γ x∈π t∈Δ ¬val) = {!!}
ε-sim ⟨ Γ , .(Var x∈π) , x₂ ⟩ ⟨ .Γ , x₄ , .x₂ ⟩ (inj₁ _) (Var₁' Δ∈Γ x∈π v∈Δ val) = Hole
ε-sim ⟨ Γ , x₁ , .(# x∈π ∷ x₅) ⟩ ⟨ ._ , .x₁ , x₅ ⟩ (inj₁ _) (Var₂ Δ∈Γ x∈π val) = {!!}
ε-sim ⟨ x , ._ , x₂ ⟩ ⟨ .x , x₄ , ._ ⟩ (inj₁ _) If = Hole
ε-sim ⟨ x , .True , ._ ⟩ ⟨ .x , x₄ , x₅ ⟩ (inj₁ _) IfTrue = Hole
ε-sim ⟨ x , .False , ._ ⟩ ⟨ .x , x₄ , x₅ ⟩ (inj₁ _) IfFalse = Hole
ε-sim ⟨ x , ._ , x₂ ⟩ ⟨ .x , ._ , .x₂ ⟩ (inj₁ _) Return = Hole
ε-sim ⟨ x , ._ , x₂ ⟩ ⟨ .x , x₄ , ._ ⟩ (inj₁ _) Bind₁ = Hole
ε-sim ⟨ x , ._ , ._ ⟩ ⟨ .x , ._ , x₅ ⟩ (inj₁ _) Bind₂ = Hole
ε-sim ⟨ Γ , ._ , x₂ ⟩ ⟨ .Γ , ._ , .x₂ ⟩ (inj₁ _) (Label' p) = Hole
ε-sim ._ ._ (inj₁ _) (Label'∙ p₁) = Hole
ε-sim ⟨ Γ , .(unlabel p x₄) , x₂ ⟩ ⟨ .Γ , x₄ , .(unlabel p ∷ x₂) ⟩ (inj₁ _) (Unlabel₁ p) = Hole
ε-sim ⟨ Γ , ._ , .(unlabel p ∷ x₅) ⟩ ⟨ .Γ , ._ , x₅ ⟩ (inj₁ _) (Unlabel₂ p) = Hole
ε-sim ⟨ Γ , ._ , ._ ⟩ ⟨ .Γ , ._ , ._ ⟩ (inj₁ _) (Unlabel∙₁ p) = Hole
ε-sim ⟨ Γ , ._ , .(unlabel∙ p ∷ x₅) ⟩ ⟨ .Γ , ._ , x₅ ⟩ (inj₁ _) (Unlabel∙₂ p) = Hole
ε-sim ⟨ x , .(unId x₄) , x₂ ⟩ ⟨ .x , x₄ , .(unId ∷ x₂) ⟩ (inj₁ _) UnId₁ = Hole
ε-sim ⟨ x , .(Id x₄) , .(unId ∷ x₅) ⟩ ⟨ .x , x₄ , x₅ ⟩ (inj₁ _) UnId₂ = Hole
ε-sim ⟨ Γ , ._ , x₂ ⟩ ⟨ .Γ , ._ , .x₂ ⟩ (inj₁ _) (Fork p) = Hole
ε-sim ⟨ x , .∙ , .∙ ⟩ ⟨ .x , .∙ , .∙ ⟩ (inj₁ _) Hole = Hole
--
ε-sim ._ ._ (inj₂ p) (App₁ Δ∈Γ) = {!!}
ε-sim ._ ._ (inj₂ p) (App₂ y∈π x∈π) = {!!}
ε-sim ._ ._ (inj₂ p) (Var₁ Δ∈Γ x∈π t∈Δ ¬val) = {!!}
ε-sim ._ ._ (inj₂ p) (Var₁' Δ∈Γ x∈π v∈Δ val) = {!!}
ε-sim ._ ._ (inj₂ p) (Var₂ Δ∈Γ x∈π val) = {!!}
ε-sim ⟨ _ , ._ , S ⟩ ._ (inj₂ y) (If {τ = τ}) with isSecret? τ
ε-sim ⟨ x , ._ , S ⟩ ._ (inj₂ y) If | inj₁ (Macᴴ h⋤lᴬ) = ⊥-elim (lemma' (Macᴴ h⋤lᴬ) y S)
ε-sim ⟨ _ , ._ , S ⟩ _ (inj₂ y) If | inj₂ _ = If
ε-sim ._ ._ (inj₂ p) IfTrue = IfTrue
ε-sim ._ ._ (inj₂ p) IfFalse = IfFalse
ε-sim ._ ⟨ _ , Mac {α = τ} l t , S ⟩ (inj₂ y) Return with isSecret? (Mac l τ)
ε-sim .(⟨ Γ , Return l t , S ⟩) ⟨ Γ , Mac l t , S ⟩ (inj₂ (Macᴸ l⊑h)) Return | inj₁ x = ⊥-elim (secretNotPublic x (Macᴸ l⊑h))
ε-sim .(⟨ x , Return l t , S ⟩) ⟨ x , Mac l t , S ⟩ (inj₂ y) Return | inj₂ y' = Return
ε-sim ._ ._ (inj₂ (Macᴸ {τ} {l} l⊑lᴬ)) Bind₁ with isSecret? (Mac l τ)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) Bind₁ | inj₁ x = ⊥-elim (secretNotPublic x (Macᴸ l⊑lᴬ))
ε-sim ._ ._ (inj₂ (Macᴸ {l = l} l⊑lᴬ₁)) Bind₁ | inj₂ (Macᴸ l⊑lᴬ) with l ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ₁)) Bind₁ | inj₂ (Macᴸ l⊑lᴬ) | yes p = Bind₁
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ₁)) Bind₁ | inj₂ (Macᴸ l⊑lᴬ) | no ¬p = ⊥-elim (¬p l⊑lᴬ₁)
ε-sim ._ ._ (inj₂ (Macᴸ {τ} {l} l⊑lᴬ)) Bind₂ with isSecret? (Mac l τ)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) Bind₂ | inj₁ x = ⊥-elim (secretNotPublic x (Macᴸ l⊑lᴬ))
ε-sim ._ ._ (inj₂ (Macᴸ {l = l} l⊑lᴬ)) Bind₂ | inj₂ y with l ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) Bind₂ | inj₂ y | yes p = Bind₂
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) Bind₂ | inj₂ y | no ¬p = ⊥-elim (¬p l⊑lᴬ)
ε-sim ._ ._ (inj₂ (Macᴸ {τ} {l} l⊑A)) (Label' p₁) with isSecret? (Mac l τ)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Label' p₁) | inj₁ x = ⊥-elim (secretNotPublic x (Macᴸ l⊑A))
ε-sim ._ ._ (inj₂ (Macᴸ {l = l} l⊑A)) (Label' p₁) | inj₂ y with l ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Label' {h = h} p₁) | inj₂ y | yes p with h ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Label' p₂) | inj₂ y | yes p₁ | yes p = Label' p₂
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Label' p₁) | inj₂ y | yes p | no ¬p = Label'∙ p₁
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Label' p₁) | inj₂ y | no ¬p = ⊥-elim (¬p l⊑A)
ε-sim ._ ._ (inj₂ (Macᴸ {τ} {l} l⊑A)) (Label'∙ p₁) with isSecret? (Mac l τ)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Label'∙ p₁) | inj₁ x = ⊥-elim (secretNotPublic x (Macᴸ l⊑A))
ε-sim ._ ._ (inj₂ (Macᴸ {l = l} l⊑A)) (Label'∙ p₁) | inj₂ y with l ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Label'∙ {h = h} p₁) | inj₂ y | yes p with h ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Label'∙ p₂) | inj₂ y | yes p₁ | yes p = Label'∙ p₂
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Label'∙ p₁) | inj₂ y | yes p | no ¬p = Label'∙ p₁
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Label'∙ p₁) | inj₂ y | no ¬p = ⊥-elim (¬p l⊑A)
ε-sim ._ ._ (inj₂ (Macᴸ {τ} {l} l⊑lᴬ)) (Unlabel₁ p₁) with isSecret? (Mac l τ)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Unlabel₁ p₁) | inj₁ x = ⊥-elim (secretNotPublic x (Macᴸ l⊑lᴬ))
ε-sim ._ ._ (inj₂ (Macᴸ {l = l} l⊑lᴬ)) (Unlabel₁ p₁) | inj₂ y with l ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Unlabel₁ {τ = τ₁} p₁) | inj₂ y | yes p with isSecret? τ₁
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Unlabel₁ p₁) | inj₂ y | yes p | inj₁ x = Unlabel∙₁ p₁
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Unlabel₁ p₁) | inj₂ y₁ | yes p | inj₂ y = Unlabel₁ p₁
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Unlabel₁ p₁) | inj₂ y | no ¬p = ⊥-elim (¬p l⊑lᴬ)
ε-sim ._ ._ (inj₂ (Macᴸ {τ} {l} l⊑lᴬ)) (Unlabel₂ p₁) with isSecret? (Mac l τ)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Unlabel₂ p₁) | inj₁ x = ⊥-elim (secretNotPublic x (Macᴸ l⊑lᴬ))
ε-sim ._ ._ (inj₂ (Macᴸ {l = l} l⊑lᴬ)) (Unlabel₂ p₁) | inj₂ y with l ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Unlabel₂ {l' = l'} p₁) | inj₂ y | yes p with l' ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Unlabel₂ {τ = τ} p₂) | inj₂ y | yes p₁ | yes p with isSecret? τ
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Unlabel₂ p₂) | inj₂ y | yes p₁ | yes p | inj₁ (Macᴴ h⋤lᴬ) = Unlabel∙₂ p₂
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Unlabel₂ p₂) | inj₂ y₁ | yes p₁ | yes p | inj₂ y = Unlabel₂ p₂
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Unlabel₂ p₁) | inj₂ y | yes p | no ¬p = ⊥-elim (¬p (trans-⊑ p₁ l⊑lᴬ))
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Unlabel₂ p₁) | inj₂ y | no ¬p = ⊥-elim (¬p l⊑lᴬ)
ε-sim ._ ._ (inj₂ (Macᴸ {τ} {l} l⊑lᴬ)) (Unlabel∙₁ p) with isSecret? (Mac l τ)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Unlabel∙₁ p) | inj₁ x = ⊥-elim (secretNotPublic x (Macᴸ l⊑lᴬ))
ε-sim ._ ._ (inj₂ (Macᴸ {l = l} l⊑lᴬ)) (Unlabel∙₁ p) | inj₂ y with l ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Unlabel∙₁ p₁) | inj₂ y | yes p = Unlabel∙₁ p₁
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Unlabel∙₁ p) | inj₂ y | no ¬p = ⊥-elim (¬p l⊑lᴬ)
ε-sim ._ ._ (inj₂ (Macᴸ {τ} {l} l⊑lᴬ)) (Unlabel∙₂ p) with isSecret? (Mac l τ)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Unlabel∙₂ p) | inj₁ x = ⊥-elim (secretNotPublic x (Macᴸ l⊑lᴬ))
ε-sim ._ ._ (inj₂ (Macᴸ {l = l} l⊑lᴬ)) (Unlabel∙₂ p) | inj₂ y with l ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Unlabel∙₂ {l' = l'}  p₁) | inj₂ y | yes p with l' ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Unlabel∙₂ p₂) | inj₂ y | yes p₁ | yes p = Unlabel∙₂ p₂
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Unlabel∙₂ p₁) | inj₂ y | yes p | no ¬p = Unlabel∙₂ p₁
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Unlabel∙₂ p) | inj₂ y | no ¬p = ⊥-elim (¬p l⊑lᴬ)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (UnId₁ {τ = τ}) with isSecret? τ
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (UnId₁ {S = S}) | inj₁ (Macᴴ h⋤lᴬ) = ⊥-elim (lemma' (Macᴴ h⋤lᴬ) (Macᴸ l⊑lᴬ) S)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) UnId₁ | inj₂ y = UnId₁
ε-sim ._ ._ (inj₂ p) UnId₂ = UnId₂
ε-sim ._ ._ (inj₂ (Macᴸ {τ} {l} l⊑lᴬ)) (Fork p₁) with isSecret? (Mac l τ)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Fork p₁) | inj₁ x = ⊥-elim (secretNotPublic x (Macᴸ l⊑lᴬ))
ε-sim ._ ._ (inj₂ (Macᴸ {l = l} l⊑lᴬ)) (Fork p₁) | inj₂ y with l ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Fork p₁) | inj₂ y | yes p = Fork p₁
ε-sim ._ ._ (inj₂ (Macᴸ l⊑lᴬ)) (Fork p₁) | inj₂ y | no ¬p = ⊥-elim (¬p l⊑lᴬ)
ε-sim ._ ._ (inj₂ p) Hole = Hole
