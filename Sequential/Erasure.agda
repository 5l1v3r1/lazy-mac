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

level : Ty -> Set
level （） = ⊤
level Bool = ⊤
level (τ => τ₁) = level τ × level τ₁
level (Mac l τ) = (Dec (l ⊑ A)) × (level τ)
level (Res l τ) = (Dec (l ⊑ A)) × (level τ)
level (Id τ) = level τ

level[_] : (τ : Ty) -> level τ
level[ （） ] = tt
level[ Bool ] = tt
level[ τ => τ₁ ] = level[ τ ] , level[ τ₁ ]
level[ Mac l τ ] = (l ⊑? A) , level[ τ ]
level[ Res l τ ] = (l ⊑? A) , level[ τ ]
level[ Id τ ] = level[ τ ]

εᵗ : ∀ {τ n } {π : Context n} -> level τ -> Term π τ -> Term π τ
εᵗ x （） = （）
εᵗ x True = True
εᵗ x False = False
εᵗ x (Id t) = Id (εᵗ x t)
εᵗ {（）} x (unId t) = unId (εᵗ x t)
εᵗ {Bool} x (unId t) = unId (εᵗ x t)
εᵗ {τ => τ₁} x (unId t) = unId (εᵗ x t)
εᵗ {Mac l τ} (yes p , proj₂) (unId t) = unId (εᵗ (yes p , proj₂) t)
εᵗ {Mac l τ} (no ¬p , proj₂) (unId t) = ∙
εᵗ {Res l τ} x (unId t) = unId (εᵗ x t)
εᵗ {Id τ} x (unId t) = unId (εᵗ x t)
εᵗ x (Var x∈π) = Var x∈π
εᵗ (proj₁ , proj₂) (Abs x t) = Abs x (εᵗ proj₂ t)
εᵗ {（）} x (App {α} t t₁) = App (εᵗ (level[ α ] , tt) t) (εᵗ level[ α ] t₁)
εᵗ {Bool} x (App {α} t t₁) = App (εᵗ (level[ α ] , tt) t) (εᵗ level[ α ] t₁)
εᵗ {τ => τ₁} x (App {α} t t₁) = App (εᵗ (level[ α ] , x) t) (εᵗ level[ α ] t₁)
εᵗ {Mac l τ} (yes p , proj₂) (App {α} t t₁) = App (εᵗ (level[ α ] , yes p , proj₂) t) (εᵗ level[ α ] t₁)
εᵗ {Mac l τ} (no ¬p , proj₂) (App t t₁) = ∙
εᵗ {Res l τ} x (App {α} t t₁) = App (εᵗ (level[ α ] , x) t) (εᵗ level[ α ] t₁)
εᵗ {Id τ} x (App {α} t t₁) = App (εᵗ (level[ α ] , x) t) (εᵗ level[ α ] t₁)
εᵗ {（）} x (If t Then t₁ Else t₂) = If (εᵗ tt t) Then (εᵗ tt t₁) Else (εᵗ tt t₂)
εᵗ {Bool} x (If t Then t₁ Else t₂) = If (εᵗ tt t) Then (εᵗ tt t₁) Else (εᵗ tt t₂)
εᵗ {τ => τ₁} x (If t Then t₁ Else t₂) = If (εᵗ tt t) Then (εᵗ x t₁) Else (εᵗ x t₂)
εᵗ {Mac l τ} (yes p , proj₂) (If t Then t₁ Else t₂) = If (εᵗ tt t) Then (εᵗ (yes p , proj₂) t₁) Else (εᵗ (yes p , proj₂) t₂)
εᵗ {Mac l τ} (no ¬p , proj₂) (If t Then t₁ Else t₂) = ∙
εᵗ {Res l τ} x (If t Then t₁ Else t₂) = If (εᵗ tt t) Then (εᵗ x t₁) Else (εᵗ x t₂)
εᵗ {Id τ} x (If t Then t₁ Else t₂) = If (εᵗ tt t) Then (εᵗ x t₁) Else (εᵗ x t₂)
εᵗ (yes p , proj₂) (Return l t) = Return l (εᵗ proj₂ t)
εᵗ (no ¬p , proj₂) (Return l t) = ∙
εᵗ (yes p , proj₂) (_>>=_ {α = α} t t₁) = (εᵗ ((yes p) , level[ α ]) t) >>= (εᵗ (level[ α ] , (yes p , proj₂)) t₁)
εᵗ (no ¬p , proj₂) (t >>= t₁) = ∙
εᵗ (yes p , proj₂) (Mac l t) = Mac l (εᵗ proj₂ t)
εᵗ (no ¬p , proj₂) (Mac l t) = ∙
εᵗ (yes p , proj₂) (Res l t) = Res l (εᵗ proj₂ t)
εᵗ (no ¬p , proj₂) (Res l t) = Res l ∙
εᵗ (yes A⊑L , yes p , α₁) (label L⊑H t) = label L⊑H (εᵗ α₁ t)
εᵗ (yes A⊑L , no ¬p , α₁) (label L⊑H t) = label∙ L⊑H (εᵗ α₁ t)
εᵗ (no ¬A⊑L , x , α₁) (label l⊑h t) = ∙
εᵗ (yes A⊑L , x , α₁) (label∙ L⊑H t) = label∙ L⊑H (εᵗ α₁ t)
εᵗ (no ¬A⊑L , x , α₁) (label∙ l⊑h t) = ∙
εᵗ (yes p , proj₂) (unlabel l⊑h t) = unlabel l⊑h (εᵗ ((yes (trans-⊑ l⊑h p)) , proj₂) t)
εᵗ (no ¬p , proj₂) (unlabel l⊑h t) = ∙
εᵗ (yes p , proj₂) (fork l⊑h t) = fork l⊑h (εᵗ level[ (Mac _ （）) ] t)
εᵗ (no ¬p , proj₂) (fork l⊑h t) = ∙
εᵗ {（）} x (deepDup x₁) = deepDup x₁
εᵗ {Bool} x (deepDup x₁) = deepDup x₁
εᵗ {τ => τ₁} x (deepDup x₁) = deepDup x₁
εᵗ {Mac l τ} (yes p , proj₂) (deepDup x₁) = deepDup x₁
εᵗ {Mac l τ} (no ¬p , proj₂) (deepDup x₁) = ∙
εᵗ {Res l τ} x (deepDup x₁) = deepDup x₁
εᵗ {Id τ} x (deepDup x₁) = deepDup x₁
εᵗ x ∙ = ∙

εᵀ : ∀ {τ n } {π : Context n} -> Term π τ -> Term π τ
εᵀ {τ} t = εᵗ level[ τ ] t

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

εᶜ : ∀ {τ₁ τ₂} -> Cont τ₁ τ₂ -> Cont τ₁ τ₂
εᶜ (Var x∈π) = Var x∈π
εᶜ (# x∈π) = # x∈π
εᶜ {τ₂ = τ₂} (Then t₁ Else t₂) = Then (εᵀ t₁) Else εᵀ t₂
εᶜ {τ₁ = Mac .l α} {τ₂ = Mac l β} (Bind t) = Bind (εᵀ t)
εᶜ (unlabel p) = unlabel p
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

εˢ : ∀ {τ₁ τ₂ l} -> Level τ₁ -> Level τ₂ -> Stack l τ₁ τ₂ -> Stack l τ₁ τ₂
εˢ a b ∙ = ∙
εˢ (inj₁ x) b [] = ∙
εˢ (inj₂ y) b [] = []
εˢ (inj₁ x) b (x₁ ∷ S) = ∙
εˢ (inj₂ y) (inj₁ x) (x₁ ∷ S) = ∙
εˢ (inj₂ y) (inj₂ y₁) (x ∷ S) with εˢ (isSecret? _) (isSecret? _) S
εˢ (inj₂ y) (inj₂ y₁) (x ∷ S) | ∙ = ∙
εˢ (inj₂ y) (inj₂ y₁) (x ∷ S) | S' = (εᶜ x) ∷ S'

εᴷ : ∀ {τ₁ τ₂ l} -> Stack l τ₁ τ₂ -> Stack l τ₁ τ₂
εᴷ S = εˢ (isSecret? _) (isSecret? _) S

--------------------------------------------------------------------------------

ε : ∀ {l τ} -> State l τ -> State l τ
ε ⟨ Γ , t , S ⟩ with εᴷ S
ε {τ = τ} (⟨_,_,_⟩ {π = π} Γ t S) | ∙ = ⟨ (εʰ Γ) , ∙ {π = π} , ∙ {τ₁ = τ}⟩
ε ⟨ Γ , t , S ⟩ | S' = ⟨ (εʰ Γ) , (εᵀ t) , S' ⟩


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



-- Simulation Property
ε-sim : ∀ {l τ} (s₁ s₂ : State l τ) -> s₁ ⇝ s₂ -> ε s₁ ⇝ ε s₂
ε-sim ⟨ Γ , t , S ⟩ s₂ step with εᴷ S
ε-sim ⟨ Γ , t , S ⟩ s₂ step | [] = {!!}
ε-sim ⟨ Γ , t , S ⟩ s₂ step | x ∷ r = {!!}
ε-sim ⟨ Γ , ._ , S ⟩ ._ (App₁ Δ∈Γ) | ∙ = {!!}
ε-sim ⟨ Γ , ._ , ._ ⟩ ._ (App₂ y∈π x∈π) | ∙ = {!!}
ε-sim ⟨ Γ , .(Var x∈π) , S ⟩ ._ (Var₁ Δ∈Γ x∈π t∈Δ ¬val) | ∙ = {!!}
ε-sim ⟨ Γ , .(Var x∈π) , S ⟩ ._ (Var₁' Δ∈Γ x∈π v∈Δ val) | ∙ = {!!}
ε-sim ⟨ Γ , t , ._ ⟩ ._ (Var₂ Δ∈Γ x∈π val) | ∙ = {!!}
ε-sim ⟨ Γ , ._ , S ⟩ ._ If | ∙ = {!!}
ε-sim ⟨ Γ , .True , ._ ⟩ ._ IfTrue | ∙ = {!!}
ε-sim ⟨ Γ , .False , ._ ⟩ ._ IfFalse | ∙ = {!!}
ε-sim ⟨ Γ , ._ , S ⟩ ._ Return | ∙ = {!!}
ε-sim ⟨ Γ , ._ , S ⟩ ._ Bind₁ | ∙ = {!!}
ε-sim ⟨ Γ , ._ , ._ ⟩ ._ Bind₂ | ∙ = {!!}
ε-sim ⟨ Γ , ._ , S ⟩ ._ (Label' p) | ∙ = {!!}
ε-sim ⟨ Γ , ._ , S ⟩ ._ (Unlabel₁ p) | ∙ = {!!}
ε-sim ⟨ Γ , ._ , ._ ⟩ ._ (Unlabel₂ p) | ∙ = {!!}
ε-sim ⟨ Γ , ._ , S ⟩ ._ UnId₁ | ∙ = {!!}
ε-sim ⟨ Γ , ._ , ._ ⟩ ._ UnId₂ | ∙ = {!!}
ε-sim ⟨ Γ , ._ , S ⟩ ._ (Fork p) | ∙ = {!!}
ε-sim ⟨ Γ , .∙ , .∙ ⟩ .(⟨ Γ , ∙ , ∙ ⟩) Hole | ∙ = Hole
