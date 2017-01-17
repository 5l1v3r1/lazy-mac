open import Types
import Lattice
open Lattice.Lattice 𝓛 renaming (_≟_ to _≟ᴸ_)

module Sequential.Erasure (A : Label) where  -- A is the security level of the attacker

open import Sequential.Calculus
open import Sequential.Semantics
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding (subst ; [_])

-- A view over sensitive (secret) computation types.
-- A is the attacker's security level
data Secret : Ty -> Set where
  Macᴴ : ∀ {h τ} -> (h⋤A : h ⋤ A) -> Secret (Mac h τ)
  -- Resᴴ is not here because it is always erased homomorphically
  -- like Public types, except for the constructor Res.


-- A view over insensitive (public) types.
-- A is the attacker's security level
data Public : Ty -> Set where
  Macᴸ : ∀ {τ l} -> (l⊑A : l ⊑ A) -> Public (Mac l τ)
  Res : ∀ {τ l} -> (l⊑?A : Dec (l ⊑ A)) -> Public (Res l τ)
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
εᵗ (inj₂ (Macᴸ l⊑A)) (t >>= t₁) = εᵗ (inj₂ (Macᴸ l⊑A)) t >>= (εᵗ (inj₂ Fun) t₁)
εᵗ (inj₁ x) (Mac l t) = ∙
εᵗ (inj₂ y) (Mac l t) = Mac l (εᵗ (isSecret? _) t)
εᵗ (inj₁ ()) (Res l t)
εᵗ (inj₂ (Res (yes p))) (Res l t) = Res l (εᵗ (isSecret? _) t)
εᵗ (inj₂ (Res (no ¬p))) (Res l t) = Res l ∙
εᵗ (inj₁ x) (label L⊑H t) = ∙
εᵗ (inj₂ (Macᴸ l⊑A)) (label {h = H} L⊑H t) with H ⊑? A
εᵗ (inj₂ (Macᴸ l⊑A)) (label L⊑H t) | yes p = label L⊑H (εᵗ (isSecret? _) t)
εᵗ (inj₂ (Macᴸ l⊑A)) (label L⊑H t) | no ¬p = label∙ L⊑H (εᵗ (isSecret? _) t)
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

εᴱ : ∀ {l n} {π : Context n} -> Dec (l ⊑ A) ->  Env l π -> Env l π
εᴱ (yes p) [] = []
εᴱ (yes p) (mt ∷ Δ) = (M.map (εᵗ (isSecret? _)) mt) ∷ (εᴱ (yes p) Δ)
εᴱ (yes p) ∙ = ∙
εᴱ (no ¬p) Δ = ∙

-- Proof irrelevance for εᴱ
εᴱ-ext : ∀ {l n} {π : Context n} -> (x y : Dec (l ⊑ A)) (Δ : Env l π) -> εᴱ x Δ ≡ εᴱ y Δ
εᴱ-ext (yes p) (yes p₁) [] = refl
εᴱ-ext (yes p) (yes p₁) (t ∷ Δ) rewrite εᴱ-ext (yes p) (yes p₁) Δ = refl
εᴱ-ext (yes p) (yes p₁) ∙ = refl
εᴱ-ext (yes p) (no ¬p) Δ = ⊥-elim (¬p p)
εᴱ-ext (no ¬p) (yes p) Δ = ⊥-elim (¬p p)
εᴱ-ext (no ¬p) (no ¬p₁) Δ = refl

-- Heap Erasure Function
εᴴ : ∀ {ls} -> Heap ls -> Heap ls
εᴴ [] = []
εᴴ (Δ ∷ Γ) = (εᴱ ( _ ⊑? A) Δ) ∷ εᴴ Γ

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

ε : ∀ {l τ ls} -> Level (Mac l τ) ->  State ls l (Mac l τ) -> State ls l (Mac l τ)
ε {l} {τ} (inj₁ ¬p) (⟨_,_,_⟩ {π = π} Γ t S) = ⟨ (εᴴ Γ) , ∙ {π = π} {{Mac l τ}} , ∙ ⟩
ε (inj₂ p) ⟨ Γ , t , S ⟩ = ⟨ εᴴ Γ , εᵀ t , εˢ S ⟩

--------------------------------------------------------------------------------

ε-wken : ∀ {τ n₁ n₂} {π₁ : Context n₁} {π₂ : Context n₂} -> (x : Level τ) -> (t : Term π₁ τ) (p : π₁ ⊆ˡ π₂) -> εᵗ x (wken t p) ≡ wken (εᵗ x t) p
ε-wken = {!!}

ε-subst : ∀ {τ n} {π : Context n} {x : Variable} (t₁ : Term π (ty x)) (t₂ : Term (x ∷ π) τ) (x : Level τ) ->
                 εᵗ x (subst t₁ t₂) ≡ subst (εᵀ t₁) (εᵗ x t₂)
ε-subst {π = π} = ε-tm-subst [] π -- t₁ t₂ p --  ε-tm-subst [] _ x t
  where
        ε-tm-subst : ∀ {τ n₁ n₂} {x : Variable} (π₁ : Context n₁) (π₂ : Context n₂) (t₁ : Term π₂ (ty x)) (t₂ : Term (π₁ ++ [ x ] ++ π₂) τ) (x : Level τ)
                   ->  εᵗ x (tm-subst π₁ π₂ t₁ t₂) ≡ tm-subst π₁ π₂ (εᵗ (isSecret? _) t₁) (εᵗ x t₂)
        ε-tm-subst π₁ π₂ t₁ （） p = refl
        ε-tm-subst π₁ π₂ t₁ True p = refl
        ε-tm-subst π₁ π₂ t₁ False p = refl
        ε-tm-subst π₁ π₂ t₁ (Id t₂) p rewrite ε-tm-subst π₁ π₂ t₁ t₂ (isSecret? _) = refl
        ε-tm-subst π₁ π₂ t₁ (unId t₂) (inj₁ x₁) = refl
        ε-tm-subst π₁ π₂ t₁ (unId t₂) (inj₂ y) rewrite ε-tm-subst π₁ π₂ t₁ t₂ (isSecret? _) = refl
        ε-tm-subst π₁ π₂ t₁ (Var x∈π) p = {!!}
        ε-tm-subst π₁ π₂ t₁ (Abs x t₂) p rewrite  ε-tm-subst (x ∷ π₁) _ t₁ t₂ (isSecret? _) = refl
        ε-tm-subst π₁ π₂ t₁ (App t₂ t₃) (inj₁ x₁) = refl
        ε-tm-subst π₁ π₂ t₁ (App t₂ t₃) (inj₂ y)
          rewrite ε-tm-subst π₁ π₂ t₁ t₂ (isSecret? _) | ε-tm-subst π₁ π₂ t₁ t₃ (isSecret? _) = refl
        ε-tm-subst π₁ π₂ t₁ (If t₂ Then t₃ Else t₄) (inj₁ x₁) = refl
        ε-tm-subst π₁ π₂ t₁ (If t₂ Then t₃ Else t₄) (inj₂ y)
          rewrite ε-tm-subst π₁ π₂ t₁ t₂ (inj₂ Bool) | ε-tm-subst π₁ π₂ t₁ t₃ (inj₂ y) | ε-tm-subst π₁ π₂ t₁ t₄ (inj₂ y) = refl
        ε-tm-subst π₁ π₂ t₁ (Return l t₂) (inj₁ x₁) = refl
        ε-tm-subst π₁ π₂ t₁ (Return l t₂) (inj₂ y)
          rewrite ε-tm-subst π₁ π₂ t₁ t₂ (isSecret? _) = refl
        ε-tm-subst π₁ π₂ t₁ (t₂ >>= t₃) (inj₁ x₁) = refl
        ε-tm-subst π₁ π₂ t₁ (t₂ >>= t₃) (inj₂ (Macᴸ y))
          rewrite ε-tm-subst π₁ π₂ t₁ t₂ (inj₂ (Macᴸ y)) | ε-tm-subst π₁ π₂ t₁ t₃ (inj₂ Fun) = refl
        ε-tm-subst π₁ π₂ t₁ (Mac l t₂) (inj₁ x₁) = refl
        ε-tm-subst π₁ π₂ t₁ (Mac l t₂) (inj₂ y) rewrite ε-tm-subst π₁ π₂ t₁ t₂ (isSecret? _) = refl
        ε-tm-subst π₁ π₂ t₁ (Res l t₂) (inj₁ ())
        ε-tm-subst π₁ π₂ t₁ (Res l t₂) (inj₂ (Res (yes p))) rewrite ε-tm-subst π₁ π₂ t₁ t₂ (isSecret? _) = refl
        ε-tm-subst π₁ π₂ t₁ (Res l t₂) (inj₂ (Res (no ¬p))) = refl
        ε-tm-subst π₁ π₂ t₁ (label l⊑h t₂) (inj₁ x₁) = refl
        ε-tm-subst π₁ π₂ t₁ (label {h = H} l⊑h t₂) (inj₂ (Macᴸ l⊑A)) with H ⊑? A
        ε-tm-subst π₁ π₂ t₁ (label l⊑h t₂) (inj₂ (Macᴸ l⊑A)) | yes p rewrite ε-tm-subst π₁ π₂ t₁ t₂ (isSecret? _) = refl
        ε-tm-subst π₁ π₂ t₁ (label l⊑h t₂) (inj₂ (Macᴸ l⊑A)) | no ¬p rewrite ε-tm-subst π₁ π₂ t₁ t₂ (isSecret? _) = refl
        ε-tm-subst π₁ π₂ t₁ (label∙ l⊑h t₂) (inj₁ x₁) = refl
        ε-tm-subst π₁ π₂ t₁ (label∙ l⊑h t₂) (inj₂ y) rewrite ε-tm-subst π₁ π₂ t₁ t₂ (isSecret? _) = refl
        ε-tm-subst π₁ π₂ t₁ (unlabel l⊑h t₂) (inj₁ x₁) = refl
        ε-tm-subst π₁ π₂ t₁ (unlabel {α = τ} l⊑h t₂) (inj₂ (Macᴸ _)) with isSecret? τ
        ε-tm-subst π₁ π₂ t₁ (unlabel l⊑h t₂) (inj₂ (Macᴸ _)) | inj₁ x₁ rewrite ε-tm-subst π₁ π₂ t₁ t₂ (isSecret? _) = refl
        ε-tm-subst π₁ π₂ t₁ (unlabel l⊑h t₂) (inj₂ (Macᴸ _)) | inj₂ y rewrite ε-tm-subst π₁ π₂ t₁ t₂ (isSecret? _) = refl
        ε-tm-subst π₁ π₂ t₁ (unlabel∙ l⊑h t₂) (inj₁ x₁) = refl
        ε-tm-subst π₁ π₂ t₁ (unlabel∙ l⊑h t₂) (inj₂ (Macᴸ l⊑A)) rewrite ε-tm-subst π₁ π₂ t₁ t₂ (isSecret? _) = refl
        ε-tm-subst π₁ π₂ t₁ (fork l⊑h t₂) (inj₁ x₁) = refl
        ε-tm-subst π₁ π₂ t₁ (fork {h = H} l⊑h t₂) (inj₂ (Macᴸ l⊑A)) rewrite ε-tm-subst π₁ π₂ t₁ t₂ (isSecret? _) = refl
        ε-tm-subst π₁ π₂ t₁ (deepDup x) p = refl
        ε-tm-subst π₁ π₂ t₁ ∙ p = refl

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
lemma' (Macᴴ h⋤A) (Macᴸ l⊑A) [] = ⊥-elim (h⋤A l⊑A)
lemma' x y (# x∈π ∷ S) = lemma' x y S
lemma' (Macᴴ h⋤A) (Macᴸ l⊑A) (Bind x₁ ∷ S) = lemma' (Macᴴ h⋤A) (Macᴸ l⊑A) S
lemma' (Macᴴ h⋤A) (Macᴸ l⊑A) ∙ = {!!} -- Is it the case that H ⋤ L -> L ⊑ H ?


updateᴱ∙ : ∀ {l n τ} {π : Context n} {Δ Δ' : Env l π} {t : Term π τ} -> (l⋤A : l ⋤ A) -> Δ' ≔ Δ [ ⟪ n , τ , l ⟫ ↦ t ]ᴱ -> εᴱ (no l⋤A) Δ' ≡ εᴱ (no l⋤A) Δ
updateᴱ∙ l⋤A x = refl

updateᴴ∙ : ∀ {l ls n} {π : Context n} {Δ : Env l π} {Γ Γ' : Heap ls} -> l ⋤ A -> Γ' ≔ Γ [ l ↦ Δ ]ᴴ -> εᴴ Γ' ≡ εᴴ Γ
updateᴴ∙ {l} l⋤A here with l ⊑? A
updateᴴ∙ l⋤A here | yes p = ⊥-elim (l⋤A p)
updateᴴ∙ l⋤A here | no ¬p = {!refl!} -- No because of type-level π and n
updateᴴ∙ l⋤A (there x) rewrite updateᴴ∙ l⋤A x = refl

insertᴴ∙ : ∀ {l ls τ n} {π : Context n} {Δ : Env l π} {Γ Γ' : Heap ls} {t : Term π τ} ->
          l ⋤ A -> Γ' ≔ Γ [ l ↦ insert t Δ ]ᴴ -> εᴴ Γ' ≡ εᴴ Γ
insertᴴ∙ {l} ¬p here with l ⊑? A
insertᴴ∙ ¬p here | yes p = ⊥-elim (¬p p)
insertᴴ∙ ¬p₁ here | no ¬p = {!!} -- No because of type-level π and n
insertᴴ∙ ¬p (there x) rewrite insertᴴ∙ ¬p x = refl

memberᴴ : ∀ {l ls n} {Γ : Heap ls} {π : Context n} {Δ : Env l π} -> (l⊑A : l ⊑ A) -> l ↦ Δ ∈ᴴ Γ -> l ↦ (εᴱ (yes l⊑A) Δ) ∈ᴴ (εᴴ Γ)
memberᴴ {l} p here with l ⊑? A
memberᴴ {Δ = Δ} p₁ here | yes p rewrite εᴱ-ext (yes p) (yes p₁) Δ = here
memberᴴ p here | no ¬p = ⊥-elim (¬p p)
memberᴴ p (there x) = there (memberᴴ p x)

insertᴴ : ∀ {l n τ ls} {Γ Γ' : Heap ls} {π : Context n} {Δ : Env l π} {t : Term π τ} (l⊑A : l ⊑ A) ->
            Γ' ≔ Γ [ l ↦ insert t Δ ]ᴴ -> εᴴ Γ' ≔ (εᴴ Γ) [ l ↦ insert (εᵗ (isSecret? τ) t) (εᴱ (yes l⊑A) Δ) ]ᴴ
insertᴴ {l} l⊑A here with l ⊑? A
insertᴴ {l} {Δ = []} l⊑A here | yes p = here
insertᴴ {l} {Δ = t ∷ Δ} l⊑A here | yes p  rewrite εᴱ-ext (yes p) (yes l⊑A) Δ = here
insertᴴ {l} {Δ = ∙} l⊑A here | yes p = here
insertᴴ l⊑A here | no ¬p = ⊥-elim (¬p l⊑A)
insertᴴ l⊑A (there x) = there (insertᴴ l⊑A x)

-- Simulation Property
-- Note that I fixed the type of the whole configuration to be Mac l τ, in order
-- to tie the security level of the computation to that of the stack.
-- It is also with the fact that all of these computations will be threads
-- in the concurrent semantics.
-- Since the actual term under evaluation can have any type the property
-- is still sufficiently general.
ε-sim : ∀ {l τ ls} (s₁ s₂ : State ls l (Mac l τ)) (x : Level (Mac l τ)) -> s₁ ⇝ s₂ -> ε x s₁ ⇝ ε x s₂
ε-sim ._ ._ (inj₁ (Macᴴ h⋤A)) (App₁ Δ∈Γ uᴴ)
  rewrite insertᴴ∙ h⋤A uᴴ = Hole
ε-sim ._ ._ (inj₁ x) (App₂ y∈π x∈π) = Hole
ε-sim ._ ._ (inj₁ (Macᴴ h⋤A)) (Var₁ Δ∈Γ x∈π t∈Δ ¬val rᴱ uᴴ)
  rewrite updateᴴ∙ h⋤A uᴴ = Hole
ε-sim ._ ._ (inj₁ x) (Var₁' Δ∈Γ x∈π v∈Δ val) = Hole
ε-sim ._ ._ (inj₁ (Macᴴ h⋤A)) (Var₂ Δ∈Γ x∈π val uᴱ uᴴ)
  rewrite updateᴴ∙ h⋤A uᴴ = Hole
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

ε-sim ._ ._ (inj₂ y) (App₁ {τ₂ = τ₂} Δ∈Γ uᴴ) with isSecret? τ₂
ε-sim ._ ._ (inj₂ y) (App₁ {S = S} Δ∈Γ uᴴ) | inj₁ (Macᴴ h⋤A) = ⊥-elim (lemma' (Macᴴ h⋤A) y S)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (App₁ Δ∈Γ uᴴ) | inj₂ y = App₁ (memberᴴ l⊑A Δ∈Γ) (insertᴴ l⊑A uᴴ)
ε-sim ⟨ Γ , Abs y t , ._ ∷ S ⟩ ._ (inj₂ y') (App₂ {β = β} y∈π x∈π) rewrite ε-subst (Var x∈π) t (isSecret? _) = App₂ y∈π x∈π
ε-sim ._ ._ (inj₂ y) (Var₁ Δ∈Γ x∈π t∈Δ ¬val rᴱ uᴴ) = {!!}
ε-sim ._ ._ (inj₂ y) (Var₁' Δ∈Γ x∈π v∈Δ val) = {!!}
ε-sim ._ ._ (inj₂ y) (Var₂ Δ∈Γ x∈π val uᴱ uᴴ) = {!!}
ε-sim ⟨ _ , ._ , S ⟩ ._ (inj₂ y) (If {τ = τ}) with isSecret? τ
ε-sim ⟨ x , ._ , S ⟩ ._ (inj₂ y) If | inj₁ (Macᴴ h⋤A) = ⊥-elim (lemma' (Macᴴ h⋤A) y S)
ε-sim ⟨ _ , ._ , S ⟩ _ (inj₂ y) If | inj₂ _ = If
ε-sim ._ ._ (inj₂ p) IfTrue = IfTrue
ε-sim ._ ._ (inj₂ p) IfFalse = IfFalse
ε-sim ._ ⟨ _ , Mac {α = τ} l t , S ⟩ (inj₂ y) Return with isSecret? (Mac l τ)
ε-sim .(⟨ Γ , Return l t , S ⟩) ⟨ Γ , Mac l t , S ⟩ (inj₂ (Macᴸ l⊑h)) Return | inj₁ x = ⊥-elim (secretNotPublic x (Macᴸ l⊑h))
ε-sim .(⟨ x , Return l t , S ⟩) ⟨ x , Mac l t , S ⟩ (inj₂ y) Return | inj₂ y' = Return
ε-sim ._ ._ (inj₂ (Macᴸ {τ} {l} l⊑A)) Bind₁ with isSecret? (Mac l τ)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) Bind₁ | inj₁ x = ⊥-elim (secretNotPublic x (Macᴸ l⊑A))
ε-sim ._ ._ (inj₂ (Macᴸ {l = l} l⊑A₁)) Bind₁ | inj₂ (Macᴸ l⊑A) with l ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A₁)) Bind₁ | inj₂ (Macᴸ l⊑A) | yes p = Bind₁
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A₁)) Bind₁ | inj₂ (Macᴸ l⊑A) | no ¬p = ⊥-elim (¬p l⊑A₁)
ε-sim ._ ._ (inj₂ (Macᴸ {τ} {l} l⊑A)) Bind₂ with isSecret? (Mac l τ)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) Bind₂ | inj₁ x = ⊥-elim (secretNotPublic x (Macᴸ l⊑A))
ε-sim ._ ._ (inj₂ (Macᴸ {l = l} l⊑A)) Bind₂ | inj₂ y with l ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) Bind₂ | inj₂ y | yes p = Bind₂
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) Bind₂ | inj₂ y | no ¬p = ⊥-elim (¬p l⊑A)
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
ε-sim ._ ._ (inj₂ (Macᴸ {τ} {l} l⊑A)) (Unlabel₁ p₁) with isSecret? (Mac l τ)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Unlabel₁ p₁) | inj₁ x = ⊥-elim (secretNotPublic x (Macᴸ l⊑A))
ε-sim ._ ._ (inj₂ (Macᴸ {l = l} l⊑A)) (Unlabel₁ p₁) | inj₂ y with l ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Unlabel₁ {τ = τ₁} p₁) | inj₂ y | yes p with isSecret? τ₁
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Unlabel₁ p₁) | inj₂ y | yes p | inj₁ x = Unlabel∙₁ p₁
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Unlabel₁ p₁) | inj₂ y₁ | yes p | inj₂ y = Unlabel₁ p₁
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Unlabel₁ p₁) | inj₂ y | no ¬p = ⊥-elim (¬p l⊑A)
ε-sim ._ ._ (inj₂ (Macᴸ {τ} {l} l⊑A)) (Unlabel₂ p₁) with isSecret? (Mac l τ)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Unlabel₂ p₁) | inj₁ x = ⊥-elim (secretNotPublic x (Macᴸ l⊑A))
ε-sim ._ ._ (inj₂ (Macᴸ {l = l} l⊑A)) (Unlabel₂ p₁) | inj₂ y with l ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Unlabel₂ {l' = l'} p₁) | inj₂ y | yes p with l' ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Unlabel₂ {τ = τ} p₂) | inj₂ y | yes p₁ | yes p with isSecret? τ
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Unlabel₂ p₂) | inj₂ y | yes p₁ | yes p | inj₁ (Macᴴ h⋤A) = Unlabel∙₂ p₂
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Unlabel₂ p₂) | inj₂ y₁ | yes p₁ | yes p | inj₂ y = Unlabel₂ p₂
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Unlabel₂ p₁) | inj₂ y | yes p | no ¬p = ⊥-elim (¬p (trans-⊑ p₁ l⊑A))
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Unlabel₂ p₁) | inj₂ y | no ¬p = ⊥-elim (¬p l⊑A)
ε-sim ._ ._ (inj₂ (Macᴸ {τ} {l} l⊑A)) (Unlabel∙₁ p) with isSecret? (Mac l τ)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Unlabel∙₁ p) | inj₁ x = ⊥-elim (secretNotPublic x (Macᴸ l⊑A))
ε-sim ._ ._ (inj₂ (Macᴸ {l = l} l⊑A)) (Unlabel∙₁ p) | inj₂ y with l ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Unlabel∙₁ p₁) | inj₂ y | yes p = Unlabel∙₁ p₁
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Unlabel∙₁ p) | inj₂ y | no ¬p = ⊥-elim (¬p l⊑A)
ε-sim ._ ._ (inj₂ (Macᴸ {τ} {l} l⊑A)) (Unlabel∙₂ p) with isSecret? (Mac l τ)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Unlabel∙₂ p) | inj₁ x = ⊥-elim (secretNotPublic x (Macᴸ l⊑A))
ε-sim ._ ._ (inj₂ (Macᴸ {l = l} l⊑A)) (Unlabel∙₂ p) | inj₂ y with l ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Unlabel∙₂ {l' = l'}  p₁) | inj₂ y | yes p with l' ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Unlabel∙₂ p₂) | inj₂ y | yes p₁ | yes p = Unlabel∙₂ p₂
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Unlabel∙₂ p₁) | inj₂ y | yes p | no ¬p = Unlabel∙₂ p₁
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Unlabel∙₂ p) | inj₂ y | no ¬p = ⊥-elim (¬p l⊑A)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (UnId₁ {τ = τ}) with isSecret? τ
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (UnId₁ {S = S}) | inj₁ (Macᴴ h⋤A) = ⊥-elim (lemma' (Macᴴ h⋤A) (Macᴸ l⊑A) S)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) UnId₁ | inj₂ y = UnId₁
ε-sim ._ ._ (inj₂ p) UnId₂ = UnId₂
ε-sim ._ ._ (inj₂ (Macᴸ {τ} {l} l⊑A)) (Fork p₁) with isSecret? (Mac l τ)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Fork p₁) | inj₁ x = ⊥-elim (secretNotPublic x (Macᴸ l⊑A))
ε-sim ._ ._ (inj₂ (Macᴸ {l = l} l⊑A)) (Fork p₁) | inj₂ y with l ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Fork p₁) | inj₂ y | yes p = Fork p₁
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Fork p₁) | inj₂ y | no ¬p = ⊥-elim (¬p l⊑A)
ε-sim ._ ._ (inj₂ p) Hole = Hole
