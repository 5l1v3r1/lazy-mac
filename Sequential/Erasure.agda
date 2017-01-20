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
data Secret : Ty -> Set where  Macᴴ : ∀ {h τ} -> (h⋤A : h ⋤ A) -> Secret (Mac h τ)

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

εᵗ : ∀ {τ π} -> Term π τ -> Term π τ
εᵗ （） = （）
εᵗ True = True
εᵗ False = False
εᵗ (Id t) = Id (εᵗ t)
εᵗ (unId t) = unId (εᵗ t)
εᵗ (Var τ∈π) = Var τ∈π
εᵗ (Abs t) = Abs (εᵗ t)
εᵗ (App t t₁) = App (εᵗ t) (εᵗ t₁)
εᵗ (If t Then t₁ Else t₂) = If (εᵗ t) Then (εᵗ t₁) Else (εᵗ t₂)
εᵗ (Return l t) = Return l (εᵗ t)
εᵗ (t >>= t₁) = (εᵗ t) >>= (εᵗ t₁)
εᵗ (Mac l t) = Mac l (εᵗ t)
εᵗ (Res l t) with l ⊑? A
εᵗ (Res l t) | yes p = Res l (εᵗ t)
εᵗ (Res l t) | no ¬p = Res l ∙
εᵗ (label {h = H} l⊑h t) with H ⊑? A
εᵗ (label l⊑h t) | yes p = label l⊑h (εᵗ t)
εᵗ (label l⊑h t) | no ¬p = label∙ l⊑h (εᵗ t)
εᵗ (label∙ l⊑h t) = label∙ l⊑h (εᵗ t)
εᵗ (unlabel l⊑h t) = unlabel l⊑h (εᵗ t)
εᵗ (fork l⊑h t) = fork l⊑h (εᵗ t)
εᵗ (deepDup t) = deepDup (εᵗ t)
εᵗ ∙ = ∙

εᵀ : ∀ {τ π} -> Term π τ -> Term π τ
εᵀ {τ} t = εᵗ t

εᵀ¬Val : ∀ {π τ} {t : Term π τ} -> ¬ Value t -> ¬ (Value (εᵀ t))
εᵀ¬Val {t = （）} ¬val val-ε = ¬val val-ε
εᵀ¬Val {t = True} ¬val val-ε = ¬val val-ε
εᵀ¬Val {t = False} ¬val val-ε = ¬val val-ε
εᵀ¬Val {t = Id t} ¬val val-ε = ¬val (Id t)
εᵀ¬Val {t = unId t} ¬val ()
εᵀ¬Val {t = Var τ∈π} ¬val val-ε = ¬val val-ε
εᵀ¬Val {t = Abs t} ¬val val-ε = ¬val (Abs t)
εᵀ¬Val {t = App t t₁} ¬val ()
εᵀ¬Val {t = If t Then t₁ Else t₂} ¬val ()
εᵀ¬Val {t = Return l t} ¬val ()
εᵀ¬Val {t = t >>= t₁} ¬val ()
εᵀ¬Val {t = Mac l t} ¬val val-ε = ¬val (Mac t)
εᵀ¬Val {t = Res l t} ¬val val-ε = ¬val (Res t)
εᵀ¬Val {t = label {h = H} l⊑h t} ¬val val-ε with H ⊑? A
εᵀ¬Val {π} {._} {label l⊑h t} ¬val () | yes p
εᵀ¬Val {π} {._} {label l⊑h t} ¬val () | no ¬p
εᵀ¬Val {t = label∙ l⊑h t} ¬val ()
εᵀ¬Val {t = unlabel l⊑h t} ¬val ()
εᵀ¬Val {t = fork l⊑h t} ¬val ()
εᵀ¬Val {t = deepDup t} ¬val ()
εᵀ¬Val {t = ∙} ¬val ()

εᵀ-Val : ∀ {τ π} {v : Term π τ} -> Value v -> Value (εᵀ v)
εᵀ-Val （） = （）
εᵀ-Val True = True
εᵀ-Val False = False
εᵀ-Val (Abs t) = Abs (εᵗ t)
εᵀ-Val (Id t) = Id (εᵗ t)
εᵀ-Val {Mac l τ} (Mac t) = Mac _
εᵀ-Val {Res l τ} (Res t) with l ⊑? A
εᵀ-Val {Res l τ} (Res t) | yes p = Res (εᵗ t)
εᵀ-Val {Res l τ} (Res t) | no ¬p = Res ∙

εᵗ¬Var : ∀ {π τ} {t : Term π τ} -> ¬ IsVar t -> ¬ (IsVar (εᵗ t))
εᵗ¬Var {t = （）} ¬var var-ε = ¬var var-ε
εᵗ¬Var {t = True} ¬var var-ε = ¬var var-ε
εᵗ¬Var {t = False} ¬var var-ε = ¬var var-ε
εᵗ¬Var {t = Id t} ¬var ()
εᵗ¬Var {t = unId t} ¬var ()
εᵗ¬Var {t = Var τ∈π} ¬var var-ε = ¬var (Var τ∈π)
εᵗ¬Var {t = Abs t} ¬var ()
εᵗ¬Var {t = App t t₁} ¬var ()
εᵗ¬Var {t = If t Then t₁ Else t₂} ¬var ()
εᵗ¬Var {t = Return l t} ¬var ()
εᵗ¬Var {t = t >>= t₁} ¬var ()
εᵗ¬Var {t = Mac l t} ¬var ()
εᵗ¬Var {t = Res l t} ¬var var-ε with l ⊑? A
εᵗ¬Var {π} {._} {Res l t} ¬var () | yes p
εᵗ¬Var {π} {._} {Res l t} ¬var () | no ¬p
εᵗ¬Var {t = label {h = H} l⊑h t} ¬var var-ε with H ⊑? A
εᵗ¬Var {π} {._} {label l⊑h t} ¬var () | yes p
εᵗ¬Var {π} {._} {label l⊑h t} ¬var () | no ¬p
εᵗ¬Var {t = label∙ l⊑h t} ¬var ()
εᵗ¬Var {t = unlabel l⊑h t} ¬var ()
εᵗ¬Var {t = fork l⊑h t} ¬var ()
εᵗ¬Var {t = deepDup t} ¬var ()
εᵗ¬Var {t = ∙} ¬var ()

open import Data.Product as P
open import Data.Maybe as M
open import Function

εᴱ : ∀ {l π} -> Dec (l ⊑ A) ->  Env l π -> Env l π
εᴱ (yes p) [] = []
εᴱ (yes p) (mt ∷ Δ) = (M.map εᵗ mt) ∷ (εᴱ (yes p) Δ)
εᴱ (yes p) ∙ = ∙
εᴱ (no ¬p) Δ = ∙

-- Proof irrelevance for εᴱ
εᴱ-ext : ∀ {l π} -> (x y : Dec (l ⊑ A)) (Δ : Env l π) -> εᴱ x Δ ≡ εᴱ y Δ
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
εᶜ (unlabel {τ = τ} p) = unlabel p
εᶜ unId = unId

-- Fully homomorphic erasure on stack
εˢ : ∀ {τ₁ τ₂ l} -> Stack l τ₁ τ₂ -> Stack l τ₁ τ₂
εˢ [] = []
εˢ (c ∷ S) = (εᶜ c) ∷ εˢ S
εˢ ∙ = ∙

--------------------------------------------------------------------------------

ε : ∀ {l τ ls} -> Level (Mac l τ) ->  State ls l (Mac l τ) -> State ls l (Mac l τ)
ε {l} {τ} (inj₁ ¬p) (⟨_,_,_⟩ {π = π} Γ t S) = ⟨ (εᴴ Γ) , ∙ {π = π} {{Mac l τ}} , ∙ ⟩
ε (inj₂ p) ⟨ Γ , t , S ⟩ = ⟨ εᴴ Γ , εᵀ t , εˢ S ⟩

--------------------------------------------------------------------------------

ε-wken : ∀ {τ π₁ π₂} -> (t : Term π₁ τ) (p : π₁ ⊆ˡ π₂) -> εᵗ (wken t p) ≡ wken (εᵗ t) p
ε-wken （） p = refl
ε-wken True p = refl
ε-wken False p = refl
ε-wken (Id t) p rewrite ε-wken t p = refl
ε-wken (unId t) p rewrite ε-wken t p = refl
ε-wken (Var τ∈π) p = refl
ε-wken (Abs t) p rewrite ε-wken t (cons p) = refl
ε-wken (App t t₁) p
  rewrite ε-wken t p | ε-wken t₁ p = refl
ε-wken (If t Then t₁ Else t₂) p
  rewrite ε-wken t p | ε-wken t₁ p | ε-wken t₂ p = refl
ε-wken (Return l t) p rewrite ε-wken t p = refl
ε-wken (t >>= t₁) p
  rewrite ε-wken t p | ε-wken t₁ p = refl
ε-wken (Mac l t) p rewrite ε-wken t p = refl
ε-wken (Res l t) p with l ⊑? A
... | no _ = refl
... | yes _ rewrite ε-wken t p = refl
ε-wken (label {h = H} l⊑h t) p with H ⊑? A
... | no ¬p rewrite ε-wken t p = refl
... | yes _ rewrite ε-wken t p = refl
ε-wken (label∙ l⊑h t) p rewrite ε-wken t p = refl
ε-wken (unlabel l⊑h t) p rewrite ε-wken t p = refl
ε-wken (fork l⊑h t) p rewrite ε-wken t p = refl
ε-wken (deepDup t) p rewrite ε-wken t p = refl
ε-wken ∙ p = refl
ε-subst : ∀ {τ τ' π} (t₁ : Term π τ') (t₂ : Term (τ' ∷ π) τ) -> εᵗ (subst t₁ t₂) ≡ subst (εᵀ t₁) (εᵗ t₂)
ε-subst = ε-tm-subst [] _
  where ε-var-subst  :  ∀ {α β} (π₁ : Context) (π₂ : Context) (t₁ : Term π₂ α) (β∈π : β ∈ (π₁ ++ [ α ] ++ π₂))
                      ->  εᵗ (var-subst π₁ π₂ t₁ β∈π) ≡ var-subst π₁ π₂ (εᵗ t₁) β∈π
        ε-var-subst [] π₂ t₁ here = refl
        ε-var-subst [] π₁ t₁ (there β∈π) = refl
        ε-var-subst (β ∷ π₁) π₂ t₁ here = refl
        ε-var-subst (τ ∷ π₁) π₂ t₁ (there β∈π)
          rewrite ε-wken (var-subst π₁ π₂ t₁ β∈π) (drop {τ} refl-⊆ˡ) | ε-var-subst π₁ π₂ t₁ β∈π = refl

        ε-tm-subst : ∀ {τ τ'} (π₁ : Context) (π₂ : Context) (t₁ : Term π₂ τ') (t₂ : Term (π₁ ++ [ τ' ] ++ π₂) τ)
                   ->  εᵗ (tm-subst π₁ π₂ t₁ t₂) ≡ tm-subst π₁ π₂ (εᵗ t₁) (εᵗ t₂)
        ε-tm-subst π₁ π₂ t₁ （） = refl
        ε-tm-subst π₁ π₂ t₁ True = refl
        ε-tm-subst π₁ π₂ t₁ False = refl
        ε-tm-subst π₁ π₂ t₁ (Id t₂) rewrite ε-tm-subst π₁ π₂ t₁ t₂ = refl
        ε-tm-subst π₁ π₂ t₁ (unId t₂) rewrite ε-tm-subst π₁ π₂ t₁ t₂ = refl
        ε-tm-subst π₁ π₂ t₁ (Var τ∈π) rewrite ε-var-subst π₁ π₂ t₁ τ∈π = refl
        ε-tm-subst π₁ π₂ t₁ (Abs t₂)  rewrite ε-tm-subst (_ ∷ π₁) π₂ t₁ t₂ = refl
        ε-tm-subst π₁ π₂ t₁ (App t₂ t₃)
          rewrite ε-tm-subst π₁ π₂ t₁ t₂ | ε-tm-subst π₁ π₂ t₁ t₃ = refl
        ε-tm-subst π₁ π₂ t₁ (If t₂ Then t₃ Else t₄)
          rewrite ε-tm-subst π₁ π₂ t₁ t₂ | ε-tm-subst π₁ π₂ t₁ t₃ | ε-tm-subst π₁ π₂ t₁ t₄ = refl
        ε-tm-subst π₁ π₂ t₁ (Return l t₂) rewrite ε-tm-subst π₁ π₂ t₁ t₂ = refl
        ε-tm-subst π₁ π₂ t₁ (t₂ >>= t₃)
          rewrite ε-tm-subst π₁ π₂ t₁ t₂ | ε-tm-subst π₁ π₂ t₁ t₃ = refl
        ε-tm-subst π₁ π₂ t₁ (Mac l t₂) rewrite ε-tm-subst π₁ π₂ t₁ t₂ = refl
        ε-tm-subst π₁ π₂ t₁ (Res l t₂) with l ⊑? A
        ε-tm-subst π₁ π₂ t₁ (Res l t₂) | yes p rewrite ε-tm-subst π₁ π₂ t₁ t₂ = refl
        ε-tm-subst π₁ π₂ t₁ (Res l t₂) | no ¬p = refl
        ε-tm-subst π₁ π₂ t₁ (label {h = H} l⊑h t₂) with H ⊑? A
        ε-tm-subst π₁ π₂ t₁ (label l⊑h t₂) | yes p rewrite ε-tm-subst π₁ π₂ t₁ t₂ = refl
        ε-tm-subst π₁ π₂ t₁ (label l⊑h t₂) | no ¬p rewrite ε-tm-subst π₁ π₂ t₁ t₂ = refl
        ε-tm-subst π₁ π₂ t₁ (label∙ l⊑h t₂) rewrite ε-tm-subst π₁ π₂ t₁ t₂ = refl
        ε-tm-subst π₁ π₂ t₁ (unlabel l⊑h t₂) rewrite ε-tm-subst π₁ π₂ t₁ t₂ = refl
        ε-tm-subst π₁ π₂ t₁ (fork l⊑h t₂) rewrite ε-tm-subst π₁ π₂ t₁ t₂ = refl
        ε-tm-subst π₁ π₂ t₁ (deepDup t₂) rewrite ε-tm-subst π₁ π₂ t₁ t₂ = refl
        ε-tm-subst π₁ π₂ t₁ ∙ = refl

ε-deepDupᵀ-≡ : ∀ {π τ} -> (t : Term π τ) ->  εᵗ (deepDupᵀ t) ≡ deepDupᵀ (εᵗ t)
ε-deepDupᵀ-≡ = εᵗ-dup-ufv-≡ []
  where εᵗ-dup-ufv-≡ : ∀ {π τ} -> (vs : Vars π) (t : Term π τ) ->  εᵗ (dup-ufv vs t) ≡ dup-ufv vs (εᵗ t)
        εᵗ-dup-ufv-≡ vs （） = refl
        εᵗ-dup-ufv-≡ vs True = refl
        εᵗ-dup-ufv-≡ vs False = refl
        εᵗ-dup-ufv-≡ vs (Id t)
          rewrite εᵗ-dup-ufv-≡ vs t = refl
        εᵗ-dup-ufv-≡ vs (unId t)
          rewrite εᵗ-dup-ufv-≡ vs t = refl
        εᵗ-dup-ufv-≡ vs (Var τ∈π) with memberⱽ τ∈π vs
        εᵗ-dup-ufv-≡ vs (Var τ∈π) | yes p = refl
        εᵗ-dup-ufv-≡ vs (Var τ∈π) | no ¬p = refl
        εᵗ-dup-ufv-≡ vs (Abs t)
          rewrite εᵗ-dup-ufv-≡ (here ∷ (mapⱽ there vs)) t = refl
        εᵗ-dup-ufv-≡ vs (App t t₁)
          rewrite εᵗ-dup-ufv-≡ vs t | εᵗ-dup-ufv-≡ vs t₁ = refl
        εᵗ-dup-ufv-≡ vs (If t Then t₁ Else t₂)
          rewrite εᵗ-dup-ufv-≡ vs t | εᵗ-dup-ufv-≡ vs t₁ | εᵗ-dup-ufv-≡ vs t₂ = refl
        εᵗ-dup-ufv-≡ vs (Return l t) rewrite εᵗ-dup-ufv-≡ vs t = refl
        εᵗ-dup-ufv-≡ vs (t >>= t₁)
          rewrite εᵗ-dup-ufv-≡ vs t | εᵗ-dup-ufv-≡ vs t₁ = refl
        εᵗ-dup-ufv-≡ vs (Mac l t) rewrite εᵗ-dup-ufv-≡ vs t = refl
        εᵗ-dup-ufv-≡ vs (Res l t) with l ⊑? A
        εᵗ-dup-ufv-≡ vs (Res l t) | yes p rewrite εᵗ-dup-ufv-≡ vs t = refl
        εᵗ-dup-ufv-≡ vs (Res l t) | no ¬p = refl
        εᵗ-dup-ufv-≡ vs (label {h = H} l⊑h t) with H ⊑? A
        εᵗ-dup-ufv-≡ vs (label l⊑h t) | yes p rewrite εᵗ-dup-ufv-≡ vs t = refl
        εᵗ-dup-ufv-≡ vs (label l⊑h t) | no ¬p rewrite εᵗ-dup-ufv-≡ vs t = refl
        εᵗ-dup-ufv-≡ vs (label∙ l⊑h t) rewrite εᵗ-dup-ufv-≡ vs t = refl
        εᵗ-dup-ufv-≡ vs (unlabel l⊑h t) rewrite εᵗ-dup-ufv-≡ vs t = refl
        εᵗ-dup-ufv-≡ vs (fork l⊑h t) rewrite εᵗ-dup-ufv-≡ vs t = refl
        εᵗ-dup-ufv-≡ vs (deepDup t) rewrite εᵗ-dup-ufv-≡ vs t = refl
        εᵗ-dup-ufv-≡ vs ∙ = refl

--------------------------------------------------------------------------------
-- Env lemmas

memberᴱ : ∀ {l π π' τ} {Δ : Env l π} {t : Term π' τ} {τ∈π : τ ∈ π} ->
          (l⊑A : l ⊑ A) -> τ∈π ↦ t ∈ᴱ Δ -> τ∈π ↦ (εᵀ t) ∈ᴱ (εᴱ (yes l⊑A) Δ)
memberᴱ l⊑A here = here
memberᴱ l⊑A (there t∈Δ) = there (memberᴱ l⊑A t∈Δ)

updateᴱ : ∀ {l π π' τ} {Δ Δ' : Env l π} {mt : Maybe (Term π' τ)} {τ∈π : τ ∈ π}
          (l⊑A : l ⊑ A) -> Updateᴱ mt τ∈π Δ Δ' -> Updateᴱ (M.map εᵀ mt) τ∈π (εᴱ (yes l⊑A) Δ) (εᴱ (yes l⊑A) Δ')
updateᴱ l⊑A here = here
updateᴱ l⊑A (there x) = there (updateᴱ l⊑A x)
updateᴱ l⊑A ∙ = ∙

--------------------------------------------------------------------------------
-- Heap Lemmas

updateᴴ∙ : ∀ {l ls π} {Δ : Env l π} {Γ Γ' : Heap ls} -> l ⋤ A -> Γ' ≔ Γ [ l ↦ Δ ]ᴴ -> εᴴ Γ' ≡ εᴴ Γ
updateᴴ∙ {l} l⋤A here with l ⊑? A
updateᴴ∙ l⋤A here | yes p = ⊥-elim (l⋤A p)
updateᴴ∙ l⋤A here | no ¬p = {!refl!} -- No because of type-level π
updateᴴ∙ l⋤A (there x) rewrite updateᴴ∙ l⋤A x = refl

insertᴴ∙ : ∀ {l ls τ π} {Δ : Env l π} {Γ Γ' : Heap ls} {t : Term π τ} ->
          l ⋤ A -> Γ' ≔ Γ [ l ↦ insert t Δ ]ᴴ -> εᴴ Γ' ≡ εᴴ Γ
insertᴴ∙ {l} ¬p here with l ⊑? A
insertᴴ∙ ¬p here | yes p = ⊥-elim (¬p p)
insertᴴ∙ ¬p₁ here | no ¬p = {!refl!} -- No because of type-level π
insertᴴ∙ ¬p (there x) rewrite insertᴴ∙ ¬p x = refl

memberᴴ : ∀ {l ls π} {Γ : Heap ls} {Δ : Env l π} -> (l⊑A : l ⊑ A) -> l ↦ Δ ∈ᴴ Γ -> l ↦ (εᴱ (yes l⊑A) Δ) ∈ᴴ (εᴴ Γ)
memberᴴ {l} p here with l ⊑? A
memberᴴ {Δ = Δ} p₁ here | yes p rewrite εᴱ-ext (yes p) (yes p₁) Δ = here
memberᴴ p here | no ¬p = ⊥-elim (¬p p)
memberᴴ p (there x) = there (memberᴴ p x)

insertᴴ : ∀ {l π τ ls} {Γ Γ' : Heap ls} {Δ : Env l π} {t : Term π τ} (l⊑A : l ⊑ A) ->
            Γ' ≔ Γ [ l ↦ insert t Δ ]ᴴ -> εᴴ Γ' ≔ (εᴴ Γ) [ l ↦ insert (εᵗ t) (εᴱ (yes l⊑A) Δ) ]ᴴ
insertᴴ {l} l⊑A here with l ⊑? A
insertᴴ {l} {Δ = []} l⊑A here | yes p = here
insertᴴ {l} {Δ = t ∷ Δ} l⊑A here | yes p  rewrite εᴱ-ext (yes p) (yes l⊑A) Δ = here
insertᴴ {l} {Δ = ∙} l⊑A here | yes p = here
insertᴴ l⊑A here | no ¬p = ⊥-elim (¬p l⊑A)
insertᴴ l⊑A (there x) = there (insertᴴ l⊑A x)

updateᴴ : ∀ {l ls π} {Δ : Env l π} {Γ Γ' : Heap ls} -> (l⊑A : l ⊑ A) -> Γ' ≔ Γ [ l ↦ Δ ]ᴴ -> (εᴴ Γ') ≔ (εᴴ Γ) [ l ↦ (εᴱ (yes l⊑A ) Δ) ]ᴴ
updateᴴ {l} {Δ = Δ} l⊑A here rewrite εᴱ-ext (yes l⊑A) (l ⊑? A) Δ = here
updateᴴ l⊑A (there x) = there (updateᴴ l⊑A x)

-- Simulation Property
-- Note that I fixed the type of the whole configuration to be Mac l τ, in order
-- to tie the security level of the computation to that of the stack.
-- It is also consistent with the fact that all of these computations will be threads
-- in the concurrent semantics.
-- Since the actual term under evaluation can have any type the property
-- is still sufficiently general.
ε-sim : ∀ {l τ ls} {s₁ s₂ : State ls l (Mac l τ)} (x : Level (Mac l τ)) -> s₁ ⇝ s₂ -> ε x s₁ ⇝ ε x s₂

-- High-Computations
ε-sim (inj₁ (Macᴴ h⋤A)) (App₁ Δ∈Γ uᴴ) rewrite insertᴴ∙ h⋤A uᴴ = Hole
ε-sim (inj₁ x) (App₂ α∈π α∈π₁) = Hole
ε-sim (inj₁ (Macᴴ h⋤A)) (Var₁ Δ∈Γ τ∈π t∈Δ ¬val rᴱ uᴴ)
  rewrite updateᴴ∙ h⋤A uᴴ = Hole
ε-sim (inj₁ x) (Var₁' Δ∈Γ τ∈π v∈Δ val) = Hole
ε-sim (inj₁ (Macᴴ h⋤A)) (Var₂ Δ∈Γ τ∈π val uᴱ uᴴ)
  rewrite updateᴴ∙ h⋤A uᴴ = Hole
ε-sim (inj₁ x) If = Hole
ε-sim (inj₁ x) IfTrue = Hole
ε-sim (inj₁ x) IfFalse = Hole
ε-sim (inj₁ x) Return = Hole
ε-sim (inj₁ x) Bind₁ = Hole
ε-sim (inj₁ x) Bind₂ = Hole
ε-sim (inj₁ x) (Label' p) = Hole
ε-sim (inj₁ x) (Label'∙ p) = Hole
ε-sim (inj₁ x) (Unlabel₁ p) = Hole
ε-sim (inj₁ x) (Unlabel₂ p) = Hole
ε-sim (inj₁ x) UnId₁ = Hole
ε-sim (inj₁ x) UnId₂ = Hole
ε-sim (inj₁ x) (Fork p) = Hole
ε-sim (inj₁ x) Hole = Hole
ε-sim (inj₁ (Macᴴ h⋤A)) (DeepDup Δ∈Γ t∈Δ uᴴ)
  rewrite insertᴴ∙ h⋤A uᴴ = Hole
ε-sim (inj₁ (Macᴴ h⋤A)) (DeepDup' ¬var Δ∈Γ uᴴ)
  rewrite insertᴴ∙ h⋤A uᴴ = Hole

-- Low-compuations
ε-sim (inj₂ (Macᴸ l⊑A)) (App₁ Δ∈Γ uᴴ) = App₁ (memberᴴ l⊑A Δ∈Γ) (insertᴴ l⊑A uᴴ)
ε-sim (inj₂ (Macᴸ l⊑A)) (App₂ {t = t} α∈π α∈π₁) rewrite ε-subst (Var α∈π₁) t = App₂ α∈π α∈π₁
ε-sim (inj₂ (Macᴸ l⊑A)) (Var₁ Δ∈Γ τ∈π t∈Δ ¬val rᴱ uᴴ) = Var₁ (memberᴴ l⊑A Δ∈Γ) τ∈π (memberᴱ l⊑A t∈Δ) (εᵀ¬Val ¬val) (updateᴱ l⊑A rᴱ) (updateᴴ l⊑A uᴴ)
ε-sim (inj₂ (Macᴸ l⊑A)) (Var₁' Δ∈Γ τ∈π v∈Δ val) = Var₁' (memberᴴ l⊑A Δ∈Γ) τ∈π (memberᴱ l⊑A v∈Δ) (εᵀ-Val val)
ε-sim (inj₂ (Macᴸ l⊑A)) (Var₂ Δ∈Γ τ∈π val uᴱ uᴴ) = Var₂ (memberᴴ l⊑A Δ∈Γ) τ∈π (εᵀ-Val val) (updateᴱ l⊑A uᴱ) (updateᴴ l⊑A uᴴ)
ε-sim (inj₂ y) If = If
ε-sim (inj₂ y) IfTrue = IfTrue
ε-sim (inj₂ y) IfFalse = IfFalse
ε-sim (inj₂ y) Return = Return
ε-sim (inj₂ y) Bind₁ = Bind₁
ε-sim (inj₂ y) Bind₂ = Bind₂
ε-sim (inj₂ y) (Label' {h = H} p) with H ⊑? A
ε-sim (inj₂ y) (Label' p₁) | yes p = Label' p₁
ε-sim (inj₂ y) (Label' p) | no ¬p = Label'∙ p
ε-sim (inj₂ y) (Label'∙ {h = H} p) with H ⊑? A
ε-sim (inj₂ y) (Label'∙ p₁) | yes p = Label'∙ p₁
ε-sim (inj₂ y) (Label'∙ p) | no ¬p = Label'∙ p
ε-sim (inj₂ y) (Unlabel₁ p) = Unlabel₁ p
ε-sim (inj₂ (Macᴸ H⊑A)) (Unlabel₂ {l' = L} L⊑H) with L ⊑? A
ε-sim (inj₂ (Macᴸ H⊑A)) (Unlabel₂ L⊑H) | yes p = Unlabel₂ L⊑H
ε-sim (inj₂ (Macᴸ H⊑A)) (Unlabel₂ L⊑H) | no L⋤A = ⊥-elim (L⋤A (trans-⊑ L⊑H H⊑A))
ε-sim (inj₂ y) UnId₁ = UnId₁
ε-sim (inj₂ y) UnId₂ = UnId₂
ε-sim (inj₂ y) (Fork p) = Fork p
ε-sim (inj₂ y) Hole = Hole
ε-sim (inj₂ (Macᴸ l⊑A)) (DeepDup {t = t} Δ∈Γ t∈Δ uᴴ) with insertᴴ l⊑A uᴴ
... | uᴴ' rewrite ε-deepDupᵀ-≡ t = DeepDup (memberᴴ l⊑A Δ∈Γ) (memberᴱ l⊑A t∈Δ) uᴴ'
ε-sim (inj₂ (Macᴸ l⊑A)) (DeepDup' ¬var Δ∈Γ uᴴ) = DeepDup' (εᵗ¬Var ¬var) (memberᴴ l⊑A Δ∈Γ) (insertᴴ l⊑A uᴴ)
