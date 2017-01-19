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

εᵗ : ∀ {τ π}  -> Level τ -> Term π τ -> Term π τ
εᵗ x （） = （）
εᵗ x True = True
εᵗ x False = False
εᵗ x (Id t) = Id (εᵗ (isSecret? _) t)
εᵗ (inj₁ x) (unId t) = ∙
εᵗ (inj₂ y) (unId t) = unId (εᵗ (inj₂ Id) t)
εᵗ x (Var x∈π) = Var x∈π  -- Can we kill variables as well?
εᵗ _ (Abs t) = Abs (εᵗ (isSecret? _) t)
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
εᵗ x (deepDup t) = deepDup (εᵗ x t)
εᵗ x ∙ = ∙

εᵀ : ∀ {τ π} -> Term π τ -> Term π τ
εᵀ {τ} t = εᵗ (isSecret? _) t

εᵀ¬Val : ∀ {π τ} {t : Term π τ} -> ¬ Value t -> ¬ (Value (εᵀ t))
εᵀ¬Val = ε¬Val _ (isSecret? _)
  where ε¬Val : ∀ {π τ} -> (t : Term π τ) (x : Level τ) -> ¬ (Value t) -> ¬ (Value (εᵗ x t))
        ε¬Val （） x ¬val val-ε = ¬val val-ε
        ε¬Val True x ¬val val-ε = ¬val val-ε
        ε¬Val False x ¬val val-ε = ¬val val-ε
        ε¬Val (Id t₁) x ¬val val-ε = ¬val (Id t₁)
        ε¬Val (unId t₁) (inj₁ x) ¬val ()
        ε¬Val (unId t₁) (inj₂ y) ¬val ()
        ε¬Val (Var τ∈π) x ¬val val-ε = ¬val val-ε
        ε¬Val (Abs t₁) x ¬val val-ε = ¬val (Abs t₁)
        ε¬Val (App t₁ t₂) (inj₁ x) ¬val ()
        ε¬Val (App t₁ t₂) (inj₂ y) ¬val ()
        ε¬Val (If t₁ Then t₂ Else t₃) (inj₁ x) ¬val ()
        ε¬Val (If t₁ Then t₂ Else t₃) (inj₂ y) ¬val ()
        ε¬Val (Return l t₁) (inj₁ x) ¬val ()
        ε¬Val (Return l t₁) (inj₂ y) ¬val ()
        ε¬Val (t₁ >>= t₂) (inj₁ x) ¬val ()
        ε¬Val (t₁ >>= t₂) (inj₂ (Macᴸ l⊑A)) ¬val ()
        ε¬Val (Mac l t₁) x ¬val val-ε = ¬val (Mac t₁)
        ε¬Val (Res l t₁) x ¬val val-ε = ¬val (Res t₁)
        ε¬Val (label l⊑h t₁) (inj₁ x) ¬val ()
        ε¬Val (label {h = H} l⊑h t₁) (inj₂ (Macᴸ l⊑A)) ¬val val-ε with H ⊑? A
        ε¬Val (label l⊑h t₁) (inj₂ (Macᴸ l⊑A)) ¬val () | yes p
        ε¬Val (label l⊑h t₁) (inj₂ (Macᴸ l⊑A)) ¬val () | no ¬p
        ε¬Val (label∙ l⊑h t₁) (inj₁ x) ¬val ()
        ε¬Val (label∙ l⊑h t₁) (inj₂ y) ¬val ()
        ε¬Val (unlabel l⊑h t₁) (inj₁ x) ¬val ()
        ε¬Val (unlabel {α = τ} l⊑h t₁) (inj₂ (Macᴸ l⊑A)) ¬val val-ε with isSecret? τ
        ε¬Val (unlabel l⊑h t₁) (inj₂ (Macᴸ l⊑A)) ¬val () | inj₁ x
        ε¬Val (unlabel l⊑h t₁) (inj₂ (Macᴸ l⊑A)) ¬val () | inj₂ y
        ε¬Val (unlabel∙ l⊑h t₁) (inj₁ x) ¬val ()
        ε¬Val (unlabel∙ l⊑h t₁) (inj₂ (Macᴸ l⊑A)) ¬val ()
        ε¬Val (fork l⊑h t₁) (inj₁ x) ¬val ()
        ε¬Val (fork l⊑h t₁) (inj₂ y) ¬val ()
        ε¬Val (deepDup x) (inj₁ x₁) ¬val ()
        ε¬Val (deepDup x) (inj₂ y) ¬val ()
        ε¬Val ∙ x ¬val ()

εᵀ-Val : ∀ {τ π} {v : Term π τ} -> Public τ -> Value v -> Value (εᵀ v)
εᵀ-Val p （） = （）
εᵀ-Val p True = True
εᵀ-Val p False = False
εᵀ-Val p (Abs t) = Abs (εᵗ (isSecret? _) t)
εᵀ-Val p (Id t) = Id (εᵗ (isSecret? _) t)
εᵀ-Val {Mac l τ} p (Mac t) with isSecret? (Mac l τ)
εᵀ-Val {Mac l τ} p (Mac t) | inj₁ x = ⊥-elim (secretNotPublic x p)
εᵀ-Val {Mac l τ} p (Mac t) | inj₂ y = Mac (εᵗ (isSecret? τ) t)
εᵀ-Val {Res l τ} p (Res t) with isSecret? (Res l τ)
εᵀ-Val {Res l τ} p (Res t) | inj₁ ()
εᵀ-Val {Res l τ} p₁ (Res t) | inj₂ (Res (yes p)) = Res (εᵗ (isSecret? τ) t)
εᵀ-Val {Res l τ} p (Res t) | inj₂ (Res (no ¬p)) = Res ∙

εᵗ¬Var : ∀ {π τ} {t : Term π τ} -> (x : Level τ) -> ¬ IsVar t -> ¬ (IsVar (εᵗ x t))
εᵗ¬Var {t = t} = ε¬Var t
  where ε¬Var : ∀ {π τ} -> (t : Term π τ) (x : Level τ) -> ¬ (IsVar t) -> ¬ (IsVar (εᵗ x t))
        ε¬Var （） x ¬var var-ε = ¬var var-ε
        ε¬Var True x ¬var var-ε = ¬var var-ε
        ε¬Var False x ¬var var-ε = ¬var var-ε
        ε¬Var (Id t₁) x ¬var ()
        ε¬Var (unId t₁) (inj₁ _) ¬var ()
        ε¬Var (unId t₁) (inj₂ _) ¬var ()
        ε¬Var (Var τ∈π) x ¬var _ = ¬var (Var τ∈π)
        ε¬Var (Abs t₁) x ¬var ()
        ε¬Var (App t₁ t₂) (inj₁ _) ¬var ()
        ε¬Var (App t₁ t₂) (inj₂ _) ¬var ()
        ε¬Var (If t₁ Then t₂ Else t₃) (inj₁ _) ¬var ()
        ε¬Var (If t₁ Then t₂ Else t₃) (inj₂ _) ¬var ()
        ε¬Var (Return l t₁) (inj₁ _) ¬var ()
        ε¬Var (Return l t₁) (inj₂ _) ¬var ()
        ε¬Var (t₁ >>= t₂) (inj₁ _) ¬var ()
        ε¬Var (t₁ >>= t₂) (inj₂ (Macᴸ l⊑A)) ¬var ()
        ε¬Var (Mac l t₁) (inj₁ _) ¬var ()
        ε¬Var (Mac l t₁) (inj₂ _) ¬var ()
        ε¬Var (Res l t₁) (inj₁ ()) ¬var _
        ε¬Var (Res l t₁) (inj₂ (Res (yes p))) ¬var ()
        ε¬Var (Res l t₁) (inj₂ (Res (no ¬p))) ¬var ()
        ε¬Var (label {h = H} l⊑h t₁) (inj₁ _) ¬var ()
        ε¬Var (label {h = H} l⊑h t₁) (inj₂ (Macᴸ l⊑A)) ¬var var-ε with H ⊑? A
        ε¬Var (label l⊑h t₁) (inj₂ (Macᴸ l⊑A)) ¬var () | yes p
        ε¬Var (label l⊑h t₁) (inj₂ (Macᴸ l⊑A)) ¬var () | no ¬p
        ε¬Var (label∙ l⊑h t₁) (inj₁ _) ¬var ()
        ε¬Var (label∙ l⊑h t₁) (inj₂ _) ¬var ()
        ε¬Var (unlabel {α = τ} l⊑h t₁) (inj₁ _) ¬var ()
        ε¬Var (unlabel {α = τ} l⊑h t₁) (inj₂ (Macᴸ l⊑A)) ¬var var-ε with isSecret? τ
        ε¬Var (unlabel l⊑h t₁) (inj₂ (Macᴸ l⊑A)) ¬var () | inj₁ x
        ε¬Var (unlabel l⊑h t₁) (inj₂ (Macᴸ l⊑A)) ¬var () | inj₂ y
        ε¬Var (unlabel∙ l⊑h t₁) (inj₁ _) ¬var ()
        ε¬Var (unlabel∙ l⊑h t₁) (inj₂ (Macᴸ l⊑A)) ¬var ()
        ε¬Var (fork l⊑h t₁) (inj₁ _) ¬var ()
        ε¬Var (fork l⊑h t₁) (inj₂ _) ¬var ()
        ε¬Var (deepDup t₁) (inj₁ _) ¬var ()
        ε¬Var (deepDup t₁) (inj₂ _) ¬var ()
        ε¬Var ∙ x ¬var ()

εᵗ-ext : ∀ {τ π} -> (x y : Level τ) (t : Term π τ) -> εᵗ x t ≡ εᵗ y t
εᵗ-ext x y （） = refl
εᵗ-ext x y True = refl
εᵗ-ext x y False = refl
εᵗ-ext x y (Id t) = refl
εᵗ-ext (inj₁ _) (inj₁ _) (unId t) = refl
εᵗ-ext (inj₁ x) (inj₂ y) (unId t) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ y) (inj₁ x) (unId t) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ y) (inj₂ y₁) (unId t) = refl
εᵗ-ext x y (Var x∈π) = refl
εᵗ-ext x₁ y (Abs t) = refl
εᵗ-ext (inj₁ x) (inj₁ x₁) (App t t₁) = refl
εᵗ-ext (inj₁ x) (inj₂ y) (App t t₁) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ y) (inj₁ x) (App t t₁) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ y) (inj₂ y₁) (App t t₁) = refl
εᵗ-ext (inj₁ x) (inj₁ x₁) (If t Then t₁ Else t₂) = refl
εᵗ-ext (inj₁ x) (inj₂ y) (If t Then t₁ Else t₂) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ y) (inj₁ x) (If t Then t₁ Else t₂) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ y) (inj₂ y₁) (If t Then t₁ Else t₂)
  rewrite εᵗ-ext (inj₂ y) (inj₂ y₁) t₁ |  εᵗ-ext (inj₂ y) (inj₂ y₁) t₂ = refl
εᵗ-ext (inj₁ x) (inj₁ x₁) (Return l t) = refl
εᵗ-ext (inj₁ x) (inj₂ y) (Return l t) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ y) (inj₁ x) (Return l t) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ y) (inj₂ y₁) (Return l t) = refl
εᵗ-ext (inj₁ x) (inj₁ x₁) (t >>= t₁) = refl
εᵗ-ext (inj₁ x) (inj₂ y) (t >>= t₁) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ y) (inj₁ x) (t >>= t₁) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ (Macᴸ l⊑A)) (inj₂ (Macᴸ l⊑A₁)) (t >>= t₁)
  rewrite εᵗ-ext (inj₂ (Macᴸ l⊑A)) (inj₂ (Macᴸ l⊑A₁)) t = refl
εᵗ-ext (inj₁ x) (inj₁ x₁) (Mac l t) = refl
εᵗ-ext (inj₁ x) (inj₂ y) (Mac l t) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ y) (inj₁ x) (Mac l t) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ y) (inj₂ y₁) (Mac l t) = refl
εᵗ-ext (inj₁ ()) (inj₁ x₁) (Res l t)
εᵗ-ext (inj₁ ()) (inj₂ y) (Res l t)
εᵗ-ext (inj₂ y) (inj₁ ()) (Res l t)
εᵗ-ext (inj₂ (Res (yes p))) (inj₂ (Res (yes p₁))) (Res l t) = refl
εᵗ-ext (inj₂ (Res (yes p))) (inj₂ (Res (no ¬p))) (Res l t) = ⊥-elim (¬p p)
εᵗ-ext (inj₂ (Res (no ¬p))) (inj₂ (Res (yes p))) (Res l t) = ⊥-elim (¬p p)
εᵗ-ext (inj₂ (Res (no ¬p))) (inj₂ (Res (no ¬p₁))) (Res l t) = refl
εᵗ-ext (inj₁ x) (inj₁ x₁) (label l⊑h t) = refl
εᵗ-ext (inj₁ x) (inj₂ y) (label l⊑h t) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ y) (inj₁ x) (label l⊑h t) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ (Macᴸ l⊑A)) (inj₂ (Macᴸ l⊑A₁)) (label l⊑h t) = refl
εᵗ-ext (inj₁ x) (inj₁ x₁) (label∙ l⊑h t) = refl
εᵗ-ext (inj₁ x) (inj₂ y) (label∙ l⊑h t) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ y) (inj₁ x) (label∙ l⊑h t) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ y) (inj₂ y₁) (label∙ l⊑h t) = refl
εᵗ-ext (inj₁ x) (inj₁ x₁) (unlabel l⊑h t) = refl
εᵗ-ext (inj₁ x) (inj₂ y) (unlabel l⊑h t) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ y) (inj₁ x) (unlabel l⊑h t) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ (Macᴸ l⊑A)) (inj₂ (Macᴸ l⊑A₁)) (unlabel l⊑h t) = refl
εᵗ-ext (inj₁ x) (inj₁ x₁) (unlabel∙ l⊑h t) = refl
εᵗ-ext (inj₁ x) (inj₂ y) (unlabel∙ l⊑h t) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ y) (inj₁ x) (unlabel∙ l⊑h t) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ (Macᴸ l⊑A)) (inj₂ (Macᴸ l⊑A₁)) (unlabel∙ l⊑h t) = refl
εᵗ-ext (inj₁ x) (inj₁ x₁) (fork l⊑h t) = refl
εᵗ-ext (inj₁ x) (inj₂ y) (fork l⊑h t) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ y) (inj₁ x) (fork l⊑h t) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ y) (inj₂ y₁) (fork l⊑h t) = refl
εᵗ-ext (inj₁ x) (inj₁ x₁) (deepDup x₂) rewrite εᵗ-ext (inj₁ x) (inj₁ x₁) x₂ = refl
εᵗ-ext (inj₁ x) (inj₂ y) (deepDup x₁) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ y) (inj₁ x) (deepDup x₁) = ⊥-elim (secretNotPublic x y)
εᵗ-ext (inj₂ y) (inj₂ y₁) (deepDup x₁) rewrite εᵗ-ext (inj₂ y) (inj₂ y₁) x₁ = refl
εᵗ-ext x y ∙ = refl

open import Data.Product as P
open import Data.Maybe as M
open import Function

εᴱ : ∀ {l π} -> Dec (l ⊑ A) ->  Env l π -> Env l π
εᴱ (yes p) [] = []
εᴱ (yes p) (mt ∷ Δ) = (M.map (εᵗ (isSecret? _)) mt) ∷ (εᴱ (yes p) Δ)
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

--------------------------------------------------------------------------------

ε : ∀ {l τ ls} -> Level (Mac l τ) ->  State ls l (Mac l τ) -> State ls l (Mac l τ)
ε {l} {τ} (inj₁ ¬p) (⟨_,_,_⟩ {π = π} Γ t S) = ⟨ (εᴴ Γ) , ∙ {π = π} {{Mac l τ}} , ∙ ⟩
ε (inj₂ p) ⟨ Γ , t , S ⟩ = ⟨ εᴴ Γ , εᵀ t , εˢ S ⟩

--------------------------------------------------------------------------------

ε-wken : ∀ {τ π₁ π₂} -> (x : Level τ) -> (t : Term π₁ τ) (p : π₁ ⊆ˡ π₂) -> εᵗ x (wken t p) ≡ wken (εᵗ x t) p
ε-wken x （） p = refl
ε-wken x True p = refl
ε-wken x False p = refl
ε-wken x (Id t) p rewrite ε-wken (isSecret? _) t p = refl
ε-wken (inj₁ x) (unId t) p = refl
ε-wken (inj₂ y) (unId t) p rewrite ε-wken (inj₂ Id) t p = refl
ε-wken x (Var x∈π) p = refl
ε-wken x₁ (Abs t) p rewrite ε-wken (isSecret? _) t (cons p) = refl
ε-wken (inj₁ x) (App t t₁) p = refl
ε-wken (inj₂ y) (App t t₁) p rewrite ε-wken (inj₂ Fun) t p | ε-wken (isSecret? _) t₁ p = refl
ε-wken (inj₁ x) (If t Then t₁ Else t₂) p = refl
ε-wken (inj₂ y) (If t Then t₁ Else t₂) p
  rewrite ε-wken (inj₂ Bool) t p | ε-wken (inj₂ y) t₁ p | ε-wken (inj₂ y) t₂ p = refl
ε-wken (inj₁ x) (Return l t) p = refl
ε-wken (inj₂ y) (Return l t) p
  rewrite ε-wken (isSecret? _) t p = refl
ε-wken (inj₁ x) (t >>= t₁) p = refl
ε-wken (inj₂ (Macᴸ y)) (t >>= t₁) p
  rewrite ε-wken (inj₂ (Macᴸ y)) t p | ε-wken (inj₂ Fun)  t₁ p = refl
ε-wken (inj₁ x) (Mac l t) p = refl
ε-wken (inj₂ y) (Mac l t) p
  rewrite ε-wken (isSecret? _) t p = refl
ε-wken (inj₁ ()) (Res l t) p
ε-wken (inj₂ (Res (yes p))) (Res l t) p₁
  rewrite ε-wken (isSecret? _) t p₁ = refl
ε-wken (inj₂ (Res (no ¬p))) (Res l t) p = refl
ε-wken (inj₁ x) (label l⊑h t) p = refl
ε-wken (inj₂ (Macᴸ l⊑A)) (label {h = H} l⊑h t) p with H ⊑? A
ε-wken (inj₂ (Macᴸ l⊑A)) (label l⊑h t) p₁ | yes p rewrite ε-wken (isSecret? _) t p₁ = refl
ε-wken (inj₂ (Macᴸ l⊑A)) (label l⊑h t) p | no ¬p rewrite ε-wken (isSecret? _) t p = refl
ε-wken (inj₁ x) (label∙ l⊑h t) p = refl
ε-wken (inj₂ y) (label∙ l⊑h t) p rewrite ε-wken (isSecret? _) t p = refl
ε-wken (inj₁ x) (unlabel l⊑h t) p = refl
ε-wken (inj₂ (Macᴸ L⊑A)) (unlabel {α = τ} l⊑h t) p with isSecret? τ
ε-wken (inj₂ (Macᴸ L⊑A)) (unlabel l⊑h t) p | inj₁ x rewrite ε-wken (isSecret? _) t p = refl
ε-wken (inj₂ (Macᴸ L⊑A)) (unlabel l⊑h t) p | inj₂ y rewrite ε-wken (isSecret? _) t p = refl
ε-wken (inj₁ x) (unlabel∙ l⊑h t) p = refl
ε-wken (inj₂ (Macᴸ L⊑A)) (unlabel∙ l⊑h t) p rewrite ε-wken (isSecret? _) t p = refl
ε-wken (inj₁ x) (fork l⊑h t) p = refl
ε-wken (inj₂ y) (fork {h = H} l⊑h t) p rewrite ε-wken (isSecret? _) t p = refl
ε-wken (inj₁ x) (deepDup x₁) p rewrite ε-wken (inj₁ x) x₁ p = refl
ε-wken (inj₂ y) (deepDup x₁) p rewrite ε-wken (inj₂ y) x₁ p = refl
ε-wken x ∙ p = refl

ε-subst : ∀ {τ τ' π} (t₁ : Term π τ') (t₂ : Term (τ' ∷ π) τ) (x : Level τ) ->
                 εᵗ x (subst t₁ t₂) ≡ subst (εᵀ t₁) (εᵗ x t₂)
ε-subst {π = π} = ε-tm-subst [] π
  where

        ε-var-subst   :  ∀ {α β} (π₁ : Context) (π₂ : Context) (t₁ : Term π₂ α) (β∈π : β ∈ (π₁ ++ [ α ] ++ π₂))
                           (p : Level β)
                      ->  εᵗ p (var-subst π₁ π₂ t₁ β∈π) ≡ var-subst π₁ π₂ (εᵗ (isSecret? _) t₁) β∈π
        ε-var-subst [] π₂ t₁ here p rewrite εᵗ-ext p (isSecret? _) t₁ = refl
        ε-var-subst [] π₂ t₁ (there x∈π) p = refl
        ε-var-subst (._ ∷ π₁) π₂ t₁ here p = refl
        ε-var-subst (x₁ ∷ π₁) π₂ t₁ (there x∈π) p
          rewrite ε-wken p (var-subst π₁ π₂ t₁ x∈π) (drop {x₁} refl-⊆ˡ) | ε-var-subst π₁ π₂ t₁ x∈π p = refl

        ε-tm-subst : ∀ {τ τ'} (π₁ : Context) (π₂ : Context) (t₁ : Term π₂ τ') (t₂ : Term (π₁ ++ [ τ' ] ++ π₂) τ) (x : Level τ)
                   ->  εᵗ x (tm-subst π₁ π₂ t₁ t₂) ≡ tm-subst π₁ π₂ (εᵗ (isSecret? _) t₁) (εᵗ x t₂)
        ε-tm-subst π₁ π₂ t₁ （） p = refl
        ε-tm-subst π₁ π₂ t₁ True p = refl
        ε-tm-subst π₁ π₂ t₁ False p = refl
        ε-tm-subst π₁ π₂ t₁ (Id t₂) p rewrite ε-tm-subst π₁ π₂ t₁ t₂ (isSecret? _) = refl
        ε-tm-subst π₁ π₂ t₁ (unId t₂) (inj₁ x₁) = refl
        ε-tm-subst π₁ π₂ t₁ (unId t₂) (inj₂ y) rewrite ε-tm-subst π₁ π₂ t₁ t₂ (isSecret? _) = refl
        ε-tm-subst π₁ π₂ t₁ (Var τ∈π) p rewrite ε-var-subst π₁ π₂ t₁ τ∈π p = refl
        ε-tm-subst π₁ π₂ t₁ (Abs t₂) p rewrite  ε-tm-subst (_ ∷ π₁) _ t₁ t₂ (isSecret? _) = refl
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
        ε-tm-subst π₁ π₂ t₁ (deepDup x) (inj₁ x₁) rewrite ε-tm-subst π₁ π₂ t₁ x (inj₁ x₁) = refl
        ε-tm-subst π₁ π₂ t₁ (deepDup x) (inj₂ y) rewrite ε-tm-subst π₁ π₂ t₁ x (inj₂ y) = refl
        ε-tm-subst π₁ π₂ t₁ ∙ p = refl


εᵗ-dup-ufv-≡ : ∀ {π τ} -> (x : Level τ) (vs : Vars π) (t : Term π τ) ->  εᵗ x (dup-ufv vs t) ≡ dup-ufv vs (εᵗ x t)
εᵗ-dup-ufv-≡ x vs （） = refl
εᵗ-dup-ufv-≡ x vs True = refl
εᵗ-dup-ufv-≡ x vs False = refl
εᵗ-dup-ufv-≡ x vs (Id t) rewrite εᵗ-dup-ufv-≡ (isSecret? _) vs t = refl
εᵗ-dup-ufv-≡ (inj₁ x) vs (unId t) = refl
εᵗ-dup-ufv-≡ (inj₂ y) vs (unId t) rewrite εᵗ-dup-ufv-≡ (inj₂ Id) vs t = refl
εᵗ-dup-ufv-≡ x vs (Var τ∈π) with memberⱽ τ∈π vs
εᵗ-dup-ufv-≡ x vs (Var τ∈π) | yes p = refl
εᵗ-dup-ufv-≡ (inj₁ x) vs (Var τ∈π) | no ¬p = refl -- Doh!
εᵗ-dup-ufv-≡ (inj₂ y) vs (Var τ∈π) | no ¬p = refl
εᵗ-dup-ufv-≡ x vs (Abs t)
  rewrite εᵗ-dup-ufv-≡ (isSecret? _) (here ∷ (mapⱽ there vs)) t = refl
εᵗ-dup-ufv-≡ (inj₁ x) vs (App t t₁) = refl
εᵗ-dup-ufv-≡ (inj₂ y) vs (App t t₁)
  rewrite εᵗ-dup-ufv-≡ (isSecret? _ ) vs t | εᵗ-dup-ufv-≡ (isSecret? _ ) vs t₁ = refl
εᵗ-dup-ufv-≡ (inj₁ x) vs (If t Then t₁ Else t₂) = refl
εᵗ-dup-ufv-≡ (inj₂ y) vs (If t Then t₁ Else t₂)
  rewrite εᵗ-dup-ufv-≡ (inj₂ Bool) vs t | εᵗ-dup-ufv-≡ (inj₂ y) vs t₁ | εᵗ-dup-ufv-≡ (inj₂ y) vs t₂ = refl
εᵗ-dup-ufv-≡ (inj₁ x) vs (Return l t) = refl
εᵗ-dup-ufv-≡ (inj₂ y) vs (Return l t)
  rewrite εᵗ-dup-ufv-≡ (isSecret? _) vs t = refl
εᵗ-dup-ufv-≡ (inj₁ x) vs (t >>= t₁) = refl
εᵗ-dup-ufv-≡ (inj₂ (Macᴸ h⊑A)) vs (t >>= t₁)
  rewrite εᵗ-dup-ufv-≡ (inj₂ (Macᴸ h⊑A)) vs t | εᵗ-dup-ufv-≡ (isSecret? _) vs t₁ = refl
εᵗ-dup-ufv-≡ (inj₁ x) vs (Mac l t) = refl
εᵗ-dup-ufv-≡ (inj₂ y) vs (Mac l t)
  rewrite εᵗ-dup-ufv-≡ (isSecret? _) vs t = refl
εᵗ-dup-ufv-≡ (inj₁ ()) vs (Res l t)
εᵗ-dup-ufv-≡ (inj₂ (Res (yes p))) vs (Res l t)
  rewrite εᵗ-dup-ufv-≡ (isSecret? _) vs t = refl
εᵗ-dup-ufv-≡ (inj₂ (Res (no ¬p))) vs (Res l t)
  rewrite εᵗ-dup-ufv-≡ (isSecret? _) vs t = refl
εᵗ-dup-ufv-≡ (inj₁ x) vs (label l⊑h t) = refl
εᵗ-dup-ufv-≡ (inj₂ (Macᴸ l⊑A)) vs (label {h = H} l⊑h t) with H ⊑? A
εᵗ-dup-ufv-≡ (inj₂ (Macᴸ l⊑A)) vs (label l⊑h t) | yes p
  rewrite εᵗ-dup-ufv-≡ (isSecret? _) vs t = refl
εᵗ-dup-ufv-≡ (inj₂ (Macᴸ l⊑A)) vs (label l⊑h t) | no ¬p
  rewrite εᵗ-dup-ufv-≡ (isSecret? _) vs t = refl
εᵗ-dup-ufv-≡ (inj₁ x) vs (label∙ l⊑h t) = refl
εᵗ-dup-ufv-≡ (inj₂ y) vs (label∙ l⊑h t)
  rewrite εᵗ-dup-ufv-≡ (isSecret? _) vs t = refl
εᵗ-dup-ufv-≡ (inj₁ x) vs (unlabel l⊑h t) = refl
εᵗ-dup-ufv-≡ (inj₂ (Macᴸ l⊑A)) vs (unlabel {α = τ} l⊑h t) with isSecret? τ
εᵗ-dup-ufv-≡ (inj₂ (Macᴸ l⊑A)) vs (unlabel l⊑h t) | inj₁ x
  rewrite εᵗ-dup-ufv-≡ (isSecret? _) vs t = refl
εᵗ-dup-ufv-≡ (inj₂ (Macᴸ l⊑A)) vs (unlabel l⊑h t) | inj₂ y
  rewrite εᵗ-dup-ufv-≡ (isSecret? _) vs t = refl
εᵗ-dup-ufv-≡ (inj₁ x) vs (unlabel∙ l⊑h t) = refl
εᵗ-dup-ufv-≡ (inj₂ (Macᴸ l⊑A)) vs (unlabel∙ l⊑h t)
  rewrite εᵗ-dup-ufv-≡ (isSecret? _) vs t = refl
εᵗ-dup-ufv-≡ (inj₁ x) vs (fork l⊑h t) = refl
εᵗ-dup-ufv-≡ (inj₂ y) vs (fork l⊑h t)
  rewrite εᵗ-dup-ufv-≡ (isSecret? _) vs t = refl
εᵗ-dup-ufv-≡ x vs (deepDup t) = refl
εᵗ-dup-ufv-≡ x vs ∙ = refl

-- This is the proof that it is impossible to turn a high computation into a low one
-- We need this lemma to discharge those cases in which the Stack produce a Mac L
-- computation but the current term under evaluation has type Mac H.
¬secureStack : ∀ {l h τ₁ τ₂} -> Secret (Mac h τ₁) -> Public (Mac l τ₂) -> Stack l (Mac h τ₁) (Mac l τ₂) -> ⊥
¬secureStack (Macᴴ h⋤A) (Macᴸ l⊑A) [] = ⊥-elim (h⋤A l⊑A)
¬secureStack x y (# x∈π ∷ S) = ¬secureStack x y S
¬secureStack (Macᴴ h⋤A) (Macᴸ l⊑A) (Bind x₁ ∷ S) = ¬secureStack (Macᴴ h⋤A) (Macᴸ l⊑A) S
¬secureStack (Macᴴ h⋤A) (Macᴸ l⊑A) ∙ = {!!} -- No because ∙ can freely choose types also the insecure ones

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
            Γ' ≔ Γ [ l ↦ insert t Δ ]ᴴ -> εᴴ Γ' ≔ (εᴴ Γ) [ l ↦ insert (εᵗ (isSecret? τ) t) (εᴱ (yes l⊑A) Δ) ]ᴴ
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
ε-sim ._ ._ (inj₁ (Macᴴ h⋤A)) (DeepDup Δ∈Γ t∈Δ uᴴ)
  rewrite insertᴴ∙ h⋤A uᴴ = Hole
ε-sim ._ ._ (inj₁ (Macᴴ h⋤A)) (DeepDup' ¬var Δ∈Γ uᴴ)
  rewrite insertᴴ∙ h⋤A uᴴ = Hole
ε-sim ⟨ x , .∙ , .∙ ⟩ ⟨ .x , .∙ , .∙ ⟩ (inj₁ _) Hole = Hole

ε-sim ._ ._ (inj₂ y) (App₁ {τ₂ = τ₂} Δ∈Γ uᴴ) with isSecret? τ₂
ε-sim ._ ._ (inj₂ y) (App₁ {S = S} Δ∈Γ uᴴ) | inj₁ (Macᴴ h⋤A) = ⊥-elim (¬secureStack (Macᴴ h⋤A) y S)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (App₁ Δ∈Γ uᴴ) | inj₂ y = App₁ (memberᴴ l⊑A Δ∈Γ) (insertᴴ l⊑A uᴴ)
ε-sim ⟨ Γ , Abs t , ._ ∷ S ⟩ ._ (inj₂ y') (App₂ {β = β} y∈π x∈π) rewrite ε-subst (Var x∈π) t (isSecret? _) = App₂ y∈π x∈π
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Var₁ Δ∈Γ x∈π t∈Δ ¬val rᴱ uᴴ) = Var₁ (memberᴴ l⊑A Δ∈Γ) x∈π (memberᴱ l⊑A t∈Δ) (εᵀ¬Val ¬val) (updateᴱ l⊑A rᴱ) (updateᴴ l⊑A uᴴ)
ε-sim ⟨ _ , _ , S ⟩ ._ (inj₂ y) (Var₁' {τ = τ} Δ∈Γ τ∈π v∈Δ val) with isSecret? τ
ε-sim ⟨ _ , _ , S ⟩ ._ (inj₂ (Macᴸ y)) (Var₁' Δ∈Γ τ∈π v∈Δ val) | inj₁ (Macᴴ x) = ⊥-elim (¬secureStack (Macᴴ x) (Macᴸ y) S)
ε-sim ⟨ _ , _ , S ⟩ ._ (inj₂ (Macᴸ l⊑A)) (Var₁' {v = v} Δ∈Γ τ∈π v∈Δ val) | inj₂ y
  rewrite εᵗ-ext (inj₂ y) (isSecret? _) v = Var₁' (memberᴴ l⊑A Δ∈Γ) τ∈π (memberᴱ l⊑A v∈Δ) (εᵀ-Val y val)
ε-sim ._ ._ (inj₂ y) (Var₂ {τ = τ} Δ∈Γ τ∈π val uᴱ uᴴ) with isSecret? τ
ε-sim ._ ._ (inj₂ (Macᴸ y)) (Var₂ {S = S} Δ∈Γ τ∈π val uᴱ uᴴ) | inj₁ (Macᴴ x) = ⊥-elim (¬secureStack (Macᴴ x) (Macᴸ y) S)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Var₂ {v = v} Δ∈Γ τ∈π val uᴱ uᴴ) | inj₂ y
  rewrite εᵗ-ext (inj₂ y) (isSecret? _) v = Var₂ (memberᴴ l⊑A Δ∈Γ) τ∈π (εᵀ-Val y val) (updateᴱ l⊑A uᴱ) (updateᴴ l⊑A uᴴ)
ε-sim ⟨ _ , ._ , S ⟩ ._ (inj₂ y) (If {τ = τ}) with isSecret? τ
ε-sim ⟨ x , ._ , S ⟩ ._ (inj₂ y) If | inj₁ (Macᴴ h⋤A) = ⊥-elim (¬secureStack (Macᴴ h⋤A) y S)
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
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (UnId₁ {S = S}) | inj₁ (Macᴴ h⋤A) = ⊥-elim (¬secureStack (Macᴴ h⋤A) (Macᴸ l⊑A) S)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) UnId₁ | inj₂ y = UnId₁
ε-sim ._ ._ (inj₂ p) UnId₂ = UnId₂
ε-sim ._ ._ (inj₂ (Macᴸ {τ} {l} l⊑A)) (Fork p₁) with isSecret? (Mac l τ)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Fork p₁) | inj₁ x = ⊥-elim (secretNotPublic x (Macᴸ l⊑A))
ε-sim ._ ._ (inj₂ (Macᴸ {l = l} l⊑A)) (Fork p₁) | inj₂ y with l ⊑? A
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Fork p₁) | inj₂ y | yes p = Fork p₁
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (Fork p₁) | inj₂ y | no ¬p = ⊥-elim (¬p l⊑A)
ε-sim ._ ._ (inj₂ p) (DeepDup {τ = τ} Δ∈Γ t∈Δ uᴴ) with isSecret? τ
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (DeepDup {S = S} Δ∈Γ t∈Δ uᴴ) | inj₁ (Macᴴ h⋤A) = ⊥-elim (¬secureStack (Macᴴ h⋤A) (Macᴸ l⊑A) S)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (DeepDup {t = t} Δ∈Γ t∈Δ uᴴ) | inj₂ y with insertᴴ l⊑A uᴴ
... | uᴴ' rewrite εᵗ-dup-ufv-≡ (isSecret? _) [] t = DeepDup (memberᴴ l⊑A Δ∈Γ) (memberᴱ l⊑A t∈Δ) uᴴ'
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (DeepDup' {τ = τ} ¬var Δ∈Γ uᴴ) with isSecret? τ
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (DeepDup'{S = S}  ¬var Δ∈Γ uᴴ) | inj₁ (Macᴴ h⋤A) = ⊥-elim (¬secureStack (Macᴴ h⋤A) (Macᴸ l⊑A) S)
ε-sim ._ ._ (inj₂ (Macᴸ l⊑A)) (DeepDup' {t = t} ¬var Δ∈Γ uᴴ) | inj₂ y
  rewrite εᵗ-ext (inj₂ y) (isSecret? _) t = DeepDup' (εᵗ¬Var (isSecret? _) ¬var) (memberᴴ l⊑A Δ∈Γ) (insertᴴ l⊑A uᴴ)
ε-sim ._ ._ (inj₂ p) Hole = Hole
