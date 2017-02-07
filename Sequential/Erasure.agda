import Lattice as L

-- A is the security level of the attacker
module Sequential.Erasure (𝓛 : L.Lattice) (A : L.Label 𝓛) where

open import Types 𝓛
open import Sequential.Calculus 𝓛
open import Sequential.Semantics 𝓛

open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding (subst ; [_])
open import Relation.Nullary
open import Data.Empty

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
  Addr : Public Addr

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
isSecret? Addr = inj₂ Addr
--------------------------------------------------------------------------------

εᵀ : ∀ {τ π} -> Term π τ -> Term π τ
εᵀ （） = （）
εᵀ True = True
εᵀ False = False
εᵀ (Id t) = Id (εᵀ t)
εᵀ (unId t) = unId (εᵀ t)
εᵀ (Var τ∈π) = Var τ∈π
εᵀ (Abs t) = Abs (εᵀ t)
εᵀ (App t t₁) = App (εᵀ t) (εᵀ t₁)
εᵀ (If t Then t₁ Else t₂) = If (εᵀ t) Then (εᵀ t₁) Else (εᵀ t₂)
εᵀ (Return l t) = Return l (εᵀ t)
εᵀ (t >>= t₁) = (εᵀ t) >>= (εᵀ t₁)
εᵀ (Mac l t) = Mac l (εᵀ t)
εᵀ (Res l t) with l ⊑? A
εᵀ (Res l t) | yes p = Res l (εᵀ t)
εᵀ (Res l t) | no ¬p = Res l ∙
εᵀ (label {h = H} l⊑h t) with H ⊑? A
εᵀ (label l⊑h t) | yes p = label l⊑h (εᵀ t)
εᵀ (label l⊑h t) | no ¬p = label∙ l⊑h (εᵀ t)
εᵀ (label∙ l⊑h t) = label∙ l⊑h (εᵀ t)
εᵀ (unlabel l⊑h t) = unlabel l⊑h (εᵀ t)
εᵀ (new {h = H} l⊑h t) with H ⊑? A
... | yes p = new l⊑h (εᵀ t)
... | no ¬p = new∙ l⊑h (εᵀ t)
εᵀ (new∙ l⊑h t) = new∙ l⊑h (εᵀ t)
εᵀ (read l⊑h t) = read l⊑h (εᵀ t)
εᵀ (write {h = H} l⊑h t₁ t₂) with H ⊑? A
... | yes p = write l⊑h (εᵀ t₁) (εᵀ t₂)
... | no ¬p = write∙ l⊑h (εᵀ t₁) (εᵀ t₂)
εᵀ (write∙ l⊑h t₁ t₂) = write∙ l⊑h (εᵀ t₁) (εᵀ t₂)
εᵀ (#[ n ]) = #[ n ]
εᵀ (#[ n ]ᴰ) = #[ n ]ᴰ
εᵀ (fork {h = h} l⊑h t) with h ⊑? A
... | yes _ = fork l⊑h (εᵀ t)
... | no _ = fork∙ l⊑h (εᵀ t)
εᵀ (fork∙ l⊑h t) = fork∙ l⊑h (εᵀ t)
εᵀ (deepDup t) = deepDup (εᵀ t)
εᵀ ∙ = ∙

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
εᵀ¬Val {t = new {h = H} l⊑h t} ¬val val-ε with H ⊑? A
εᵀ¬Val {π} {._} {new l⊑h t} ¬val () | yes p
εᵀ¬Val {π} {._} {new l⊑h t} ¬val () | no ¬p
εᵀ¬Val {t = new∙ l⊑h t} ¬val ()
εᵀ¬Val {t = read l⊑h t} ¬val ()
εᵀ¬Val {t = write {h = H} l⊑h t₁ t₂} ¬val val-ε with H ⊑? A
εᵀ¬Val {π} {._} {write l⊑h t₁ t₂} ¬val () | yes p
εᵀ¬Val {π} {._} {write l⊑h t₁ t₂} ¬val () | no ¬p
εᵀ¬Val {t = write∙ l⊑h t₁ t₂} ¬val ()
εᵀ¬Val {t = #[ t ]} ¬val val-ε = ¬val #[ t ]
εᵀ¬Val {t = #[ t ]ᴰ} ¬val val-ε = ¬val #[ t ]ᴰ
εᵀ¬Val {t = fork {h = h} l⊑h t} ¬val val-ε with h ⊑? A
εᵀ¬Val {t = fork l⊑h t} ¬val ()  | yes _
εᵀ¬Val {t = fork l⊑h t} ¬val () | no _
εᵀ¬Val {t = fork∙ l⊑h t} ¬val ()
εᵀ¬Val {t = deepDup t} ¬val ()
εᵀ¬Val {t = ∙} ¬val ()

εᵀ-Val : ∀ {τ π} {v : Term π τ} -> Value v -> Value (εᵀ v)
εᵀ-Val （） = （）
εᵀ-Val True = True
εᵀ-Val False = False
εᵀ-Val (Abs t) = Abs (εᵀ t)
εᵀ-Val (Id t) = Id (εᵀ t)
εᵀ-Val {Mac l τ} (Mac t) = Mac _
εᵀ-Val {Res l τ} (Res t) with l ⊑? A
εᵀ-Val {Res l τ} (Res t) | yes p = Res (εᵀ t)
εᵀ-Val {Res l τ} (Res t) | no ¬p = Res ∙
εᵀ-Val (#[ n ]) = #[ n ]
εᵀ-Val (#[ n ]ᴰ) = #[ n ]ᴰ

εᵀ¬Var : ∀ {π τ} {t : Term π τ} -> ¬ IsVar t -> ¬ (IsVar (εᵀ t))
εᵀ¬Var {t = （）} ¬var var-ε = ¬var var-ε
εᵀ¬Var {t = True} ¬var var-ε = ¬var var-ε
εᵀ¬Var {t = False} ¬var var-ε = ¬var var-ε
εᵀ¬Var {t = Id t} ¬var ()
εᵀ¬Var {t = unId t} ¬var ()
εᵀ¬Var {t = Var τ∈π} ¬var var-ε = ¬var (Var τ∈π)
εᵀ¬Var {t = Abs t} ¬var ()
εᵀ¬Var {t = App t t₁} ¬var ()
εᵀ¬Var {t = If t Then t₁ Else t₂} ¬var ()
εᵀ¬Var {t = Return l t} ¬var ()
εᵀ¬Var {t = t >>= t₁} ¬var ()
εᵀ¬Var {t = Mac l t} ¬var ()
εᵀ¬Var {t = Res l t} ¬var var-ε with l ⊑? A
εᵀ¬Var {π} {._} {Res l t} ¬var () | yes p
εᵀ¬Var {π} {._} {Res l t} ¬var () | no ¬p
εᵀ¬Var {t = label {h = H} l⊑h t} ¬var var-ε with H ⊑? A
εᵀ¬Var {π} {._} {label l⊑h t} ¬var () | yes p
εᵀ¬Var {π} {._} {label l⊑h t} ¬var () | no ¬p
εᵀ¬Var {t = label∙ l⊑h t} ¬var ()
εᵀ¬Var {t = unlabel l⊑h t} ¬var ()
εᵀ¬Var {t = new {h = H} l⊑h t} ¬var val-ε with H ⊑? A
εᵀ¬Var {π} {._} {new l⊑h t} ¬var () | yes p
εᵀ¬Var {π} {._} {new l⊑h t} ¬var () | no ¬p
εᵀ¬Var {t = new∙ l⊑h t} ¬var ()
εᵀ¬Var {t = read l⊑h t} ¬var ()
εᵀ¬Var {t = write {h = H} l⊑h t₁ t₂} ¬var val-ε with H ⊑? A
εᵀ¬Var {π} {._} {write l⊑h t₁ t₂} ¬var () | yes p
εᵀ¬Var {π} {._} {write l⊑h t₁ t₂} ¬var () | no ¬p
εᵀ¬Var {t = write∙ l⊑h t₁ t₂} ¬var ()
εᵀ¬Var {t = #[ t ]} ¬var ()
εᵀ¬Var {t = #[ t ]ᴰ} ¬var ()
εᵀ¬Var {t = fork {h = h} l⊑h t} ¬var var-ε with h ⊑? A
εᵀ¬Var {t = fork l⊑h t} ¬var () | yes _
εᵀ¬Var {t = fork l⊑h t} ¬var () | no _
εᵀ¬Var {t = fork∙ l⊑h t} ¬var ()
εᵀ¬Var {t = deepDup t} ¬var ()
εᵀ¬Var {t = ∙} ¬var ()

εᵀ¬Fork : ∀ {π τ} {t : Term π τ} -> ¬ (IsFork t) -> ¬ (IsFork (εᵀ t))
εᵀ¬Fork {t = （）} ¬fork ()
εᵀ¬Fork {t = True} ¬fork ()
εᵀ¬Fork {t = False} ¬fork ()
εᵀ¬Fork {t = Id t} ¬fork ()
εᵀ¬Fork {t = unId t} ¬fork ()
εᵀ¬Fork {t = Var τ∈π} ¬fork ()
εᵀ¬Fork {t = Abs t} ¬fork ()
εᵀ¬Fork {t = App t t₁} ¬fork ()
εᵀ¬Fork {t = If t Then t₁ Else t₂} ¬fork ()
εᵀ¬Fork {t = Return l t} ¬fork ()
εᵀ¬Fork {t = t >>= t₁} ¬fork ()
εᵀ¬Fork {t = Mac l t} ¬fork ()
εᵀ¬Fork {t = Res l t} ¬fork ()
εᵀ¬Fork {t = label l⊑h t} ¬fork ()
εᵀ¬Fork {t = label∙ l⊑h t} ¬fork ()
εᵀ¬Fork {t = unlabel l⊑h t} ¬fork ()
εᵀ¬Fork {t = read x t} ¬fork ()
εᵀ¬Fork {t = write {h = h} x t t₁} ¬fork a with h ⊑? A
εᵀ¬Fork {t = write x t t₁} ¬fork () | yes p
εᵀ¬Fork {t = write x t t₁} ¬fork () | no _
εᵀ¬Fork {t = write∙ x t t₁} ¬fork ()
εᵀ¬Fork {t = new x t} ¬fork ()
εᵀ¬Fork {t = new∙ x t} ¬fork ()
εᵀ¬Fork {t = #[ x ]} ¬fork ()
εᵀ¬Fork {t = #[ x ]ᴰ} ¬fork ()
εᵀ¬Fork {t = fork l⊑h t} ¬fork x = ¬fork (Fork l⊑h t)
εᵀ¬Fork {t = fork∙ l⊑h t} ¬fork x = ¬fork (Fork∙ l⊑h t)
εᵀ¬Fork {t = deepDup t} ¬fork ()
εᵀ¬Fork {t = ∙} ¬fork ()

open import Data.Maybe as M
open import Function

εᴱ : ∀ {l π} ->  Env l π -> Env l π
εᴱ [] = []
εᴱ (t ∷ Δ) = (M.map εᵀ t) ∷ (εᴱ Δ)
εᴱ ∙ = ∙

-- εᴱ : ∀ {l π} -> Dec (l ⊑ A) ->  Env l π -> Env l π
-- εᴱ (yes p) [] = []
-- εᴱ (yes p) (mt ∷ Δ) = (M.map εᵀ mt) ∷ (εᴱ (yes p) Δ)
-- εᴱ (yes p) ∙ = ∙
-- εᴱ (no ¬p) Δ = ∙

-- Proof irrelevance for εᴱ
-- εᴱ-ext : ∀ {l π} -> (x y : Dec (l ⊑ A)) (Δ : Env l π) -> εᴱ x Δ ≡ εᴱ y Δ
-- εᴱ-ext (yes p) (yes p₁) [] = refl
-- εᴱ-ext (yes p) (yes p₁) (t ∷ Δ) rewrite εᴱ-ext (yes p) (yes p₁) Δ = refl
-- εᴱ-ext (yes p) (yes p₁) ∙ = refl
-- εᴱ-ext (yes p) (no ¬p) Δ = ⊥-elim (¬p p)
-- εᴱ-ext (no ¬p) (yes p) Δ = ⊥-elim (¬p p)
-- εᴱ-ext (no ¬p) (no ¬p₁) Δ = refl

-- Heaps Erasure Function
-- εᴴ : ∀ {ls} -> Heaps ls -> Heaps ls
-- εᴴ [] = []
-- εᴴ (Δ ∷ Γ) = (εᴱ ( _ ⊑? A) Δ) ∷ εᴴ Γ

--------------------------------------------------------------------------------

εᶜ : ∀ {τ₁ τ₂ l} -> Cont l τ₁ τ₂ -> Cont l τ₁ τ₂
εᶜ (Var x∈π) = Var x∈π
εᶜ (# x∈π) = # x∈π
εᶜ {τ₂ = τ₂} (Then t₁ Else t₂) = Then (εᵀ t₁) Else εᵀ t₂
εᶜ {τ₁ = Mac .l α} {τ₂ = Mac l β} (Bind t) = Bind (εᵀ t)
εᶜ (unlabel {τ = τ} p) = unlabel p
εᶜ (write {H = H}  l⊑h τ∈π) with H ⊑? A
... | yes p = write l⊑h τ∈π
... | no ¬p = write∙ l⊑h τ∈π
εᶜ (write∙ l⊑h τ∈π) = write∙ l⊑h τ∈π
εᶜ (read l⊑h) = read l⊑h
εᶜ unId = unId

-- Fully homomorphic erasure on stack
εˢ : ∀ {τ₁ τ₂ l} -> Stack l τ₁ τ₂ -> Stack l τ₁ τ₂
εˢ [] = []
εˢ (c ∷ S) = (εᶜ c) ∷ εˢ S
εˢ ∙ = ∙

--------------------------------------------------------------------------------

ε : ∀ {l τ} -> Dec (l ⊑ A) -> State l τ -> State l τ
ε (no x) s = ∙
ε (yes y) ⟨ Δ , t , S ⟩ = ⟨ εᴱ Δ , εᵀ t , εˢ S ⟩
ε (yes y) ∙ = ∙

--------------------------------------------------------------------------------

ε-wken : ∀ {τ π₁ π₂} -> (t : Term π₁ τ) (p : π₁ ⊆ π₂) -> εᵀ (wken t p) ≡ wken (εᵀ t) p
ε-wken （） p = refl
ε-wken True p = refl
ε-wken False p = refl
ε-wken (Id t) p rewrite ε-wken t p = refl
ε-wken (unId t) p rewrite ε-wken t p = refl
ε-wken (Var τ∈π) p = refl
ε-wken (Abs t) p with ε-wken t (cons p)
... | x rewrite x = refl
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
ε-wken (read x t) p rewrite ε-wken t p = refl
ε-wken (write {h = H} x t t₁) p with H ⊑? A
... | yes _ rewrite ε-wken t p | ε-wken t₁ p = refl
... | no _ rewrite ε-wken t p | ε-wken t₁ p = refl
ε-wken (write∙ x t t₁) p rewrite ε-wken t p | ε-wken t₁ p = refl
ε-wken (new {h = H} x t) p with H ⊑? A
... | yes _  rewrite ε-wken t p = refl
... | no _ rewrite ε-wken t p = refl
ε-wken (new∙ x t) p rewrite ε-wken t p = refl
ε-wken #[ n ] p = refl
ε-wken #[ n ]ᴰ p = refl
ε-wken (fork {h = h} l⊑h t) p with h ⊑? A
... | yes _ rewrite ε-wken t p = refl
... | no _ rewrite ε-wken t p = refl
ε-wken (fork∙ l⊑h t) p rewrite ε-wken t p = refl
ε-wken (deepDup t) p rewrite ε-wken t p = refl
ε-wken ∙ p = refl

{-# REWRITE ε-wken #-}

ε-subst : ∀ {τ τ' π} (t₁ : Term π τ') (t₂ : Term (τ' ∷ π) τ) -> εᵀ (subst t₁ t₂) ≡ subst (εᵀ t₁) (εᵀ t₂)
ε-subst = ε-tm-subst [] _
  where ε-var-subst  :  ∀ {l} {α β} (π₁ : Context) (π₂ : Context) (t₁ : Term π₂ α) (β∈π : β ∈⟨ l ⟩ (π₁ ++ [ α ] ++ π₂))
                      ->  εᵀ (var-subst π₁ π₂ t₁ β∈π) ≡ var-subst π₁ π₂ (εᵀ t₁) β∈π
        ε-var-subst [] π₂ t₁ ⟪ here ⟫ = refl
        ε-var-subst [] π₁ t₁ (⟪ there β∈π ⟫) = refl
        ε-var-subst (β ∷ π₁) π₂ t₁ ⟪ here ⟫ = refl
        ε-var-subst {l} (τ ∷ π₁) π₂ t₁ (⟪ there β∈π ⟫)
          rewrite ε-wken (var-subst π₁ π₂ t₁ ⟪ β∈π ⟫) (drop {_} {τ} refl-⊆) | ε-var-subst {l} π₁ π₂ t₁ ⟪ β∈π ⟫ = refl

        ε-tm-subst : ∀ {τ τ'} (π₁ : Context) (π₂ : Context) (t₁ : Term π₂ τ') (t₂ : Term (π₁ ++ [ τ' ] ++ π₂) τ)
                   ->  εᵀ (tm-subst π₁ π₂ t₁ t₂) ≡ tm-subst π₁ π₂ (εᵀ t₁) (εᵀ t₂)
        ε-tm-subst π₁ π₂ t₁ （） = refl
        ε-tm-subst π₁ π₂ t₁ True = refl
        ε-tm-subst π₁ π₂ t₁ False = refl
        ε-tm-subst π₁ π₂ t₁ (Id t₂) rewrite ε-tm-subst π₁ π₂ t₁ t₂ = refl
        ε-tm-subst π₁ π₂ t₁ (unId t₂) rewrite ε-tm-subst π₁ π₂ t₁ t₂ = refl
        ε-tm-subst π₁ π₂ t₁ (Var {l} ⟪ τ∈π ⟫) rewrite ε-var-subst {l} π₁ π₂ t₁ (⟪ ∈ᴿ-∈  τ∈π ⟫) = refl
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
        ε-tm-subst π₁ π₂ t₁ (read x t₂) rewrite ε-tm-subst π₁ π₂ t₁ t₂ = refl
        ε-tm-subst π₁ π₂ t₁ (write {h = H} x t₂ t₃) with H ⊑? A
        ... | yes _ rewrite ε-tm-subst π₁ π₂ t₁ t₂ | ε-tm-subst π₁ π₂ t₁ t₃ = refl
        ... | no _ rewrite ε-tm-subst π₁ π₂ t₁ t₂ | ε-tm-subst π₁ π₂ t₁ t₃ = refl
        ε-tm-subst π₁ π₂ t₁ (write∙ x t₂ t₃)
          rewrite ε-tm-subst π₁ π₂ t₁ t₂ | ε-tm-subst π₁ π₂ t₁ t₃ = refl
        ε-tm-subst π₁ π₂ t₁ (new {h = H} x t₂) with H ⊑? A
        ... | yes _ rewrite ε-tm-subst π₁ π₂ t₁ t₂ = refl
        ... | no _ rewrite ε-tm-subst π₁ π₂ t₁ t₂ = refl
        ε-tm-subst π₁ π₂ t₁ (new∙ x t₂) rewrite ε-tm-subst π₁ π₂ t₁ t₂ = refl
        ε-tm-subst π₁ π₂ t₁ #[ n ] = refl
        ε-tm-subst π₁ π₂ t₁ #[ n ]ᴰ = refl
        ε-tm-subst π₁ π₂ t₁ (fork {h = h} l⊑h t₂) with h ⊑? A
        ... | yes _ rewrite ε-tm-subst π₁ π₂ t₁ t₂ = refl
        ... | no _ rewrite ε-tm-subst π₁ π₂ t₁ t₂ = refl
        ε-tm-subst π₁ π₂ t₁ (fork∙ l⊑h t₂) rewrite ε-tm-subst π₁ π₂ t₁ t₂ = refl
        ε-tm-subst π₁ π₂ t₁ (deepDup t₂) rewrite ε-tm-subst π₁ π₂ t₁ t₂ = refl
        ε-tm-subst π₁ π₂ t₁ ∙ = refl


{-# REWRITE ε-subst #-}

ε-deepDupᵀ-≡ : ∀ {π τ} -> (t : Term π τ) ->  εᵀ (deepDupᵀ t) ≡ deepDupᵀ (εᵀ t)
ε-deepDupᵀ-≡ = εᵀ-dup-ufv-≡ []
  where εᵀ-dup-ufv-≡ : ∀ {π τ} -> (vs : Vars π) (t : Term π τ) ->  εᵀ (dup-ufv vs t) ≡ dup-ufv vs (εᵀ t)
        εᵀ-dup-ufv-≡ vs （） = refl
        εᵀ-dup-ufv-≡ vs True = refl
        εᵀ-dup-ufv-≡ vs False = refl
        εᵀ-dup-ufv-≡ vs (Id t)
          rewrite εᵀ-dup-ufv-≡ vs t = refl
        εᵀ-dup-ufv-≡ vs (unId t)
          rewrite εᵀ-dup-ufv-≡ vs t = refl
        εᵀ-dup-ufv-≡ vs (Var ⟪ τ∈π ⟫) with memberⱽ (∈ᴿ-∈ τ∈π) vs
        εᵀ-dup-ufv-≡ vs (Var ⟪ τ∈π ⟫) | yes p = refl
        εᵀ-dup-ufv-≡ vs (Var ⟪ τ∈π ⟫) | no ¬p = refl
        εᵀ-dup-ufv-≡ vs (Abs t)
          rewrite εᵀ-dup-ufv-≡ (here ∷ (mapⱽ there vs)) t = refl
        εᵀ-dup-ufv-≡ vs (App t t₁)
          rewrite εᵀ-dup-ufv-≡ vs t | εᵀ-dup-ufv-≡ vs t₁ = refl
        εᵀ-dup-ufv-≡ vs (If t Then t₁ Else t₂)
          rewrite εᵀ-dup-ufv-≡ vs t | εᵀ-dup-ufv-≡ vs t₁ | εᵀ-dup-ufv-≡ vs t₂ = refl
        εᵀ-dup-ufv-≡ vs (Return l t) rewrite εᵀ-dup-ufv-≡ vs t = refl
        εᵀ-dup-ufv-≡ vs (t >>= t₁)
          rewrite εᵀ-dup-ufv-≡ vs t | εᵀ-dup-ufv-≡ vs t₁ = refl
        εᵀ-dup-ufv-≡ vs (Mac l t) rewrite εᵀ-dup-ufv-≡ vs t = refl
        εᵀ-dup-ufv-≡ vs (Res l t) with l ⊑? A
        εᵀ-dup-ufv-≡ vs (Res l t) | yes p rewrite εᵀ-dup-ufv-≡ vs t = refl
        εᵀ-dup-ufv-≡ vs (Res l t) | no ¬p = refl
        εᵀ-dup-ufv-≡ vs (label {h = H} l⊑h t) with H ⊑? A
        εᵀ-dup-ufv-≡ vs (label l⊑h t) | yes p rewrite εᵀ-dup-ufv-≡ vs t = refl
        εᵀ-dup-ufv-≡ vs (label l⊑h t) | no ¬p rewrite εᵀ-dup-ufv-≡ vs t = refl
        εᵀ-dup-ufv-≡ vs (label∙ l⊑h t) rewrite εᵀ-dup-ufv-≡ vs t = refl
        εᵀ-dup-ufv-≡ vs (unlabel l⊑h t) rewrite εᵀ-dup-ufv-≡ vs t = refl
        εᵀ-dup-ufv-≡ vs (read x t) rewrite εᵀ-dup-ufv-≡ vs t = refl
        εᵀ-dup-ufv-≡ vs (write {h = H} x t t₁) with H ⊑? A
        ... | yes _ rewrite εᵀ-dup-ufv-≡ vs t |  εᵀ-dup-ufv-≡ vs t₁ = refl
        ... | no _ rewrite εᵀ-dup-ufv-≡ vs t |  εᵀ-dup-ufv-≡ vs t₁ = refl
        εᵀ-dup-ufv-≡ vs (write∙ x t t₁) rewrite εᵀ-dup-ufv-≡ vs t |  εᵀ-dup-ufv-≡ vs t₁ = refl
        εᵀ-dup-ufv-≡ vs (new {h = H} x t) with H ⊑? A
        ... | yes _ rewrite εᵀ-dup-ufv-≡ vs t = refl
        ... | no _ rewrite εᵀ-dup-ufv-≡ vs t = refl
        εᵀ-dup-ufv-≡ vs (new∙ x t) rewrite εᵀ-dup-ufv-≡ vs t = refl
        εᵀ-dup-ufv-≡ vs #[ n ] = refl
        εᵀ-dup-ufv-≡ vs #[ n ]ᴰ = refl
        εᵀ-dup-ufv-≡ vs (fork {h = h} l⊑h t) with h ⊑? A
        ... | yes _ rewrite εᵀ-dup-ufv-≡ vs t = refl
        ... | no _ rewrite εᵀ-dup-ufv-≡ vs t = refl
        εᵀ-dup-ufv-≡ vs (fork∙ l⊑h t) rewrite εᵀ-dup-ufv-≡ vs t = refl
        εᵀ-dup-ufv-≡ vs (deepDup t) rewrite εᵀ-dup-ufv-≡ vs t = refl
        εᵀ-dup-ufv-≡ vs ∙ = refl

{-# REWRITE ε-deepDupᵀ-≡ #-}

--------------------------------------------------------------------------------
-- Env lemmas

memberᴱ : ∀ {l π π' τ} {Δ : Env l π} {t : Term π' τ} (τ∈π : τ ∈⟨ l ⟩ᴿ π) ->
           τ∈π ↦ t ∈ᴱ Δ -> τ∈π ↦ (εᵀ t) ∈ᴱ (εᴱ Δ)
memberᴱ {l} ⟪ τ∈π ⟫ = aux ⟪ (∈ᴿ-∈ τ∈π) ⟫
  where aux : ∀ {π π' τ} {Δ : Env l π} {t : Term π' τ} (τ∈π : τ ∈⟨ l ⟩ π)
            -> Memberᴱ (just t) τ∈π Δ -> Memberᴱ (just (εᵀ t)) τ∈π (εᴱ Δ)
        aux (⟪ here ⟫) here = here
        aux (⟪ there τ∈π' ⟫) (there x) = there (aux ⟪ τ∈π' ⟫ x)

updateᴱ : ∀ {l π π' τ} {Δ Δ' : Env l π} {mt : Maybe (Term π' τ)} {τ∈π : τ ∈⟨ l ⟩ π} -> Updateᴱ mt τ∈π Δ Δ' -> Updateᴱ (M.map εᵀ mt) τ∈π (εᴱ Δ) (εᴱ Δ')
updateᴱ here = here
updateᴱ (there x) = there (updateᴱ x)

--------------------------------------------------------------------------------

-- Simulation Property
ε-sim : ∀ {l τ} {s₁ s₂ : State l τ} (x : Dec (l ⊑ A)) -> s₁ ⇝ s₂ -> ε x s₁ ⇝ ε x s₂
-- High-Computations
ε-sim (no x) s = Hole₁
-- Low-Computations
ε-sim (yes y) App₁ = App₁
ε-sim (yes y) (App₂ α∈π) = App₂ α∈π
ε-sim (yes y) (Var₁ τ∈π t∈Δ ¬val rᴱ) = Var₁ τ∈π (memberᴱ τ∈π t∈Δ) (εᵀ¬Val ¬val) (updateᴱ rᴱ)
ε-sim (yes y) (Var₁' τ∈π v∈Δ val) = Var₁' τ∈π (memberᴱ τ∈π v∈Δ) (εᵀ-Val val)
ε-sim (yes y) (Var₂ τ∈π val uᴱ) = Var₂ τ∈π (εᵀ-Val val) (updateᴱ uᴱ)
ε-sim (yes y) If = If
ε-sim (yes y) IfTrue = IfTrue
ε-sim (yes y) IfFalse = IfFalse
ε-sim (yes y) Return = Return
ε-sim (yes y) Bind₁ = Bind₁
ε-sim (yes y) Bind₂ = Bind₂
ε-sim (yes y) (Label' {h = H} p) with H ⊑? A
ε-sim (yes y) (Label' p₁) | yes p = Label' p₁
ε-sim (yes y) (Label' p) | no ¬p = Label'∙ p
ε-sim (yes y) (Label'∙ {h = H} p) with H ⊑? A
ε-sim (yes y) (Label'∙ p₁) | yes p = Label'∙ p₁
ε-sim (yes y) (Label'∙ p) | no ¬p = Label'∙ p
ε-sim (yes y) (Unlabel₁ p) = Unlabel₁ p
ε-sim (yes y) (Unlabel₂ {l' = L} p) with L ⊑? A
ε-sim (yes y) (Unlabel₂ p₁) | yes p = Unlabel₂ p₁
ε-sim (yes y) (Unlabel₂ p) | no ¬p = ⊥-elim (¬p (trans-⊑ p y))
ε-sim (yes y) UnId₁ = UnId₁
ε-sim (yes y) UnId₂ = UnId₂
ε-sim (yes y) (Fork {h = h} p) with h ⊑? A
... | yes _ = Fork p
... | no _ = Fork∙ p
ε-sim (yes y) (Fork∙ p) = Fork∙ p
ε-sim (yes y) (DeepDup τ∈π t∈Δ) = DeepDup τ∈π (memberᴱ τ∈π t∈Δ)
ε-sim (yes y) (DeepDup' ¬var) = DeepDup' (εᵀ¬Var ¬var)
ε-sim (yes y) (New₁ {H = H} ¬var) with H ⊑? A
ε-sim (yes y) (New₁ ¬var) | yes p = New₁ (εᵀ¬Var ¬var)
ε-sim (yes y) (New₁ ¬var) | no ¬p = New∙₁ (εᵀ¬Var ¬var)
ε-sim (yes y) (New∙₁ ¬var) = New∙₁ (εᵀ¬Var ¬var)
ε-sim (yes y) Read₁ = Read₁
ε-sim (yes y) (Write₁ {H = H}) with H ⊑? A
ε-sim (yes y) Write₁ | yes p = Write₁
ε-sim (yes y) Write₁ | no ¬p = Write∙₁
ε-sim (yes y) Write∙₁ = Write∙₁
ε-sim (yes y) Hole₁ = Hole₁
ε-sim (yes y) Hole₂ = Hole₂

--------------------------------------------------------------------------------

εᴹ : ∀ {l} -> Dec (l ⊑ A) -> Heap l -> Heap l
εᴹ (yes p) ⟨ M , Δ ⟩ = ⟨ M , εᴱ Δ ⟩  -- Memory contains only pointers to Δ, so nothing to erase there
εᴹ (yes p) ∙ = ∙
εᴹ (no ¬p) _ = ∙  -- ∙ , ∙

εᴴ : ∀ {ls} -> Heaps ls -> Heaps ls
εᴴ [] = []
εᴴ (x ∷ Γ) = εᴹ (_ ⊑? A) x ∷ εᴴ Γ

-- Erasure for Programs
ε₁ᴾ : ∀ {l ls τ} -> (x : Dec (l ⊑ A)) -> Program l ls τ -> Program l ls τ
ε₁ᴾ (yes p) ⟨ Γ , t , S ⟩ = ⟨ (εᴴ Γ) , (εᵀ t) , (εˢ S) ⟩
ε₁ᴾ (yes p) ∙ = ∙
ε₁ᴾ {l} {ls} {τ} (no ¬p) _ = ∙

writeᴹ∙-≡ : ∀ {H ls} {Γ₁ Γ₂ : Heaps ls} {X Y : Heap H} -> H ⋤ A -> H ↦ X ∈ᴴ Γ₁ -> Γ₂ ≔ Γ₁ [ H ↦ Y ]ᴴ -> (εᴴ Γ₁) ≡ (εᴴ Γ₂)
writeᴹ∙-≡ {H} H⋢A here here with H ⊑? A
writeᴹ∙-≡ H⋢A here here | yes p = ⊥-elim (H⋢A p)
writeᴹ∙-≡ H⋢A here here | no ¬p = refl
writeᴹ∙-≡ H⋢A here (there {u = u} y) = ⊥-elim (∈-not-unique (update-∈ y) u)
writeᴹ∙-≡ H⋢A (there {u = u} x) here = ⊥-elim (∈-not-unique (member-∈ x) u)
writeᴹ∙-≡ H⋢A (there x) (there y) rewrite writeᴹ∙-≡ H⋢A x y = refl

memberᴴ : ∀ {l π ls} {Γ : Heaps ls} {M : Memory l} {Δ : Env l π} -> l ⊑ A -> l ↦ ⟨ M , Δ ⟩ ∈ᴴ Γ -> l ↦ ⟨ M , εᴱ Δ ⟩ ∈ᴴ (εᴴ Γ)
memberᴴ {l} l⊑A here with l ⊑? A
... | yes _ = here
... | no ¬p = ⊥-elim (¬p l⊑A)
memberᴴ l⊑A (there x) = there (memberᴴ l⊑A x)

updateᴴ : ∀ {l π ls} {Γ Γ' : Heaps ls} {M : Memory l} {Δ : Env l π} -> l ⊑ A -> Γ' ≔ Γ [ l ↦ ⟨ M , Δ ⟩ ]ᴴ -> (εᴴ Γ') ≔ (εᴴ Γ) [ l ↦ ⟨ M , εᴱ Δ ⟩ ]ᴴ
updateᴴ {l} l⊑A here with l ⊑? A
... | yes _ = here
... | no ¬p = ⊥-elim (¬p l⊑A)
updateᴴ l⊑A (there x) = there (updateᴴ l⊑A x)

open import Data.Product using (proj₁ ; proj₂)

ε₁ᴾ-sim : ∀ {l ls τ} {p₁ p₂ : Program l ls τ} (x : Dec (l ⊑ A)) -> p₁ ⟼ p₂ -> ε₁ᴾ x p₁ ⟼ ε₁ᴾ x p₂
ε₁ᴾ-sim (yes p) (Pure l∈Γ step uᴴ) = Pure (memberᴴ p l∈Γ) (ε-sim (yes p) step) (updateᴴ p uᴴ)
ε₁ᴾ-sim (yes p) (New {H = H} H∈Γ uᴴ) with H ⊑? A
ε₁ᴾ-sim (yes p₁) (New H∈Γ uᴴ) | yes p = New (memberᴴ p H∈Γ) (updateᴴ p uᴴ)
ε₁ᴾ-sim (yes p) (New {Δ = Δ} {M = M} {τ∈π = ⟪ τ∈π ⟫} {l⊑h = l⊑h}  H∈Γ uᴴ) | no ¬p
  rewrite writeᴹ∙-≡ ¬p H∈Γ uᴴ = New∙
ε₁ᴾ-sim (yes p) (New∙ {H = H}) with H ⊑? A
ε₁ᴾ-sim (yes p₁) New∙ | yes p = New∙
ε₁ᴾ-sim (yes p) New∙ | no ¬p = New∙
ε₁ᴾ-sim (yes p) (Write₂ {H = H} H∈Γ uᴹ uᴴ) with H ⊑? A
ε₁ᴾ-sim (yes p₁) (Write₂ H∈Γ uᴹ uᴴ) | yes p = Write₂ (memberᴴ p H∈Γ) uᴹ (updateᴴ p uᴴ)
ε₁ᴾ-sim (yes p) (Write₂ {l⊑H = l⊑H} H∈Γ uᴹ uᴴ) | no ¬p
  rewrite writeᴹ∙-≡ ¬p H∈Γ uᴴ = Write∙₂
ε₁ᴾ-sim (yes p) (Writeᴰ₂ {H = H} H∈Γ uᴹ uᴴ) with H ⊑? A
ε₁ᴾ-sim (yes p₁) (Writeᴰ₂ H∈Γ uᴹ uᴴ) | yes p = Writeᴰ₂ (memberᴴ p H∈Γ) uᴹ (updateᴴ p uᴴ)
ε₁ᴾ-sim (yes p) (Writeᴰ₂ {l⊑H = l⊑H} H∈Γ uᴹ uᴴ) | no ¬p
  rewrite writeᴹ∙-≡ ¬p H∈Γ uᴴ = Write∙₂
ε₁ᴾ-sim (yes p) (Write∙₂ {H = H}) with H ⊑? A
ε₁ᴾ-sim (yes p₁) Write∙₂ | yes p = Write∙₂
ε₁ᴾ-sim (yes p) Write∙₂ | no ¬p = Write∙₂
ε₁ᴾ-sim {l} (yes p) (Read₂ l∈Γ n∈M) with l ⊑? A
ε₁ᴾ-sim (yes p₁) (Read₂ l∈Γ n∈M) | yes p = Read₂ (memberᴴ p₁ l∈Γ) n∈M
ε₁ᴾ-sim (yes p) (Read₂ l∈Γ n∈M) | no ¬p = ⊥-elim (¬p p)
ε₁ᴾ-sim {l} (yes p') (Readᴰ₂ {L = L} {L⊑l = L⊑l} L∈Γ n∈M) with L ⊑? A
... | yes p = Readᴰ₂ (memberᴴ p L∈Γ) n∈M
... | no ¬p = ⊥-elim (¬p (trans-⊑ L⊑l p'))
ε₁ᴾ-sim (yes p) (DeepDupˢ {τ∈π = τ∈π} L⊏l L∈Γ t∈Δ) = DeepDupˢ L⊏l (memberᴴ (trans-⊑ (proj₁ L⊏l) p) L∈Γ) (memberᴱ τ∈π t∈Δ)
ε₁ᴾ-sim (yes p) Hole = Hole
ε₁ᴾ-sim (no ¬p) x = Hole

εᴾ : ∀ {l ls τ} -> Program l ls τ -> Program l ls τ
εᴾ {l} = ε₁ᴾ (l ⊑? A)

εᴾ-sim : ∀ {l ls τ} {p₁ p₂ : Program l ls τ} -> p₁ ⟼ p₂ -> εᴾ p₁ ⟼ εᴾ p₂
εᴾ-sim {l} = ε₁ᴾ-sim (l ⊑? A)
