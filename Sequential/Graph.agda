-- This module defines the graph of the erasure function on terms

-- TODO move all erasure related modules in a new Security module

import Lattice as L

module Sequential.Graph (𝓛 : L.Lattice) (A : L.Label 𝓛) where

import Types as T
open T 𝓛

import Sequential.Calculus as S hiding (wkenᴱ)
open S 𝓛
open import Sequential.Erasure 𝓛 A as SE hiding (memberᴴ ; updateᴴ ; memberᴱ)

open import Relation.Nullary

data Erase {π} : ∀ {τ} -> Term π τ -> Term π τ -> Set where
  （） : Erase （） （）
  True : Erase True True
  False : Erase False False
  Id : ∀ {τ} {t t' : Term π τ} -> Erase t t' -> Erase (Id t) (Id t')
  unId : ∀ {τ} {t t' : Term π (Id τ)} -> Erase t t' -> Erase (unId t) (unId t')
  Var : ∀ {l} {τ} ->  (τ∈π : τ ∈⟨ l ⟩ᴿ π) -> Erase (Var τ∈π) (Var τ∈π)
  Abs : ∀ {α β} {t t' : Term (α ∷ π) β} -> Erase t t' -> Erase (Abs t) (Abs t')
  App : ∀ {α β} {t₁ t₁' : Term π (α => β)} {t₂ t₂' : Term π α} ->
          Erase t₁ t₁' -> Erase t₂ t₂' -> Erase (App t₁ t₂) (App t₁' t₂')

  If_Then_Else_ : ∀ {α} {t₁ t₁'} {t₂ t₂' t₃ t₃' : Term _ α} ->
                  Erase t₁ t₁' -> Erase t₂ t₂' -> Erase t₃ t₃' ->
                  Erase (If t₁ Then t₂ Else t₃) (If t₁' Then t₂' Else t₃')

  Return : ∀ {α l} {t t' : Term _ α} -> Erase t t' -> Erase (Return l t) (Return l t')
  _>>=_ : ∀ {l} {α β} {t₁ t₁' : Term π (Mac l α)} {t₂ t₂' :  Term π (α => Mac l β)} ->
            Erase t₁ t₁' -> Erase t₂ t₂' -> Erase (t₁ >>= t₂) (t₁' >>= t₂')

  Mac : ∀ {α l} {t t' : Term π α} -> Erase t t' -> Erase (Mac l t) (Mac l t')

  Res : ∀ {α l} {t t' : Term π α} -> l ⊑ A -> Erase t t' -> Erase (Res l t) (Res l t')
  Res∙ : ∀ {α l} {t : Term π α} -> l ⋤ A ->  Erase (Res l t) (Res l ∙)

  label : ∀ {l h α} {l⊑h : l ⊑ h} {t t' : Term _ α} -> (h⊑A : h ⊑ A) -> Erase t t' -> Erase (label l⊑h t) (label l⊑h t')
  label' : ∀ {l h α} {l⊑h : l ⊑ h} {t t' : Term _ α} -> (h⋤A : h ⋤ A) -> Erase t t' -> Erase (label l⊑h t) (label∙ l⊑h t')
  label∙ : ∀ {l h α} {l⊑h : l ⊑ h} {t t' : Term _ α} -> Erase t t' -> Erase (label∙ l⊑h t) (label∙ l⊑h t')

  unlabel : ∀ {l h τ} {t t' : Term _ (Labeled l τ)} -> (l⊑h : l ⊑ h) -> Erase t t' -> Erase (unlabel l⊑h t) (unlabel l⊑h t')

  read : ∀ {l h τ} {t t' : Term _ (Ref l τ)} -> (l⊑h : l ⊑ h) -> Erase t t' -> Erase (read {τ = τ} l⊑h t) (read l⊑h t')

  write : ∀ {l h τ} -> {t₁ t₁' : Term _ (Ref h τ)} {t₂ t₂' : Term _ τ} -> (l⊑h : l ⊑ h) (h⊑A : h ⊑ A) ->
               Erase t₁ t₁' -> Erase t₂ t₂' -> Erase (write l⊑h t₁ t₂) (write l⊑h t₁' t₂')

  write' : ∀ {l h τ} -> {t₁ t₁' : Term _ (Ref h τ)} {t₂ t₂' : Term _ τ} -> (l⊑h : l ⊑ h) (h⋤A : h ⋤ A) ->
               Erase t₁ t₁' -> Erase t₂ t₂' -> Erase (write l⊑h t₁ t₂) (write∙ l⊑h t₁' t₂')


  write∙ : ∀ {l h τ} {t₁ t₁' : Term _ (Ref h τ)} {t₂ t₂' : Term _ τ} -> (l⊑h : l ⊑ h) ->
             Erase t₁ t₁' -> Erase t₂ t₂' -> Erase (write∙ l⊑h t₁ t₂) (write∙ l⊑h t₁' t₂')

  new : ∀ {l h τ} {t t' : Term _ τ} (l⊑h : l ⊑ h) (h⊑A : h ⊑ A) -> Erase t t' -> Erase (new l⊑h t) (new l⊑h t')
  new' : ∀ {l h τ} {t t' : Term _ τ} (l⊑h : l ⊑ h) (h⋤A : h ⋤ A) -> Erase t t' -> Erase (new l⊑h t) (new∙ l⊑h t')
  new∙ : ∀ {l h τ} {t t' : Term _ τ} (l⊑h : l ⊑ h) -> Erase t t' -> Erase (new∙ l⊑h t) (new∙ l⊑h t')

  #[_] :  ∀ n -> Erase #[ n ] #[ n ]
  #[_]ᴰ :  ∀ n -> Erase #[ n ]ᴰ #[ n ]ᴰ

  fork : ∀ {l h} {t t' : Term _ _} -> (l⊑h : l ⊑ h) (h⊑A : h ⊑ A) -> Erase t t' -> Erase (fork l⊑h t) (fork l⊑h t')
  fork' : ∀ {l h} {t t' : Term _ _} -> (l⊑h : l ⊑ h) (h⋤A : h ⋤ A) -> Erase t t' -> Erase (fork l⊑h t) (fork∙ l⊑h t')
  fork∙ : ∀ {l h} {t t' : Term _ _} -> (l⊑h : l ⊑ h) -> Erase t t' -> Erase (fork∙ l⊑h t) (fork∙ l⊑h t')

  deepDup : ∀ {τ} {t t' : Term π τ} -> Erase t t' -> Erase (deepDup t) (deepDup t')

  ∙ : ∀ {τ} -> Erase {τ = τ} ∙ ∙


lift-ε : ∀ {τ π} -> (t : Term π τ) -> Erase t (εᵀ t)
lift-ε S.（） = （）
lift-ε S.True = True
lift-ε S.False = False
lift-ε (S.Id t) = Id (lift-ε t)
lift-ε (S.unId t) = unId (lift-ε t)
lift-ε (S.Var τ∈π) = Var τ∈π
lift-ε (S.Abs t) = Abs (lift-ε t)
lift-ε (S.App t t₁) = App (lift-ε t) (lift-ε t₁)
lift-ε (S.If t Then t₁ Else t₂) = If (lift-ε t) Then (lift-ε t₁) Else (lift-ε t₂)
lift-ε (S.Return l t) = Return (lift-ε t)
lift-ε (t S.>>= t₁) = (lift-ε t) >>= (lift-ε t₁)
lift-ε (S.Mac l t) = Mac (lift-ε t)
lift-ε (S.Res l t) with l ⊑? A
lift-ε (S.Res l t) | yes p = Res p (lift-ε t)
lift-ε (S.Res l t) | no ¬p = Res∙ ¬p
lift-ε (S.label {h = h} l⊑h t) with h ⊑? A
lift-ε (S.label l⊑h t) | yes p = label p (lift-ε t)
lift-ε (S.label l⊑h t) | no ¬p = label' ¬p (lift-ε t)
lift-ε (S.label∙ l⊑h t) = label∙ (lift-ε t)
lift-ε (S.unlabel l⊑h t) = unlabel l⊑h (lift-ε t)
lift-ε (S.read x t) = read x (lift-ε t)
lift-ε (S.write {h = h} x t t₁) with h ⊑? A
lift-ε (S.write x t t₁) | yes p = write x p (lift-ε t) (lift-ε t₁)
lift-ε (S.write x t t₁) | no ¬p = write' x ¬p (lift-ε t) (lift-ε t₁)
lift-ε (S.write∙ x t t₁) = write∙ x (lift-ε t) (lift-ε t₁)
lift-ε (S.new {h = h} x t) with h ⊑? A
lift-ε (S.new x t) | yes p = new x p (lift-ε t)
lift-ε (S.new x t) | no ¬p = new' x ¬p (lift-ε t)
lift-ε (S.new∙ x t) = new∙ x (lift-ε t)
lift-ε S.#[ x ] = #[ x ]
lift-ε S.#[ x ]ᴰ = #[ x ]ᴰ
lift-ε (S.fork {h = h} l⊑h t) with h ⊑? A
lift-ε (S.fork l⊑h t) | yes p = fork l⊑h p (lift-ε t)
lift-ε (S.fork l⊑h t) | no ¬p = fork' l⊑h ¬p (lift-ε t)
lift-ε (S.fork∙ l⊑h t) = fork∙ l⊑h (lift-ε t)
lift-ε (S.deepDup t) = deepDup (lift-ε t)
lift-ε S.∙ = ∙

open import Relation.Binary.PropositionalEquality hiding (subst)
open import Data.Empty

unlift-ε : ∀ {π τ} {t t' : Term π τ} -> Erase t t' -> εᵀ t ≡ t'
unlift-ε （） = refl
unlift-ε True = refl
unlift-ε False = refl
unlift-ε (Id x) rewrite unlift-ε x = refl
unlift-ε (unId x) rewrite unlift-ε x = refl
unlift-ε (Var τ∈π) = refl
unlift-ε (Abs x) rewrite unlift-ε x = refl
unlift-ε (App x x₁)
  rewrite unlift-ε x | unlift-ε x₁ = refl
unlift-ε (If x Then x₁ Else x₂)
    rewrite unlift-ε x | unlift-ε x₁ | unlift-ε x₂ = refl
unlift-ε (Return x) rewrite unlift-ε x = refl
unlift-ε (x >>= x₁)
  rewrite unlift-ε x | unlift-ε x₁ = refl
unlift-ε (Mac x) rewrite unlift-ε x = refl
unlift-ε (Res {l = l} p x) with l ⊑? A
unlift-ε (Res p x) | yes p' rewrite unlift-ε x = refl
unlift-ε (Res p x) | no ¬p = ⊥-elim (¬p p)
unlift-ε (Res∙ {l = l} x) with l ⊑? A
unlift-ε (Res∙ x) | yes p = ⊥-elim (x p)
unlift-ε (Res∙ x) | no ¬p = refl
unlift-ε (label {h = h} p x) with h ⊑? A
unlift-ε (label p₁ x) | yes p rewrite unlift-ε x = refl
unlift-ε (label p x) | no ¬p = ⊥-elim (¬p p)
unlift-ε (label' {h = h} h⋤A x₁) with h ⊑? A
unlift-ε (label' h⋤A x₁) | yes p = ⊥-elim (h⋤A p)
unlift-ε (label' h⋤A x₁) | no ¬p rewrite unlift-ε x₁ = refl
unlift-ε (label∙ x) rewrite unlift-ε x = refl
unlift-ε (unlabel l⊑h x) rewrite unlift-ε x = refl
unlift-ε (read l⊑h x) rewrite unlift-ε x = refl
unlift-ε (write {h = h} l⊑h p x x₁) with h ⊑? A
unlift-ε (write l⊑h p₁ x x₁) | yes p
  rewrite unlift-ε x | unlift-ε x₁ = refl
unlift-ε (write l⊑h p x x₁) | no ¬p = ⊥-elim (¬p p)
unlift-ε (write' {h = h} l⊑h x x₁ x₂) with h ⊑? A
unlift-ε (write' l⊑h x x₁ x₂) | yes p = ⊥-elim (x p)
unlift-ε (write' l⊑h x x₁ x₂) | no ¬p
  rewrite unlift-ε x₁ | unlift-ε x₂ = refl
unlift-ε (write∙ {h = h} l⊑h x x₁) with h ⊑? A
unlift-ε (write∙ l⊑h x x₁) | yes p
  rewrite unlift-ε x | unlift-ε x₁ = refl
unlift-ε (write∙ l⊑h x x₁) | no ¬p
  rewrite unlift-ε x | unlift-ε x₁ = refl
unlift-ε (new {h = h} l⊑h p x) with h ⊑? A
unlift-ε (new l⊑h p₁ x) | yes p rewrite unlift-ε x = refl
unlift-ε (new l⊑h p x) | no ¬p = ⊥-elim (¬p p)
unlift-ε (new' {h = h} l⊑h h⋤A x) with h ⊑? A
unlift-ε (new' l⊑h h⋤A x) | yes p = ⊥-elim (h⋤A p)
unlift-ε (new' l⊑h h⋤A x) | no ¬p rewrite unlift-ε x = refl
unlift-ε (new∙ {h = h} l⊑h x) with h ⊑? A
unlift-ε (new∙ l⊑h x) | yes p rewrite unlift-ε x = refl
unlift-ε (new∙ l⊑h x) | no ¬p rewrite unlift-ε x = refl
unlift-ε #[ n ] = refl
unlift-ε #[ n ]ᴰ = refl
unlift-ε (fork {h = h} l⊑h p x) with h ⊑? A
unlift-ε (fork l⊑h p₁ x) | yes p rewrite unlift-ε x = refl
unlift-ε (fork l⊑h p x) | no ¬p = ⊥-elim (¬p p)
unlift-ε (fork' {h = h} l⊑h h⋤A x) with h ⊑? A
unlift-ε (fork' l⊑h h⋤A x) | yes p = ⊥-elim (h⋤A p)
unlift-ε (fork' l⊑h h⋤A x) | no ¬p rewrite unlift-ε x = refl
unlift-ε (fork∙ l⊑h x) rewrite unlift-ε x = refl
unlift-ε (deepDup x) rewrite unlift-ε x = refl
unlift-ε ∙ = refl

wkenᴱ : ∀ {π₁ π₂ τ} {t t' : Term π₁ τ} -> Erase t t' -> (p : π₁ ⊆ π₂) ->  Erase (wken t p) (wken t' p)
wkenᴱ {π₁} {π₂} {τ} {t} e p with lift-ε (wken t p)
... | x rewrite unlift-ε e = x

substᴱ :  ∀ {π α β} {x x' : Term π α} {t t' : Term (α ∷ π) β} -> Erase x x' -> Erase t t' -> Erase (subst x t) (subst x' t')
substᴱ {x = x} {t = t} e₁ e₂ with lift-ε (subst x t)
... | e rewrite unlift-ε e₁ | unlift-ε e₂ = e

deepDupᵀᴱ : ∀ {π τ} {t t' : Term π τ} -> Erase t t' -> Erase (deepDupᵀ t) (deepDupᵀ t')
deepDupᵀᴱ {t = t} e with lift-ε (deepDupᵀ t)
... | e' rewrite unlift-ε e = e'

¬valᴱ : ∀ {π τ} {t t' : Term π τ} -> Erase t t' -> ¬ (Value t') -> ¬ (Value t)
¬valᴱ （） ¬val S.（） = ¬val S.（）
¬valᴱ True ¬val S.True = ¬val S.True
¬valᴱ False ¬val S.False = ¬val S.False
¬valᴱ (Abs x) ¬val (S.Abs t) = ¬val (S.Abs _)
¬valᴱ (Id x) ¬val (S.Id t) = ¬val (S.Id _)
¬valᴱ (Mac x) ¬val (S.Mac t) = ¬val (S.Mac _)
¬valᴱ (Res x x₁) ¬val (S.Res t) = ¬val (S.Res _)
¬valᴱ (Res∙ x) ¬val (S.Res t) = ¬val (S.Res _)
¬valᴱ #[ n ] ¬val S.#[ .n ] = ¬val S.#[ n ]
¬valᴱ #[ n ]ᴰ ¬val S.#[ .n ]ᴰ = ¬val S.#[ n ]ᴰ

¬varᴱ : ∀ {π τ} {t t' : Term π τ} -> Erase t t' -> ¬ (IsVar t') -> ¬ (IsVar t)
¬varᴱ (Var τ∈π) ¬var (S.Var .τ∈π) = ¬var (S.Var τ∈π)

valᴱ : ∀ {π τ} {t t' : Term π τ} -> Erase t t' -> Value t' -> Value t
valᴱ （） S.（） = S.（）
valᴱ True S.True = S.True
valᴱ False S.False = S.False
valᴱ (Abs e) (S.Abs t₁) = S.Abs _
valᴱ (Id e) (S.Id t₁) = S.Id _
valᴱ (Mac e) (S.Mac t₁) = S.Mac _
valᴱ (Res x e) (S.Res t₁) = S.Res _
valᴱ (Res∙ x) (S.Res .S.∙) = S.Res _
valᴱ #[ n ] S.#[ .n ] = S.#[ n ]
valᴱ #[ n ]ᴰ S.#[ .n ]ᴰ = S.#[ n ]ᴰ

val₁ᴱ : ∀ {π τ} {t t' : Term π τ} -> Erase t t' -> Value t -> Value t'
val₁ᴱ e val with εᵀ-Val val
... | val' rewrite unlift-ε e = val'

--------------------------------------------------------------------------------

data Eraseᶜ {l} : ∀ {τ₁ τ₂} -> Cont l τ₁ τ₂ -> Cont l τ₁ τ₂ -> Set where
 Var : ∀ {τ₁ τ₂} {{π : Context}} -> (τ∈π : τ₁ ∈⟨ l ⟩ᴿ π) -> Eraseᶜ {τ₂ = τ₂} (Var τ∈π) (Var τ∈π)
 # :  ∀ {τ} {{π : Context}} -> (τ∈π : τ ∈⟨ l ⟩ᴿ π)  -> Eraseᶜ (# τ∈π) (# τ∈π)
 Then_Else_ : ∀ {τ} {π : Context} {t₁ t₁' t₂ t₂' : Term π τ} -> Erase t₁ t₁' -> Erase t₂ t₂' -> Eraseᶜ (Then t₁ Else t₂) (Then t₁' Else t₂')
 Bind :  ∀ {τ₁ τ₂} {π : Context} {t t' : Term π (τ₁ => Mac l τ₂)} -> Erase t t' -> Eraseᶜ (Bind t) (Bind t')
 unlabel : ∀ {l' τ} (p : l' ⊑ l) -> Eraseᶜ {τ₁ = Labeled l' τ} (unlabel p) (unlabel p)
 unId : ∀ {τ} -> Eraseᶜ {τ₂ = τ} unId unId
 write : ∀ {τ H} {{π : Context}} (l⊑H : l ⊑ H) (H⊑A : H ⊑ A) -> (τ∈π : τ ∈⟨ l ⟩ᴿ π) -> Eraseᶜ (write l⊑H τ∈π) (write l⊑H τ∈π)
 write' : ∀ {τ H} {{π : Context}} (l⊑H : l ⊑ H) (H⋤A : H ⋤ A) -> (τ∈π : τ ∈⟨ l ⟩ᴿ π) -> Eraseᶜ (write l⊑H τ∈π) (write∙ l⊑H τ∈π)
 write∙ : ∀ {τ H} {{π : Context}} (l⊑H : l ⊑ H) -> (τ∈π : τ ∈⟨ l ⟩ᴿ π) -> Eraseᶜ (write∙ l⊑H τ∈π) (write∙ l⊑H τ∈π)
 read : ∀ {τ L} (L⊑H : L ⊑ l) -> Eraseᶜ (read {τ = τ} L⊑H) (read L⊑H)

lift-εᶜ : ∀ {l τ₁ τ₂} -> (C : Cont l τ₁ τ₂) -> Eraseᶜ C (εᶜ C)
lift-εᶜ (S.Var τ∈π) = Var τ∈π
lift-εᶜ (S.# τ∈π) = # τ∈π
lift-εᶜ (S.Then x Else x₁) = Then (lift-ε x) Else (lift-ε x₁)
lift-εᶜ (S.Bind x) = Bind (lift-ε x)
lift-εᶜ (S.unlabel p) = unlabel p
lift-εᶜ S.unId = unId
lift-εᶜ (S.write {H = H} x τ∈π) with H ⊑? A
lift-εᶜ (S.write x τ∈π) | yes p = write x p τ∈π
lift-εᶜ (S.write x τ∈π) | no ¬p = write' x ¬p τ∈π
lift-εᶜ (S.write∙ x τ∈π) = write∙ x τ∈π
lift-εᶜ (S.read x) = read x

unlift-εᶜ : ∀ {l τ₁ τ₂} {C C' : Cont l τ₁ τ₂} -> Eraseᶜ C C' -> C' ≡ εᶜ C
unlift-εᶜ (Var τ∈π) = refl
unlift-εᶜ (# τ∈π) = refl
unlift-εᶜ (Then x Else x₁)
  rewrite unlift-ε x | unlift-ε x₁ = refl
unlift-εᶜ (Bind x) rewrite unlift-ε x = refl
unlift-εᶜ (unlabel p) = refl
unlift-εᶜ unId = refl
unlift-εᶜ (write {H = H} l⊑H H⊑A τ∈π) with H ⊑? A
unlift-εᶜ (write l⊑H H⊑A τ∈π) | yes p = refl
unlift-εᶜ (write l⊑H H⊑A τ∈π) | no ¬p = ⊥-elim (¬p H⊑A)
unlift-εᶜ (write' {H = H} l⊑H H⋤A τ∈π) with H ⊑? A
unlift-εᶜ (write' l⊑H H⋤A τ∈π) | yes p = ⊥-elim (H⋤A p)
unlift-εᶜ (write' l⊑H H⋤A τ∈π) | no ¬p = refl
unlift-εᶜ (write∙ l⊑H τ∈π) = refl
unlift-εᶜ (read L⊑H) = refl

--------------------------------------------------------------------------------

data Eraseˢ {l} : ∀ {τ₁ τ₂} -> Stack l τ₁ τ₂ -> Stack l τ₁ τ₂ -> Set where
  [] : ∀ {τ} -> Eraseˢ ([] {τ = τ}) []
  _∷_ : ∀ {τ₁ τ₂ τ₃} {C₁ C₂ : Cont l τ₁ τ₂} {S₁ S₂ : Stack l τ₂ τ₃} -> Eraseᶜ C₁ C₂ -> Eraseˢ S₁ S₂ -> Eraseˢ (C₁ ∷ S₁) (C₂ ∷ S₂)
  ∙ : ∀ {τ} -> Eraseˢ (∙ {τ = τ}) ∙

lift-εˢ : ∀ {l τ₁ τ₂} -> (S : Stack l τ₁ τ₂) -> Eraseˢ S (εˢ S)
lift-εˢ S.[] = []
lift-εˢ (x S.∷ S) = (lift-εᶜ x) ∷ (lift-εˢ S)
lift-εˢ S.∙ = ∙

unlift-εˢ : ∀ {l τ₁ τ₂} {S S' : Stack l τ₁ τ₂} -> Eraseˢ S S' -> S' ≡ εˢ S
unlift-εˢ [] = refl
unlift-εˢ (x ∷ x₁) rewrite unlift-εᶜ x | unlift-εˢ x₁ = refl
unlift-εˢ ∙ = refl

--------------------------------------------------------------------------------

open import Data.Maybe as M

data Eraseᴹ {π τ} : (mt₁ mt₂ : Maybe (Term π τ)) -> Set where
  nothing : Eraseᴹ nothing nothing
  just : ∀ {t₁ t₂} -> Erase t₁ t₂ -> Eraseᴹ (just t₁) (just t₂)

lift-εᴹ : ∀ {π τ} (mt : Maybe (Term π τ)) -> Eraseᴹ mt (M.map εᵀ mt)
lift-εᴹ (just x) = just (lift-ε x)
lift-εᴹ nothing = nothing

unlift-εᴹ : ∀ {π τ} {mt mt' : Maybe (Term π τ)} -> Eraseᴹ mt mt' -> mt' ≡ M.map εᵀ mt
unlift-εᴹ nothing = refl
unlift-εᴹ (just x) rewrite unlift-ε x = refl

--------------------------------------------------------------------------------

data Eraseᴱ {l} : ∀ {π} -> (Δ₁ Δ₂ : Env l π) -> Set where
  [] : Eraseᴱ [] []
  _∷_ : ∀ {π τ} {mt mt' : Maybe (Term π τ)} {Δ Δ' : Env l π} -> Eraseᴹ mt mt' -> Eraseᴱ Δ Δ' -> Eraseᴱ (mt ∷ Δ) (mt' ∷ Δ')
  ∙ : ∀ {π} -> Eraseᴱ {π = π} ∙ ∙

lift-εᴱ : ∀ {l π} -> (Δ : Env l π) -> Eraseᴱ Δ (εᴱ Δ)
lift-εᴱ S.[] = []
lift-εᴱ (t S.∷ Δ) = (lift-εᴹ t) ∷ (lift-εᴱ Δ)
lift-εᴱ S.∙ = ∙

unlift-εᴱ : ∀ {l π} {Δ Δ' : Env l π} -> Eraseᴱ Δ Δ' -> Δ' ≡ εᴱ Δ
unlift-εᴱ [] = refl
unlift-εᴱ (x ∷ x₁) rewrite unlift-εᴹ x | unlift-εᴱ x₁ = refl
unlift-εᴱ ∙ = refl

--------------------------------------------------------------------------------

data Eraseˣ {l} : (x : Dec (l ⊑ A)) (H₁ H₂ : Heap l) -> Set where
  ⟨_,_⟩ : ∀ {π} {M : Memory l} {Δ Δ' : Env l π} (l⊑A : l ⊑ A) -> Eraseᴱ Δ Δ' -> Eraseˣ (yes l⊑A) ⟨ M , Δ ⟩ ⟨ M , Δ' ⟩
  ∙ᴸ : {l⊑A : l ⊑ A} -> Eraseˣ (yes l⊑A) ∙ ∙
  ∙ : ∀ {H : Heap l} {l⋤A : l ⋤ A} -> Eraseˣ (no l⋤A) H ∙

lift-εˣ : ∀ {l} (x : Dec (l ⊑ A)) (H : Heap l) -> Eraseˣ x H (εᴹ x H)
lift-εˣ (yes p) S.⟨ x , x₁ ⟩ = ⟨ p , (lift-εᴱ x₁) ⟩
lift-εˣ (yes p) S.∙ = ∙ᴸ
lift-εˣ (no ¬p) H = ∙

unlift-εˣ : ∀ {l} {H H' : Heap l} {x : Dec (l ⊑ A)} -> Eraseˣ x H H' -> H' ≡ εᴹ x H
unlift-εˣ ⟨ l⊑A , x ⟩ rewrite unlift-εᴱ x = refl
unlift-εˣ {l} ∙ᴸ with l ⊑? A
unlift-εˣ ∙ᴸ | yes p = refl
unlift-εˣ (∙ᴸ {l⊑A = l⊑A}) | no ¬p = ⊥-elim (¬p l⊑A)
unlift-εˣ ∙ = refl

--------------------------------------------------------------------------------

data Eraseᴴ : ∀ {ls} -> Heaps ls -> Heaps ls -> Set where
  [] : Eraseᴴ [] []
  _∷_ : ∀ {l ls} {u : Unique l ls} {H₁ H₂ : Heap l} {Γ₁ Γ₂ : Heaps ls}  ->
          Eraseˣ (l ⊑? A) H₁ H₂ -> Eraseᴴ Γ₁ Γ₂ -> Eraseᴴ (H₁ ∷ Γ₁) (H₂ ∷ Γ₂)

lift-εᴴ : ∀ {ls} (H : Heaps ls) -> Eraseᴴ H (εᴴ H)
lift-εᴴ S.[] = []
lift-εᴴ (x S.∷ H) = (lift-εˣ (_ ⊑? A) x) ∷ (lift-εᴴ H)

unlift-εᴴ : ∀ {ls} {H H' : Heaps ls} -> Eraseᴴ H H' -> H' ≡ εᴴ H
unlift-εᴴ [] = refl
unlift-εᴴ {l ∷ ls} (x₁ ∷ x₂) rewrite unlift-εˣ x₁ | unlift-εᴴ x₂ = refl

--------------------------------------------------------------------------------

data Eraseᴾ {l ls τ} : Dec (l ⊑ A) -> Program l ls τ -> Program l ls τ -> Set where
  ⟨_,_,_⟩ : ∀ {τ' π Γ Γ'} {S S' : Stack l τ' τ} {t t' : Term π τ'} {l⊑A : l ⊑ A} ->
              Eraseᴴ Γ Γ' -> Erase t t' -> Eraseˢ S S' -> Eraseᴾ (yes l⊑A) ⟨ Γ , t , S ⟩ ⟨ Γ' , t' , S' ⟩
  ∙ : ∀ {p} {l⋤A : l ⋤ A} -> Eraseᴾ (no l⋤A) p ∙
  ∙ᴸ : ∀ {l⊑A : l ⊑ A} -> Eraseᴾ (yes l⊑A) ∙ ∙

lift-εᴾ : ∀ {l ls τ} -> (x : Dec (l ⊑ A)) (p : Program l ls τ) -> Eraseᴾ x p (ε₁ᴾ x p)
lift-εᴾ (yes p) S.⟨ Γ , t , S ⟩ = ⟨ (lift-εᴴ Γ) , (lift-ε t) , (lift-εˢ S) ⟩
lift-εᴾ (yes p) S.∙ = ∙ᴸ
lift-εᴾ (no ¬p) p = ∙

unlift-εᴾ : ∀ {l ls τ} {p p' : Program l ls τ} {x : Dec (l ⊑ A)} -> Eraseᴾ x p p' -> p' ≡ ε₁ᴾ x p
unlift-εᴾ ⟨ x , x₁ , x₂ ⟩
  rewrite unlift-εᴴ x | unlift-ε x₁ | unlift-εˢ x₂ = refl
unlift-εᴾ ∙ = refl
unlift-εᴾ ∙ᴸ = refl

--------------------------------------------------------------------------------

data Eraseˢ′ {l τ} : Dec (l ⊑ A) -> State l τ -> State l τ -> Set where
  ⟨_,_,_⟩ : ∀ {l⊑A : l ⊑ A} {π τ'} {Δ Δ' : Env l π} {t t' : Term π τ'} {S S' : Stack _ _ _} ->
              Eraseᴱ Δ Δ' -> Erase t t' -> Eraseˢ S S' -> Eraseˢ′ (yes l⊑A) ⟨ Δ , t , S ⟩ ⟨ Δ' , t' , S' ⟩
  ∙ᴸ : ∀ {l⊑A : l ⊑ A} ->  Eraseˢ′ (yes l⊑A) ∙ ∙
  ∙ : ∀ {l⋤A : l ⋤ A} {p} ->  Eraseˢ′ (no l⋤A) p ∙
