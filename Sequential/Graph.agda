-- This module defines the graph of the erasure function on terms

-- TODO move all erasure related modules in a new Security module

import Lattice as L

module Sequential.Graph (𝓛 : L.Lattice) (A : L.Label 𝓛) where

open import Types 𝓛
import Sequential.Calculus as S
open S 𝓛
open import Sequential.Erasure 𝓛 A as SE

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

open import Relation.Binary.PropositionalEquality
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
