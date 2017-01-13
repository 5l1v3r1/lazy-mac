module Sequential.Semantics {- (𝓛 : Lattice) -} where


open import Types
import Lattice
open Lattice.Lattice 𝓛 renaming (_≟_ to _≟ᴸ_)

open import Sequential.Calculus
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_] ; subst)

--------------------------------------------------------------------------------
-- DeepDup helper functions and data types

open import Data.Bool using (not)
open import Data.List using (filter ; length)
open import Relation.Nullary.Decidable using (⌊_⌋)

--------------------------------------------------------------------------------

-- Operational Semantics
-- Here since we use the Substs proof we implicitly rule out name clashes in substitutions.
-- Terms that do not comply with this assumption are not reducible according to this semantics,
-- however they could be after α-conversion (we simply don't want to deal with that,
-- and assume they have already been α-converted).
-- Note that stuck terms will be dealt with in the concurrent semantics.
data _⇝_ {l : Label} : ∀ {τ} -> State l τ -> State l τ -> Set where

 App₁ : ∀ {τ₁ τ₂ τ₃ Γ n} {π : Context n} {Δ : Env l π} {t₁ : Term π (τ₁ => τ₂)} {t₂ : Term π τ₁} {S : Stack l τ₂ τ₃} ->
          (Δ∈Γ : l ↦ Δ ∈ᴴ Γ) ->
          ⟨ Γ , (App t₁ t₂) , S ⟩ ⇝ ⟨ Γ [ l ↦ Δ [ suc n ↦ t₂ ] ]ᴴ , t₁ , (Var {π = ⟪ suc n , τ₁ , l ⟫ ∷ π} here) ∷ S ⟩

 App₂ : ∀ {Γ n n₁ n₂ β l' α τ'} {π : Context n} {S : Stack l β τ'} ->
          let x = ⟪ n₁ , α , l' ⟫
              y = ⟪ n₂ , α , l' ⟫ in {t : Term (y ∷ π) β}
            -> (y∈π : y ∈ π)
            -> (x∈π : x ∈ π) ->
          ⟨ Γ , Abs y t , Var x∈π ∷ S ⟩ ⇝ ⟨ Γ , subst (Var x∈π) t , S ⟩

 Var₁ : ∀ {Γ n l' τ τ'}{n'} {π : Context n'} {Δ : Env l' π}  {S : Stack l τ τ'} ->
          let x = ⟪ n , τ , l' ⟫ in {t : Term π τ}
        -> (Δ∈Γ : l' ↦ Δ ∈ᴴ Γ)
        -> (x∈π : x ∈ π)
        -> (t∈Δ : n ↦ t ∈ Δ)
        -> (¬val :  ¬ (Value t))
        -> ⟨ Γ , Var x∈π , S ⟩ ⇝ ⟨  Γ [ l' ↦ Δ [ n ↛ t ] ]ᴴ  , t , (# x∈π) ∷ S ⟩ -- Here we should prove that l == l'

 Var₁' : ∀ {Γ l' τ n τ'} {n'} {π : Context n'} {Δ : Env l' π} {S : Stack l τ τ'} ->
           let x = ⟪ n , τ , l' ⟫ in {v : Term π τ}
         -> (Δ∈Γ : l' ↦ Δ ∈ᴴ Γ)
         -> (x∈π : x ∈ π)
         -> (v∈Δ : n ↦ v ∈ Δ)
         -> (val : Value v)
         -> ⟨ Γ , Var x∈π , S ⟩ ⇝ ⟨ Γ , v , S ⟩

 Var₂ : ∀ {Γ n τ τ' l'} {n'} {π : Context n'} {Δ : Env l' π} {S : Stack l τ τ'} {v : Term π τ} ->
          let  x = ⟪ n , τ , l' ⟫ in
           (Δ∈Γ : l' ↦ Δ ∈ᴴ Γ)
        -> (x∈π : x ∈ π)
        -> (val : Value v)
        -> ⟨ Γ , v , (# x∈π) ∷ S ⟩ ⇝ ⟨  Γ [ l' ↦ Δ [ n ↦ v ] ]ᴴ , v , S ⟩  -- Here we should prove that l == l'

 If : ∀ {Γ n τ τ'} {π : Context n} {S : Stack l τ τ'} {t₁ : Term π Bool} {t₂ t₃ : Term π τ} ->
        ⟨ Γ , (If t₁ Then t₂ Else t₃) , S ⟩ ⇝ ⟨ Γ , t₁ , (Then t₂ Else t₃) ∷ S ⟩

 IfTrue : ∀ {Γ n τ τ'} {π : Context n} {S : Stack l τ τ'} {t₂ t₃ : Term π τ} ->
            ⟨ Γ , True {π = π}, (Then t₂ Else t₃) ∷ S ⟩ ⇝ ⟨ Γ , t₂ , S ⟩

 IfFalse : ∀ {Γ n τ τ'} {π : Context n} {S : Stack l τ τ'} {t₂ t₃ : Term π τ} ->
             ⟨ Γ , False {π = π}, (Then t₂ Else t₃) ∷ S ⟩ ⇝ ⟨ Γ , t₂ , S ⟩

 Return : ∀ {Γ n τ τ'} {π : Context n} {S : Stack l _ τ'} {t : Term π τ} ->
            ⟨ Γ , Return l t , S ⟩ ⇝ ⟨ Γ , Mac l t , S ⟩

 Bind₁ : ∀ {Γ n α β τ'} {π : Context n} {S : Stack l _ τ'} {t₁ : Term π (Mac l α)} {t₂ : Term π (α => Mac l β)} ->
           ⟨ Γ , t₁ >>= t₂ , S ⟩ ⇝ ⟨ Γ , t₁ , (Bind t₂ ∷ S ) ⟩

 Bind₂ : ∀ {Γ n α β τ'} {π : Context n} {S : Stack l _ τ'} {t₁ : Term π α} {t₂ : Term π (α => (Mac l β))} ->
           ⟨ Γ , Mac l t₁ , Bind t₂ ∷ S ⟩ ⇝ ⟨ Γ , App t₂ t₁ , S ⟩

 Label' : ∀ {Γ n h τ τ'} {π : Context n} {S : Stack l _ τ'} {t : Term π τ} -> (p : l ⊑ h) ->
            ⟨ Γ , label p t , S ⟩ ⇝ ⟨ Γ , (Return l (Res h (Id t))) , S ⟩

 Unlabel₁ : ∀ {Γ n τ τ' l'} {π : Context n} {S : Stack l _ τ'} {t : Term π (Labeled l' τ)} -> (p : l' ⊑ l) ->
              ⟨ Γ , unlabel p t , S ⟩ ⇝ ⟨ Γ , t , unlabel p ∷ S ⟩

 Unlabel₂ : ∀ {Γ n τ τ' l'} {π : Context n} {S : Stack l _ τ'} {t : Term π (Id τ)} -> (p : l' ⊑ l) ->
              ⟨ Γ , Res l' t , unlabel p ∷ S ⟩ ⇝ ⟨ Γ , Return l (unId t) , S ⟩

 UnId₁ : ∀ {Γ n τ τ'} {π : Context n} {S : Stack l τ τ'} {t : Term π (Id τ)} ->
           ⟨ Γ , unId t , S ⟩ ⇝ ⟨ Γ , t , unId ∷ S ⟩

 UnId₂ : ∀ {Γ n τ τ'} {π : Context n} {S : Stack l τ τ'} {t : Term π τ} ->
           ⟨ Γ , Id t , unId ∷ S ⟩ ⇝ ⟨ Γ , t , S ⟩

 Fork : ∀ {Γ n τ h} {π : Context n} {S : Stack l _ τ} {t : Term π (Mac h _)} -> (p : l ⊑ h) ->
          ⟨ Γ , (fork p t) , S ⟩ ⇝ ⟨ Γ , Return {π = π} l （） , S ⟩

 Hole : ∀ {Γ n₁ n₂ τ₁ τ₂ τ₃} {π₁ : Context n₁} {π₂ : Context n₂} ->
          ⟨ Γ , ∙ {π = π₁}, ∙ {l} {τ₁} {τ₃} ⟩ ⇝ ⟨ Γ , ∙ {π = π₂} , ∙ {l} {τ₂} {τ₃} ⟩

 -- DeepDup : ∀ {Γ₁ Γ₂ Γ₃ n n' ns' S l' t t'} -> n ↦ (l' , t) ∈ Γ₁
 --                                -> Substs t (ufv t) ns' t'
 --                                -> Γ₂ ≔ᴰ Γ₁ [ ns' ↦ (l , ufv t) ]
 --                                -> Γ₃ ≔ᴬ Γ₂ [ n' ↦ (l , t') ]
 --                                -> ⟨ Γ₁ , (deepDup n) , S ⟩ ⇝ ⟨ Γ₃ , Var n' , S ⟩
