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
data _⇝_ {ls : List Label} {l : Label} : ∀ {τ} -> State ls l τ -> State ls l τ -> Set where

 App₁ : ∀ {τ₁ τ₂ τ₃ π Γ Γ'} {Δ : Env l π} {t₁ : Term π (τ₁ => τ₂)} {t₂ : Term π τ₁} {S : Stack l τ₂ τ₃}
          -> (Δ∈Γ : l ↦ Δ ∈ᴴ Γ)
          -> (uᴴ : Γ' ≔ Γ [ l ↦ insert t₂ Δ ]ᴴ) ->
          ⟨ Γ , (App t₁ t₂) , S ⟩ ⇝ ⟨ Γ' , t₁ , (Var {π = τ₁ ∷ π} here) ∷ S ⟩

 App₂ : ∀ {Γ β α τ'} {π : Context} {S : Stack l β τ'} {t : Term (α ∷ π) β}
            -> (α∈π : α ∈ π)
            -> (α∈π : α ∈ π) ->
          ⟨ Γ , Abs t , Var α∈π ∷ S ⟩ ⇝ ⟨ Γ , subst (Var α∈π) t , S ⟩

 Var₁ : ∀ {Γ Γ' τ τ'} {π π' : Context} {Δ Δ' : Env l π}  {S : Stack l τ τ'} {t : Term π' τ} ->
           (Δ∈Γ : l ↦ Δ ∈ᴴ Γ)
        -> (τ∈π : τ ∈ π)
        -> (t∈Δ : τ∈π ↦ t ∈ᴱ Δ)
        -> (¬val :  ¬ (Value t))
        -> (rᴱ : Δ' ≔ Δ [ τ∈π ↛ t ]ᴱ)
        -> (uᴴ : Γ' ≔ Γ [ l ↦ Δ' ]ᴴ)
        -> ⟨ Γ , Var τ∈π , S ⟩ ⇝ ⟨  Γ'  , t , (# τ∈π) ∷ S ⟩

 Var₁' : ∀ {Γ τ τ'} {π : Context} {Δ : Env l π} {S : Stack l τ τ'} {v : Term π τ}
         -> (Δ∈Γ : l ↦ Δ ∈ᴴ Γ)
         -> (τ∈π : τ ∈ π)
         -> (v∈Δ : τ∈π ↦ v ∈ᴱ Δ)
         -> (val : Value v)
         -> ⟨ Γ , Var τ∈π , S ⟩ ⇝ ⟨ Γ , v , S ⟩

 Var₂ : ∀ {Γ Γ' τ τ'} {π : Context} {Δ Δ' : Env l π} {S : Stack l τ τ'} {v : Term π τ} ->
           (Δ∈Γ : l ↦ Δ ∈ᴴ Γ)
        -> (τ∈π : τ ∈ π)
        -> (val : Value v)
        -> (uᴱ : Δ' ≔ Δ [ τ∈π ↦ v ]ᴱ)
        -> (uᴴ : Γ' ≔ Γ [ l ↦ Δ' ]ᴴ)
        -> ⟨ Γ , v , (# τ∈π) ∷ S ⟩ ⇝ ⟨  Γ' , v , S ⟩

 If : ∀ {Γ τ τ'} {π : Context} {S : Stack l τ τ'} {t₁ : Term π Bool} {t₂ t₃ : Term π τ} ->
        ⟨ Γ , (If t₁ Then t₂ Else t₃) , S ⟩ ⇝ ⟨ Γ , t₁ , (Then t₂ Else t₃) ∷ S ⟩

 IfTrue : ∀ {Γ τ τ'} {π : Context} {S : Stack l τ τ'} {t₂ t₃ : Term π τ} ->
            ⟨ Γ , True {π = π}, (Then t₂ Else t₃) ∷ S ⟩ ⇝ ⟨ Γ , t₂ , S ⟩

 IfFalse : ∀ {Γ τ τ'} {π : Context} {S : Stack l τ τ'} {t₂ t₃ : Term π τ} ->
             ⟨ Γ , False {π = π}, (Then t₂ Else t₃) ∷ S ⟩ ⇝ ⟨ Γ , t₂ , S ⟩

 Return : ∀ {Γ τ τ'} {π : Context} {S : Stack l _ τ'} {t : Term π τ} ->
            ⟨ Γ , Return l t , S ⟩ ⇝ ⟨ Γ , Mac l t , S ⟩

 Bind₁ : ∀ {Γ α β τ'} {π : Context} {S : Stack l _ τ'} {t₁ : Term π (Mac l α)} {t₂ : Term π (α => Mac l β)} ->
           ⟨ Γ , t₁ >>= t₂ , S ⟩ ⇝ ⟨ Γ , t₁ , (Bind t₂ ∷ S ) ⟩

 Bind₂ : ∀ {Γ α β τ'} {π : Context} {S : Stack l _ τ'} {t₁ : Term π α} {t₂ : Term π (α => (Mac l β))} ->
           ⟨ Γ , Mac l t₁ , Bind t₂ ∷ S ⟩ ⇝ ⟨ Γ , App t₂ t₁ , S ⟩

 Label' : ∀ {Γ h τ τ'} {π : Context} {S : Stack l _ τ'} {t : Term π τ} -> (p : l ⊑ h) ->
            ⟨ Γ , label p t , S ⟩ ⇝ ⟨ Γ , (Return l (Res h (Id t))) , S ⟩

 Label'∙ : ∀ {Γ h τ τ'} {π : Context} {S : Stack l _ τ'} {t : Term π τ} -> (p : l ⊑ h) ->
            ⟨ Γ , label∙ p t , S ⟩ ⇝ ⟨ Γ , (Return l (Res {π = π} h ∙)) , S ⟩


 Unlabel₁ : ∀ {Γ τ τ' l'} {π : Context} {S : Stack l _ τ'} {t : Term π (Labeled l' τ)} -> (p : l' ⊑ l) ->
              ⟨ Γ , unlabel p t , S ⟩ ⇝ ⟨ Γ , t , unlabel p ∷ S ⟩

 Unlabel₂ : ∀ {Γ τ τ' l'} {π : Context} {S : Stack l _ τ'} {t : Term π (Id τ)} -> (p : l' ⊑ l) ->
              ⟨ Γ , Res l' t , unlabel p ∷ S ⟩ ⇝ ⟨ Γ , Return l (unId t) , S ⟩

 Unlabel∙₁ : ∀ {Γ τ τ' l'} {π : Context} {S : Stack l _ τ'} {t : Term π (Labeled l' τ)} -> (p : l' ⊑ l) ->
              ⟨ Γ , unlabel∙ p t , S ⟩ ⇝ ⟨ Γ , t , unlabel∙ p ∷ S ⟩

 Unlabel∙₂ : ∀ {Γ τ τ' l'} {π : Context} {S : Stack l _ τ'} {t : Term π (Id τ)} -> (p : l' ⊑ l) ->
              ⟨ Γ , Res l' t , unlabel∙ p ∷ S ⟩ ⇝ ⟨ Γ , Return {π = π} l ∙ , S ⟩

 UnId₁ : ∀ {Γ τ τ'} {π : Context} {S : Stack l τ τ'} {t : Term π (Id τ)} ->
           ⟨ Γ , unId t , S ⟩ ⇝ ⟨ Γ , t , unId ∷ S ⟩

 UnId₂ : ∀ {Γ τ τ'} {π : Context} {S : Stack l τ τ'} {t : Term π τ} ->
           ⟨ Γ , Id t , unId ∷ S ⟩ ⇝ ⟨ Γ , t , S ⟩

 Fork : ∀ {Γ τ h} {π : Context} {S : Stack l _ τ} {t : Term π (Mac h _)} -> (p : l ⊑ h) ->
          ⟨ Γ , (fork p t) , S ⟩ ⇝ ⟨ Γ , Return {π = π} l （） , S ⟩

 Hole : ∀ {Γ τ₁ τ₂ τ₃} {π₁ : Context} {π₂ : Context} ->
          ⟨ Γ , ∙ {π = π₁}, ∙ {l} {τ₁} {τ₃} ⟩ ⇝ ⟨ Γ , ∙ {π = π₂} , ∙ {l} {τ₂} {τ₃} ⟩

-- I think that in this rule we should use
 -- Γ ≌ Γ', where we allow ∙ Environments to have different π:
 -- 1) [] ≌ []
 -- 2) Γ₁ ≌ Γ₂ => (∙ {π₁}) ∷ Γ₁ ≌ (∙ {π₂}) ∷ Γ₂
 -- 3) Γ₁ ≌ Γ₂ => Δ ∷ Γ₁ ≌ Δ ∷ Γ₂

 DeepDup : ∀ {Γ Γ' n ns' t π τ τ'} {Δ : Env l π} {t : Term π τ} {S : Stack l τ τ'} {τ∈π : τ ∈ π}
                 -> l ↦ Δ ∈ᴴ Γ
                 -> TypedIx τ n π τ∈π
                 -> τ∈π ↦ t ∈ᴱ Δ
                 -> Γ' ≔ Γ [ l ↦ {!!} ]ᴴ

 --                                -> Substs t (ufv t) ns' t'
 --                                -> Γ₂ ≔ᴰ Γ₁ [ ns' ↦ (l , ufv t) ]
 --                                -> Γ₃ ≔ᴬ Γ₂ [ n' ↦ (l , t') ]
                                -> ⟨ Γ , deepDup n , S ⟩ ⇝ ⟨ Γ' , {!!} , S ⟩
