open import Lattice

module Sequential.Semantics {- (𝓛 : Lattice) -} where

open import Types
open import Sequential.Calculus
open import Data.Maybe
open import Data.Product
open import Data.Map
open import Relation.Binary.PropositionalEquality hiding ([_] ; subst)

--------------------------------------------------------------------------------
-- DeepDup helper functions and data types

open import Data.Bool using (not)
open import Data.List using (filter)
open import Relation.Nullary.Decidable using (⌊_⌋)


--------------------------------------------------------------------------------

-- Operational Semantics
-- Here since we use the Substs proof we implicitly rule out name clashes in substitutions.
-- Terms that do not comply with this assumption are not reducible according to this semantics,
-- however they could be after α-conversion (we simply don't want to deal with that,
-- and assume they have already been α-converted).
-- Note that stuck terms will be dealt with in the concurrent semantics.
data _⇝_ {l : Label} {ls : List Label} : ∀ {τ} -> State ls τ -> State ls τ -> Set where

 App₁ : ∀ {π τ₁ τ₂ τ₃ S} {t₁ : Term π (τ₁ => τ₂)} {t₂ : Term π τ₁} {S : Stack l π τ₂ τ₃} ->
          ⟨ {!!} , (App t₁ t₂) , S ⟩ ⇝ ⟨ {!!} , t₁ , (Var {!!}) ∷ S ⟩

-- ∀ {Γ Γ' S t₁ t₂ n} -> Γ' ≔ᴬ Γ [ n ↦ (l , t₂) ]
--                            -> ⟨ Γ , App t₁ t₂ , S ⟩ ⇝ ⟨ Γ' , t₁ , Var n ∷ S ⟩

-- App₂ : ∀ {Γ n m t t' S} -> Subst m (Var n) t t' -> ⟨ Γ , Abs m t , Var n ∷ S ⟩ ⇝ ⟨ Γ , t' , S ⟩
 
 -- Var₁ : ∀ {Γ Γ' n t S l'} -> ¬ (Value t)
 --                          -> Γ ≔ᴿ Γ' [ n ↦ (l' , t) ]
 --                          -> ⟨ Γ' , Var n , S ⟩ ⇝ ⟨ Γ , t , (# l n) ∷ S ⟩

 -- Var₁' : ∀ {Γ n v S l'} -> Value v
 --                           -> n ↦ (l' , v) ∈ Γ
 --                           -> ⟨ Γ , Var n , S ⟩ ⇝ ⟨ Γ , v , S ⟩

 -- Var₂ : ∀ {Γ Γ' n v S} -> Γ' ≔ᴾ Γ [ n ↦ (l , v) ]
 --                       -> Value v
 --                       -> ⟨ Γ , v , (# l n) ∷ S ⟩ ⇝ ⟨ Γ' , v , S ⟩

 -- If : ∀ {Γ t₁ t₂ t₃ S} -> ⟨ Γ , (If t₁ Then t₂ Else t₃) , S ⟩ ⇝ ⟨ Γ , t₁ , (Then t₂ Else t₃) ∷ S ⟩
 -- IfTrue : ∀ {Γ t₂ t₃ S} -> ⟨ Γ , True , (Then t₂ Else t₃) ∷ S ⟩ ⇝ ⟨ Γ , t₂ , S ⟩
 -- IfFalse : ∀ {Γ t₂ t₃ S} -> ⟨ Γ , False , (Then t₂ Else t₃) ∷ S ⟩ ⇝ ⟨ Γ , t₃ , S ⟩

 -- Return : ∀ {Γ t S} -> ⟨ Γ , Return l t , S ⟩ ⇝ ⟨ Γ , Mac l t , S ⟩
 -- Bind₁ : ∀ {Γ t₁ t₂ S} -> ⟨ Γ , Bind l t₁ t₂ , S ⟩ ⇝ ⟨ Γ , t₁ , (Bind l t₂ ∷ S ) ⟩
 -- Bind₂ : ∀ {Γ t₁ t₂ S} -> ⟨ Γ , Mac l t₁ , Bind l t₂ ∷ S ⟩ ⇝ ⟨ Γ , App t₂ t₁ , S  ⟩

 -- Label' : ∀ {Γ t S h} -> (p : l ⊑ h) -> ⟨ Γ , label p t , S ⟩ ⇝ ⟨ Γ , (Return l (Res h (Id t))) , S ⟩

 -- Unlabel₁ : ∀ {Γ t S l'} -> (p : l' ⊑ l) -> ⟨ Γ , unlabel p t , S ⟩ ⇝ ⟨ Γ , t , unlabel p ∷ S ⟩
 -- Unlabel₂ : ∀ {Γ t S l'} -> (p : l' ⊑ l) -> ⟨ Γ , Res l' t , unlabel p ∷ S ⟩ ⇝ ⟨ Γ , Return l (unId t) , S ⟩

 -- UnId₁ : ∀ {Γ t S} -> ⟨ Γ , unId t , S ⟩ ⇝ ⟨ Γ , t , unId ∷ S ⟩ 
 -- UnId₂ : ∀ {Γ t S} -> ⟨ Γ , Id t , unId ∷ S ⟩ ⇝ ⟨ Γ , t , S ⟩ 

 -- Fork : ∀ {Γ t S h} -> (p : l ⊑ h) -> ⟨ Γ , (fork p t) , S ⟩ ⇝ ⟨ Γ , Return l （） , S ⟩ 

 -- Hole : ∀ {Γ S} -> ⟨ Γ , ∙ , S ⟩ ⇝ ⟨ Γ , ∙ , S ⟩

 -- DeepDup : ∀ {Γ₁ Γ₂ Γ₃ n n' ns' S l' t t'} -> n ↦ (l' , t) ∈ Γ₁
 --                                -> Substs t (ufv t) ns' t'
 --                                -> Γ₂ ≔ᴰ Γ₁ [ ns' ↦ (l , ufv t) ]
 --                                -> Γ₃ ≔ᴬ Γ₂ [ n' ↦ (l , t') ]
 --                                -> ⟨ Γ₁ , (deepDup n) , S ⟩ ⇝ ⟨ Γ₃ , Var n' , S ⟩
