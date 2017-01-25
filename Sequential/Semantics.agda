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
          ⟨ Γ , (App t₁ t₂) , S ⟩ ⇝ ⟨ Γ' , t₁ , (Var {π = τ₁ ∷ π} {!!}) ∷ S ⟩ -- here

 App₂ : ∀ {Γ β α τ'} {π : Context} {S : Stack l β τ'} {t : Term (α ∷ π) β}
            -> (α∈π₁ : α ∈ᴿ π)
            -> (α∈π₂ : α ∈ᴿ π) ->
          ⟨ Γ , Abs t , Var {π = π} α∈π₁ ∷ S ⟩ ⇝ ⟨ Γ , subst (Var α∈π₂) t , S ⟩

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

 UnId₁ : ∀ {Γ τ τ'} {π : Context} {S : Stack l τ τ'} {t : Term π (Id τ)} ->
           ⟨ Γ , unId t , S ⟩ ⇝ ⟨ Γ , t , unId ∷ S ⟩

 UnId₂ : ∀ {Γ τ τ'} {π : Context} {S : Stack l τ τ'} {t : Term π τ} ->
           ⟨ Γ , Id t , unId ∷ S ⟩ ⇝ ⟨ Γ , t , S ⟩

 Fork : ∀ {Γ τ h} {π : Context} {S : Stack l _ τ} {t : Term π (Mac h _)} -> (p : l ⊑ h) ->
          ⟨ Γ , (fork p t) , S ⟩ ⇝ ⟨ Γ , Return {π = π} l （） , S ⟩

 -- We have to write the term in the memory segment labeled as the reference (H)
 -- so that it can be correctly read by threads labeled with H or more.
 -- Note that if the current thread can also read the reference, then l ≡ H and we
 -- are still writing in the right memory.
 New : ∀ {Γ Γ' τ τ' H} {π : Context} {Δ : Env H π} {S : Stack l _ τ'} {t : Term π τ} {l⊑h : l ⊑ H}
         -> (Δ∈Γ : H ↦ Δ ∈ᴴ Γ)
         -> (uᴴ : Γ' ≔ Γ [ H ↦ insert t Δ ]ᴴ) ->
         ⟨ Γ , (new l⊑h t) , S ⟩ ⇝ ⟨ Γ' , (Return l (Res {π = (τ ∷ π)} H #[ Var {!!} ])) , S ⟩ -- here

 Write₁ : ∀ {Γ τ τ' H} {π : Context} {S : Stack l _ τ'} {t₁ : Term π (Ref H τ)} {t₂ : Term π τ} {l⊑H : l ⊑ H} ->
         ⟨ Γ , write l⊑H t₁ t₂ , S ⟩ ⇝ ⟨ Γ , t₁ , (write l⊑H t₂ ∷ S) ⟩

 Write₂ : ∀ {Γ Γ' τ τ' H} {π : Context} {Δ Δ' : Env H π} {S : Stack l _ τ'} {t : Term π τ} {l⊑H : l ⊑ H} {τ∈π : τ ∈ π}
          -> (Δ∈Γ : H ↦ Δ ∈ᴴ Γ)
          -> (uᴱ : Δ' ≔ Δ [ τ∈π ↦ t ]ᴱ)  -- Not ok beause other code might reference τ∈π. We must change the Reference to point to t.
          -> (uᴴ : Γ' ≔ Γ [ H ↦ Δ' ]ᴴ) ->
         ⟨ Γ , Res {π = π} H #[ Var {!!} ] , write l⊑H t ∷ S ⟩ ⇝ ⟨ Γ' , Return {π = π} l （） , S ⟩ -- τ∈π

 Writeᴰ₂ : ∀ {Γ Γ' τ τ' H} {π : Context} {Δ Δ' : Env H π} {S : Stack l _ τ'} {t : Term π τ} {l⊑H : l ⊑ H} {τ∈π : τ ∈ π}
          -> (Δ∈Γ : H ↦ Δ ∈ᴴ Γ)
          -> (uᴱ : Δ' ≔ Δ [ τ∈π ↦ t ]ᴱ)
          -> (uᴴ : Γ' ≔ Γ [ H ↦ Δ' ]ᴴ) ->
         ⟨ Γ , Res {π = π} H #[ Var {!!} ]ᴰ , write l⊑H t ∷ S ⟩ ⇝ ⟨ Γ' , Return {π = π} l （） , S ⟩ -- τ∈π

 Read₁ : ∀ {Γ τ τ' L} {π : Context} {S : Stack l _ τ'} {t : Term π (Ref L τ)} {L⊑l : L ⊑ l} ->
         ⟨ Γ , read L⊑l t , S ⟩ ⇝ ⟨ Γ , t , read L⊑l ∷ S ⟩

 Read₂ : ∀ {Γ τ τ' L} {π : Context} {Δ : Env L π} {S : Stack l _ τ'} {t : Term π τ} {L⊑l : L ⊑ l} {τ∈π : τ ∈ π}
         -> (Δ∈Γ : L ↦ Δ ∈ᴴ Γ)
         -> (t∈Δ : τ∈π ↦ t ∈ᴱ Δ) ->
         ⟨ Γ , Res L #[ (Var τ∈π) ] , read L⊑l ∷ S ⟩ ⇝ ⟨ Γ , Return l t , S ⟩

 Readᴰ₂ : ∀ {Γ τ τ' L} {π : Context} {Δ : Env L π} {S : Stack l _ τ'} {t : Term π τ} {L⊑l : L ⊑ l} {τ∈π : τ ∈ π}
         -> (Δ∈Γ : L ↦ Δ ∈ᴴ Γ)
         -> (t∈Δ : τ∈π ↦ t ∈ᴱ Δ) ->
         -- Without restricted syntax I believe we can directly deepDup the term pointed by τ∈π
         -- (No need to introduce a fresh copy)
         ⟨ Γ , Res L #[ (Var τ∈π) ]ᴰ , read L⊑l ∷ S ⟩ ⇝ ⟨ Γ , Return l (deepDup t) , S ⟩

 Hole : ∀ {Γ τ₁ τ₂ τ₃} {π₁ : Context} {π₂ : Context} ->
          ⟨ Γ , ∙ {π = π₁}, ∙ {l} {τ₁} {τ₃} ⟩ ⇝ ⟨ Γ , ∙ {π = π₂} , ∙ {l} {τ₂} {τ₃} ⟩

-- I think that in this rule we should use
 -- Γ ≌ Γ', where we allow ∙ Environments to have different π:
 -- 1) [] ≌ []
 -- 2) Γ₁ ≌ Γ₂ => (∙ {π₁}) ∷ Γ₁ ≌ (∙ {π₂}) ∷ Γ₂
 -- 3) Γ₁ ≌ Γ₂ => Δ ∷ Γ₁ ≌ Δ ∷ Γ₂

 -- deepDupᵀ t takes care of replacing unguarded free variables with deepDup.
 -- Note that deepDupᵀ (deepDup t) = deepDup t, so also in case of
 -- nested deepDup (e.g. deepDup (deepDup t)) we make progress.
 DeepDup : ∀ {Γ Γ' π τ τ'} {Δ : Env l π} {t : Term π τ} {S : Stack l τ τ'} {τ∈π : τ ∈ π}
                 -> (Δ∈Γ : l ↦ Δ ∈ᴴ Γ)
                 -> (t∈Δ : τ∈π ↦ t ∈ᴱ Δ)
                 -> (uᴴ : Γ' ≔ Γ [ l ↦ insert (deepDupᵀ t) Δ ]ᴴ)
                 -> ⟨ Γ , deepDup (Var τ∈π) , S ⟩ ⇝ ⟨ Γ' , Var {π = τ ∷ π} {!!} , S ⟩ -- here


 -- If the argument to deepDup is not a variable we introduce a new fresh variable (similarly to
 -- so that next rule DeepDup will apply.
 DeepDup' : ∀ {Γ Γ' π τ τ'} {Δ : Env l π} {t : Term π τ} {S : Stack l τ τ'}
              -> (¬var : ¬ (IsVar t))
              -> (Δ∈Γ : l ↦ Δ ∈ᴴ Γ)
              -> (uᴴ : Γ' ≔ Γ [ l ↦ insert t Δ ]ᴴ)
              -> ⟨ Γ , deepDup t , S ⟩ ⇝ ⟨ Γ' , deepDup (Var {π = τ ∷ π} {!!}) , S ⟩ -- here
