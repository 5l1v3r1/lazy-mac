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

data _⇝_ {l : Label} : ∀ {τ} -> State l τ -> State l τ -> Set where

 App₁ : ∀ {τ₁ τ₂ τ₃ π} {Δ : Env l π} {t₁ : Term π (τ₁ => τ₂)} {t₂ : Term π τ₁} {S : Stack l τ₂ τ₃} ->
          -- TODO if we can write subst to work with only variables then we can even
          -- use restricted syntax
          ⟨ Δ , App t₁ t₂ , S ⟩ ⇝ ⟨ just t₂ ∷ Δ , wken t₁ (drop refl-⊆ˡ) , (Var {{π = τ₁ ∷ π}} hereᴿ) ∷ S ⟩

 App₂ : ∀ {β α τ'} {π : Context} {Δ : Env l π} {S : Stack l β τ'} {t : Term (α ∷ π) β}
            -> (α∈π : α ∈ᴿ π) ->
          ⟨ Δ , Abs t , Var α∈π ∷ S ⟩ ⇝ ⟨ Δ , subst (Var α∈π) t , S ⟩

 Var₁ : ∀ {τ τ'} {π π' : Context} {Δ Δ' : Env l π}  {S : Stack l τ τ'} {t : Term π τ}
        -> (τ∈π : τ ∈ᴿ π)
        -> (t∈Δ : τ∈π ↦ t ∈ᴱ Δ)
        -> (¬val :  ¬ (Value t))
        -> (rᴱ : Δ' ≔ Δ [ τ∈π ↛ t ]ᴱ)
        -> ⟨ Δ , Var {π = π} τ∈π , S ⟩ ⇝ ⟨ Δ'  , t , (# τ∈π) ∷ S ⟩   -- t

 Var₁' : ∀ {τ τ'} {π : Context} {Δ : Env l π} {S : Stack l τ τ'} {v : Term π τ}
         -> (τ∈π : τ ∈ᴿ π)
         -> (v∈Δ : τ∈π ↦ v ∈ᴱ Δ)
         -> (val : Value v)
         -> ⟨ Δ , Var {π = π} τ∈π , S ⟩ ⇝ ⟨ Δ , v , S ⟩

 Var₂ : ∀ {τ τ'} {π : Context} {Δ Δ' : Env l π} {S : Stack l τ τ'} {v : Term π τ}
        -> (τ∈π : τ ∈ᴿ π)
        -> (val : Value v)
        -> (uᴱ : Δ' ≔ Δ [ τ∈π ↦ v ]ᴱ)
        -> ⟨ Δ , v , (# τ∈π) ∷ S ⟩ ⇝ ⟨  Δ' , v , S ⟩

 If : ∀ {π τ τ'} {Δ : Env l π} {S : Stack l τ τ'} {t₁ : Term π Bool} {t₂ t₃ : Term π τ} ->
        ⟨ Δ , (If t₁ Then t₂ Else t₃) , S ⟩ ⇝ ⟨ Δ , t₁ , (Then t₂ Else t₃) ∷ S ⟩

 IfTrue : ∀ {π τ τ'} {Δ : Env l π} {S : Stack l τ τ'} {t₂ t₃ : Term π τ} ->
            ⟨ Δ , True {π = π}, (Then t₂ Else t₃) ∷ S ⟩ ⇝ ⟨ Δ , t₂ , S ⟩

 IfFalse : ∀ {π τ τ'} {Δ : Env l π} {S : Stack l τ τ'} {t₂ t₃ : Term π τ} ->
             ⟨ Δ , False {π = π}, (Then t₂ Else t₃) ∷ S ⟩ ⇝ ⟨ Δ , t₂ , S ⟩

 Return : ∀ {π τ τ'} {Δ : Env l π} {S : Stack l _ τ'} {t : Term π τ} ->
            ⟨ Δ , Return l t , S ⟩ ⇝ ⟨ Δ , Mac l t , S ⟩

 Bind₁ : ∀ {π α β τ'} {Δ : Env l π} {S : Stack l _ τ'} {t₁ : Term π (Mac l α)} {t₂ : Term π (α => Mac l β)} ->
           ⟨ Δ , t₁ >>= t₂ , S ⟩ ⇝ ⟨ Δ , t₁ , (Bind t₂ ∷ S ) ⟩

 Bind₂ : ∀ {π α β τ'} {Δ : Env l π} {S : Stack l _ τ'} {t₁ : Term π α} {t₂ : Term π (α => (Mac l β))} ->
           ⟨ Δ , Mac l t₁ , Bind t₂ ∷ S ⟩ ⇝ ⟨ Δ , App t₂ t₁ , S ⟩

 Label' : ∀ {π h τ τ'} {Δ : Env l π} {S : Stack l _ τ'} {t : Term π τ} -> (p : l ⊑ h) ->
            ⟨ Δ , label p t , S ⟩ ⇝ ⟨ Δ , (Return l (Res h (Id t))) , S ⟩

 Label'∙ : ∀ {π h τ τ'} {Δ : Env l π} {S : Stack l _ τ'} {t : Term π τ} -> (p : l ⊑ h) ->
            ⟨ Δ , label∙ p t , S ⟩ ⇝ ⟨ Δ , (Return l (Res {π = π} h ∙)) , S ⟩

 Unlabel₁ : ∀ {π τ τ' l'} {Δ : Env l π} {S : Stack l _ τ'} {t : Term π (Labeled l' τ)} -> (p : l' ⊑ l) ->
              ⟨ Δ , unlabel p t , S ⟩ ⇝ ⟨ Δ , t , unlabel p ∷ S ⟩

 Unlabel₂ : ∀ {π τ τ' l'} {Δ : Env l π} {S : Stack l _ τ'} {t : Term π (Id τ)} -> (p : l' ⊑ l) ->
              ⟨ Δ , Res l' t , unlabel p ∷ S ⟩ ⇝ ⟨ Δ , Return l (unId t) , S ⟩

 UnId₁ : ∀ {π τ τ'} {Δ : Env l π} {S : Stack l τ τ'} {t : Term π (Id τ)} ->
           ⟨ Δ , unId t , S ⟩ ⇝ ⟨ Δ , t , unId ∷ S ⟩

 UnId₂ : ∀ {π τ τ'} {Δ : Env l π} {S : Stack l τ τ'} {t : Term π τ} ->
           ⟨ Δ , Id t , unId ∷ S ⟩ ⇝ ⟨ Δ , t , S ⟩

 Fork : ∀ {π τ h} {Δ : Env l π} {S : Stack l _ τ} {t : Term π (Mac h _)} -> (p : l ⊑ h) ->
          ⟨ Δ , (fork p t) , S ⟩ ⇝ ⟨ Δ , Return {π = π} l （） , S ⟩

 -- We have to write the term in the memory segment labeled as the reference (H)
 -- so that it can be correctly read by threads labeled with H or more.
 -- Note that if the current thread can also read the reference, then l ≡ H and we
 -- are still writing in the right memory.
 -- New : ∀ {Γ Γ' τ τ' H} {π : Context} {Δ : Env H π} {S : Stack l _ τ'} {t : Term π τ} {l⊑h : l ⊑ H}
 --         -> (Δ∈Γ : H ↦ Δ ∈ᴴ Γ)
 --         -- Insert the value (t) and a pointer (hereᴿ) to it.
 --         -> (uᴴ : Γ' ≔ Γ [ H ↦ insert (Var hereᴿ) (insert t Δ) ]ᴴ) ->
 --         -- Return a reference with a pointer (hereᴿ) to the pointer in the heap.
 --         ⟨ Γ , (new l⊑h t) , S ⟩ ⇝ ⟨ Γ' , (Return l (Res {π = τ ∷ (τ ∷ π)} H #[ Var (hereᴿ {{τ ∷ π}} ) ])) , S ⟩

 -- New∙ : ∀ {Γ τ τ' H} {π : Context} {S : Stack l _ τ'} {t : Term π τ} {l⊑h : l ⊑ H} ->
 --         ⟨ Γ , new∙ l⊑h t , S ⟩ ⇝ ⟨ Γ , Return l (Res {π = τ ∷ (τ ∷ π)} H ∙) , S ⟩

 -- Write₁ : ∀ {Γ Γ' τ τ' H} {π : Context} {Δ : Env H π} {S : Stack l _ τ'} {t₁ : Term π (Ref H τ)} {t₂ : Term π τ} {l⊑H : l ⊑ H} ->
 --            (Δ∈Γ : H ↦ Δ ∈ᴴ Γ)
 --            (uᴴ : Γ' ≔ Γ [ H ↦ insert t₂ Δ ]ᴴ ) ->
 --         ⟨ Γ , write l⊑H t₁ t₂ , S ⟩ ⇝ ⟨ Γ' , t₁ , (write l⊑H (hereᴿ {{π}}) ∷ S) ⟩

 -- Write∙₁ : ∀ {Γ τ τ' H} {π : Context} {S : Stack l _ τ'} {t₁ : Term π (Ref H τ)} {t₂ : Term π τ} {l⊑H : l ⊑ H} ->
 --         ⟨ Γ , write∙ l⊑H t₁ t₂ , S ⟩ ⇝ ⟨ Γ , t₁ , (write∙ l⊑H (hereᴿ {{π}}) ∷ S) ⟩

 -- Write₂ : ∀ {Γ Γ' τ τ' H} {π : Context} {Δ Δ' : Env H π} {S : Stack l _ τ'} {l⊑H : l ⊑ H} {τ∈π τ∈π' : τ ∈ᴿ π}
 --          -> (Δ∈Γ : H ↦ Δ ∈ᴴ Γ)
 --          -> (uᴱ : Δ' ≔ Δ [ τ∈π ↦ Var {π = π} τ∈π' ]ᴱ)
 --          -> (uᴴ : Γ' ≔ Γ [ H ↦ Δ' ]ᴴ) ->
 --         ⟨ Γ , Res {π = π} H #[ Var τ∈π ] , write l⊑H τ∈π' ∷ S ⟩ ⇝ ⟨ Γ' , Return {π = π} l （） , S ⟩

 -- Write∙₂ :  ∀ {Γ τ τ' H} {π : Context} {S : Stack l _ τ'} {l⊑H : l ⊑ H} {t : Term π (Addr τ)} {τ∈π' : τ ∈ᴿ π} ->
 --            ⟨ Γ , Res {π = π} H t , write∙ l⊑H τ∈π' ∷ S ⟩ ⇝ ⟨ Γ , Return {π = π} l （） , S ⟩

 -- Writeᴰ₂ : ∀ {Γ Γ' τ τ' H} {π : Context} {Δ Δ' : Env H π} {S : Stack l _ τ'} {l⊑H : l ⊑ H} {τ∈π τ∈π' : τ ∈ᴿ π} ->
 --             (Δ∈Γ : H ↦ Δ ∈ᴴ Γ)
 --          -> (uᴱ : Δ' ≔ Δ [ τ∈π ↦ Var {π = π} τ∈π' ]ᴱ)
 --          -> (uᴴ : Γ' ≔ Γ [ H ↦ Δ' ]ᴴ) ->
 --         ⟨ Γ , Res {π = π} H #[ Var τ∈π ]ᴰ , write l⊑H τ∈π' ∷ S ⟩ ⇝ ⟨ Γ' , Return {π = π} l （） , S ⟩

 -- Read₁ : ∀ {Γ τ τ' L} {π : Context} {S : Stack l _ τ'} {t : Term π (Ref L τ)} {L⊑l : L ⊑ l} ->
 --         ⟨ Γ , read L⊑l t , S ⟩ ⇝ ⟨ Γ , t , read L⊑l ∷ S ⟩

 -- Read₂ : ∀ {Γ τ τ' L} {π : Context} {Δ : Env L π} {S : Stack l _ τ'} {t : Term π τ} {L⊑l : L ⊑ l}
 --         -> (τ∈π : τ ∈ᴿ π)
 --         -> (Δ∈Γ : L ↦ Δ ∈ᴴ Γ)
 --         -> (t∈Δ : τ∈π ↦ t ∈ᴱ Δ) ->
 --         ⟨ Γ , Res L #[ (Var {π = π} τ∈π) ] , read L⊑l ∷ S ⟩ ⇝ ⟨ Γ , Return l t , S ⟩

 -- Readᴰ₂ : ∀ {Γ τ τ' L} {π : Context} {Δ : Env L π} {S : Stack l _ τ'} {t : Term π τ} {L⊑l : L ⊑ l}
 --         -> (τ∈π : τ ∈ᴿ π)
 --         -> (Δ∈Γ : L ↦ Δ ∈ᴴ Γ)
 --         -> (t∈Δ : τ∈π ↦ t ∈ᴱ Δ) ->
 --         -- Without restricted syntax I believe we can directly deepDup the term pointed by τ∈π
 --         -- (No need to introduce a fresh copy)
 --         ⟨ Γ , Res L #[ (Var {π = π} τ∈π) ]ᴰ , read L⊑l ∷ S ⟩ ⇝ ⟨ Γ , Return l (deepDup t) , S ⟩

 Hole : ∀ {τ} -> ∙ {τ = τ} ⇝ ∙

--  -- deepDupᵀ t takes care of replacing unguarded free variables with deepDup.
--  -- Note that deepDupᵀ (deepDup t) = deepDup t, so also in case of
--  -- nested deepDup (e.g. deepDup (deepDup t)) we make progress.
--  DeepDup : ∀ {Γ Γ' π τ τ'} {Δ : Env l π} {t : Term π τ} {S : Stack l τ τ'}
--                  -> (τ∈π : τ ∈ᴿ π)
--                  -> (Δ∈Γ : l ↦ Δ ∈ᴴ Γ)
--                  -> (t∈Δ : τ∈π ↦ t ∈ᴱ Δ)
--                  -> (uᴴ : Γ' ≔ Γ [ l ↦ insert (deepDupᵀ t) Δ ]ᴴ)
--                  -> ⟨ Γ , deepDup (Var {π = π} τ∈π) , S ⟩ ⇝ ⟨ Γ' , Var {π = τ ∷ π} hereᴿ , S ⟩


--  -- If the argument to deepDup is not a variable we introduce a new fresh variable (similarly to
--  -- so that next rule DeepDup will apply.
--  DeepDup' : ∀ {Γ Γ' π τ τ'} {Δ : Env l π} {t : Term π τ} {S : Stack l τ τ'}
--               -> (¬var : ¬ (IsVar t))
--               -> (Δ∈Γ : l ↦ Δ ∈ᴴ Γ)
--               -> (uᴴ : Γ' ≔ Γ [ l ↦ insert t Δ ]ᴴ)
--               -> ⟨ Γ , deepDup t , S ⟩ ⇝ ⟨ Γ' , deepDup (Var {π = τ ∷ π} hereᴿ) , S ⟩
