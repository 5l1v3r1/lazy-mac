import Lattice as L

module Sequential.Semantics (𝓛 : L.Lattice) where

open import Types 𝓛
open import Sequential.Calculus 𝓛

open import Data.Maybe
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_] ; subst)

--------------------------------------------------------------------------------

-- The invariant that we maintain is that in a step of thread l
-- we introduce only variables at level l.
-- Variables from lower level should occur only inside a deepDup.
data _⇝_ {l : Label} : ∀ {τ} -> State l τ -> State l τ -> Set where

 App₁ : ∀ {τ₁ τ₂ τ₃ π} {Δ : Env l π} {t₁ : Term π (τ₁ => τ₂)} {t₂ : Term π τ₁} {S : Stack l τ₂ τ₃} ->
          ⟨ Δ , App t₁ t₂ , S ⟩ ⇝ ⟨ just t₂ ∷ Δ ,  wken t₁ (drop refl-⊆ˡ) , (Var {{π = τ₁ ∷ π}} ⟪ hereᴿ ⟫) ∷ S ⟩

 App₂ : ∀ {β α τ'} {π : Context} {Δ : Env l π} {S : Stack l β τ'} {t : Term (α ∷ π) β}
            -> (α∈π : α ∈⟨ l ⟩ᴿ π) ->
          ⟨ Δ , Abs t , Var α∈π ∷ S ⟩ ⇝ ⟨ Δ , subst (Var α∈π) t , S ⟩

 Var₁ : ∀ {τ τ'} {π : Context} {Δ Δ' : Env l π}  {S : Stack l τ τ'} {t : Term π τ}
        -> (τ∈π : τ ∈⟨ l ⟩ᴿ π)
        -> (t∈Δ : τ∈π ↦ t ∈ᴱ Δ)
        -> (¬val :  ¬ (Value t))
        -> (rᴱ : Δ' ≔ Δ [ τ∈π ↛ t ]ᴱ)
        -> ⟨ Δ , Var {π = π} τ∈π , S ⟩ ⇝ ⟨ Δ'  , t , (# τ∈π) ∷ S ⟩

 Var₁' : ∀ {τ τ'} {π : Context} {Δ : Env l π} {S : Stack l τ τ'} {v : Term π τ}
         -> (τ∈π : τ ∈⟨ l ⟩ᴿ π)
         -> (v∈Δ : τ∈π ↦ v ∈ᴱ Δ)
         -> (val : Value v)
         -> ⟨ Δ , Var {π = π} τ∈π , S ⟩ ⇝ ⟨ Δ , v , S ⟩

 Var₂ : ∀ {τ τ'} {π : Context} {Δ Δ' : Env l π} {S : Stack l τ τ'} {v : Term π τ}
        -> (τ∈π : τ ∈⟨ l ⟩ᴿ π)
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

 Hole₁ : ∀ {τ} -> ∙ {τ = τ} ⇝ ∙

 Hole₂ : ∀ {τ} {π} -> ⟨ ∙ {{π}} , ∙ {{τ}} , ∙ ⟩ ⇝ ⟨ ∙ {{π}} , ∙ , ∙ ⟩

 -- deepDupᵀ t takes care of replacing unguarded free variables with deepDup.
 -- Note that deepDupᵀ (deepDup t) = deepDup t, so also in case of
 -- nested deepDup (e.g. deepDup (deepDup t)) we make progress.
 DeepDup : ∀ {π τ τ'} {Δ : Env l π} {t : Term π τ} {S : Stack l τ τ'}
             -> (τ∈π : τ ∈⟨ l ⟩ᴿ π)
             -> (t∈Δ : τ∈π ↦ t ∈ᴱ Δ)
             -- Note that this term is stuck if τ∈π ↦ t ∉ Δ
             -- in this case we can find the term in the environment labeled with l'
             -> ⟨ Δ , deepDup (Var {π = π} τ∈π) , S ⟩ ⇝ ⟨ just (deepDupᵀ t) ∷ Δ , Var {π = τ ∷ π} {l} ⟪ hereᴿ ⟫ , S ⟩

 -- If the argument to deepDup is not a variable we introduce a new fresh variable (similarly to
 -- so that next rule DeepDup will apply.
 DeepDup' : ∀ {π τ τ'} {Δ : Env l π} {t : Term π τ} {S : Stack l τ τ'}
            -> (¬var : ¬ (IsVar t))
            -> ⟨ Δ , deepDup t , S ⟩ ⇝ ⟨ just t ∷ Δ , deepDup (Var {π = τ ∷ π} {l} ⟪ hereᴿ ⟫) , S ⟩

 New₁ : ∀ {τ τ' H} {π : Context} {Δ : Env l π} {S : Stack l _ τ'} {l⊑h : l ⊑ H} {t : Term π τ}
         -> (¬var : ¬ (IsVar t)) ->
         ⟨ Δ , new {π = π} l⊑h t , S ⟩ ⇝ ⟨ just t ∷ Δ , new l⊑h (Var {π = τ ∷ π} {l} ⟪ hereᴿ ⟫) , S ⟩

 New∙₁ : ∀ {τ τ' H} {π : Context} {Δ : Env l π} {S : Stack l _ τ'} {l⊑h : l ⊑ H} {t : Term π τ}
         -> (¬var : ¬ (IsVar t)) ->
         ⟨ Δ , new∙ {π = π} l⊑h t , S ⟩ ⇝ ⟨ just t ∷ Δ , new∙ l⊑h (Var {π = τ ∷ π} {l} ⟪ hereᴿ ⟫) , S ⟩

 Write₁ : ∀ {τ τ' H} {π : Context} {Δ : Env l π} {S : Stack l _ τ'} {t₁ : Term π (Ref H τ)} {t₂ : Term π τ} {l⊑H : l ⊑ H} ->
            ⟨ Δ , write l⊑H t₁ t₂ , S ⟩ ⇝ ⟨ (just t₂ ∷ Δ) , wken t₁ (drop refl-⊆ˡ) , write {{π = τ ∷ π}} l⊑H ⟪ hereᴿ ⟫ ∷ S ⟩

 Write∙₁ : ∀ {τ τ' H} {π : Context} {Δ : Env l π} {S : Stack l _ τ'} {t₁ : Term π (Ref H τ)} {t₂ : Term π τ} {l⊑H : l ⊑ H} ->
             ⟨ Δ , write∙ l⊑H t₁ t₂ , S ⟩ ⇝ ⟨ just t₂ ∷ Δ , wken t₁ (drop refl-⊆ˡ) , write∙ {{π = τ ∷ π}} l⊑H ⟪ hereᴿ ⟫ ∷ S ⟩

 Read₁ : ∀ {τ τ' L} {π : Context} {Δ : Env l π} {S : Stack l _ τ'} {t : Term π (Ref L τ)} {L⊑l : L ⊑ l} ->
         ⟨ Δ , read {τ = τ} L⊑l t , S ⟩ ⇝ ⟨ Δ , t , read L⊑l ∷ S ⟩

-- Semantics for stateful operations (with memory)
data _⟼_ {l ls} : ∀ {τ} -> Program l ls τ -> Program l ls τ -> Set where

  Pure : ∀ {Γ Γ' π₁ π₂ τ₁ τ₂ τ₃} {t₁ : Term π₁ τ₁} {t₂ : Term π₂ τ₂} {S₁ : Stack l τ₁ τ₃} {S₂ : Stack l τ₂ τ₃}
           {M : Memory l} {Δ₁ : Env l π₁} {Δ₂ : Env l π₂}
         -> (l∈Γ : l ↦ (M , Δ₁) ∈ᴴ Γ)
         -> (step : ⟨ Δ₁ , t₁ , S₁ ⟩ ⇝ ⟨ Δ₂ , t₂ , S₂ ⟩)
         -> (uᴴ : Γ' ≔ Γ [ l ↦ (M , Δ₂) ]ᴴ)
         -> ⟨ Γ , t₁ , S₁ ⟩ ⟼ ⟨ Γ' , t₂ , S₂ ⟩

   -- We have to write the term in the memory segment labeled as the reference (H)
   -- so that it can be correctly read by threads labeled with H or more.
   -- Note that if the current thread can also read the reference, then l ≡ H and we
   -- are still writing in the right memory.
  New : ∀ {Γ Γ' τ τ' H} {π : Context} {Δ : Env H π} {M : Memory H} {S : Stack l _ τ'} {τ∈π : τ ∈⟨ l ⟩ᴿ π} {l⊑h : l ⊑ H}
         -> (H∈Γ : H ↦ (M , Δ) ∈ᴴ Γ)
         -> (uᴴ : Γ' ≔ Γ [ H ↦ (newᴹ ∥ l⊑h , τ∈π ∥ M , Δ) ]ᴴ ) ->
         ⟨ Γ , new {π = π} l⊑h (Var τ∈π) , S ⟩ ⟼ ⟨ Γ' , Return l (Res {π = π} H #[ lengthᴹ M ]) , S ⟩

  New∙ : ∀ {Γ τ τ' H} {π : Context} {S : Stack l _ τ'} {l⊑h : l ⊑ H} {τ∈π : τ ∈⟨ l ⟩ᴿ π} ->
         ⟨ Γ , new∙ {π = π} l⊑h (Var τ∈π) , S ⟩ ⟼ ⟨ Γ , Return l (Res {π = π} H ∙) , S ⟩

  Write₂ : ∀ {Γ Γ' τ τ' n π H} {M M' : Memory H} {Δ : Env H π} {S : Stack l _ τ'} {l⊑H : l ⊑ H} {τ∈π : τ ∈⟨ l ⟩ᴿ π}
          -> (H∈Γ : H ↦ (M , Δ) ∈ᴴ Γ)
          -> (uᴹ : M' ≔ M [ n ↦ ∥ (l⊑H , τ∈π) ∥ ]ᴹ)
          -> (uᴴ : Γ' ≔ Γ [ H ↦ ( M' , Δ ) ]ᴴ) ->
         ⟨ Γ , Res {π = π} H #[ n ] , write l⊑H τ∈π ∷ S ⟩ ⟼ ⟨ Γ' , Return {π = π} l （） , S ⟩

  Writeᴰ₂ : ∀ {Γ Γ' τ τ' n π H} {M M' : Memory H} {Δ : Env H π} {S : Stack l _ τ'} {l⊑H : l ⊑ H} {τ∈π : τ ∈⟨ l ⟩ᴿ π}
          -> (H∈Γ : H ↦ (M , Δ) ∈ᴴ Γ)
          -> (uᴹ : M' ≔ M [ n ↦ ∥ (l⊑H , τ∈π) ∥ ]ᴹ)
          -> (uᴴ : Γ' ≔ Γ [ H ↦ ( M' , Δ ) ]ᴴ) ->
         ⟨ Γ , Res {π = π} H #[ n ]ᴰ , write l⊑H τ∈π ∷ S ⟩ ⟼ ⟨ Γ' , Return {π = π} l （） , S ⟩

  Write∙₂ :  ∀ {Γ τ τ' H} {π : Context} {S : Stack l _ τ'} {l⊑H : l ⊑ H} {t : Term π Addr} {τ∈π : τ ∈⟨ l ⟩ᴿ π} ->
            ⟨ Γ , Res {π = π} H t , write∙ l⊑H τ∈π ∷ S ⟩ ⟼ ⟨ Γ , Return {π = π} l （） , S ⟩

  -- If we read without duplicating it must be from the same level, otherwise we are leaking
  -- (We could write this using different L and l and from the inequalities L ⊑ l and l ⊑ L conclude the same,
  -- but I don't know if I should
  Read₂ : ∀ {Γ τ τ' n} {π : Context} {M : Memory l} {Δ : Env l π} {S : Stack l _ τ'} {τ∈π : τ ∈⟨ l ⟩ᴿ π}
         -> (l∈Γ : l ↦ (M , Δ) ∈ᴴ Γ)
         -> (n∈M : n ↦ ∥ (refl-⊑ , τ∈π) ∥ ∈ᴹ M) ->
           ⟨ Γ , Res {π = π} l #[ n ] , read refl-⊑ ∷ S ⟩ ⟼ ⟨ Γ , Return {π = π} l (Var τ∈π) , S ⟩

  -- When we read a reference from a possibly lower level we must deepDup that
  Readᴰ₂ : ∀ {Γ τ τ' n L} {π : Context} {M : Memory L} {Δ : Env L π} {S : Stack l _ τ'} {τ∈π : τ ∈⟨ L ⟩ᴿ π} {L⊑l : L ⊑ l}
         -> (L∈Γ : L ↦ (M , Δ) ∈ᴴ Γ)
         -> (n∈M : n ↦ ∥ (refl-⊑ , τ∈π) ∥ ∈ᴹ M) ->
           ⟨ Γ , Res {π = π} L #[ n ]ᴰ , read L⊑l ∷ S ⟩ ⟼ ⟨ Γ , Return {π = π} l (deepDup (Var τ∈π)) , S ⟩

  DeepDupˢ : ∀ {Γ π τ τ' L} {Δ : Env L π} {M : Memory L} {t : Term π τ}{S : Stack l τ τ'}{ τ∈π : τ ∈⟨ L ⟩ᴿ π }
             -> (L⊏l : L ⊏ l)  -- Probably we need ≢
             -> (L∈Γ : L ↦ (M , Δ) ∈ᴴ Γ)
             -> (t∈Δ : τ∈π ↦ t ∈ᴱ Δ)
             -> ⟨ Γ , deepDup (Var {π = π} τ∈π) , S ⟩ ⟼ ⟨ Γ , deepDup t , S ⟩

  Hole : ∀ {τ} -> ∙ {τ = τ} ⟼ ∙

--------------------------------------------------------------------------------

data Doneᴾ {l ls τ} : Program l ls τ -> Set where
  Done : ∀ {Γ π} {v : Term π τ} -> (isVal : Value v) -> Doneᴾ ⟨ Γ , v , [] ⟩

data Redexᴾ {l ls τ} (p : Program l ls τ) : Set where
  Step : ∀ {p'} -> p ⟼ p' -> Redexᴾ p

Stuckᴾ : ∀ {l ls τ} -> Program l ls τ -> Set
Stuckᴾ p = (¬ (Doneᴾ p)) × (¬ (Redexᴾ p))

open import Data.Empty

¬Done⇒¬Val :  ∀ {l π ls τ} {Γ : Heap ls} {t : Term π τ} -> ¬ (Doneᴾ {l} ⟨ Γ , t , [] ⟩) -> ¬ Value t
¬Done⇒¬Val x v = ⊥-elim (x (Done v))

Stateᴾ : ∀ {l ls τ} (p : Program l ls τ) -> Set
Stateᴾ p = (Doneᴾ p) × ((Redexᴾ p) × (Stuckᴾ p))
