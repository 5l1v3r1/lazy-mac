import Lattice as L

module Sequential.Semantics (𝓛 : L.Lattice) where

open import Types 𝓛
open import Sequential.Calculus 𝓛

open import Data.Maybe
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_] ; subst)

--------------------------------------------------------------------------------

-- The invariant that we maintain is that in a step of thread l
-- we introduce only variables at level l.
-- Variables from lower level should occur only inside a deepDup.
data _⇝_ {l : Label} : ∀ {τ} -> State l τ -> State l τ -> Set where

 App₁ : ∀ {τ₁ τ₂ τ₃ π} {Δ : Heap l π} {t₁ : Term π (τ₁ => τ₂)} {t₂ : Term π τ₁} {S : Stack l π τ₂ τ₃} ->
          ⟨ Δ , App t₁ t₂ , S ⟩ ⇝ ⟨ just t₂ ∷ Δ ,  wken t₁ (drop refl-⊆) , (Var ⟪ hereᴿ ⟫) ∷ wkenˢ S (drop refl-⊆) ⟩

 App₂ : ∀ {β α τ'} {π : Context} {Δ : Heap l π} {S : Stack l π β τ'} {t : Term (α ∷ π) β}
            -> (α∈π : α ∈⟨ l ⟩ᴿ π) ->
          ⟨ Δ , Abs t , Var α∈π ∷ S ⟩ ⇝ ⟨ Δ , subst (Var α∈π) t , S ⟩

 Var₁ : ∀ {τ τ'} {π : Context} {Δ Δ' : Heap l π}  {S : Stack l π τ τ'} {t : Term π τ}
        -> (τ∈π : τ ∈⟨ l ⟩ᴿ π)
        -> (t∈Δ : τ∈π ↦ t ∈ᴴ Δ)
        -> (¬val :  ¬ (Value t))
        -> (rᴴ : Δ' ≔ Δ [ τ∈π ↛ t ]ᴴ)
        -> ⟨ Δ , Var {π = π} τ∈π , S ⟩ ⇝ ⟨ Δ'  , t , (# τ∈π) ∷ S ⟩

 Var₁' : ∀ {τ τ'} {π : Context} {Δ : Heap l π} {S : Stack l π τ τ'} {v : Term π τ}
         -> (τ∈π : τ ∈⟨ l ⟩ᴿ π)
         -> (v∈Δ : τ∈π ↦ v ∈ᴴ Δ)
         -> (val : Value v)
         -> ⟨ Δ , Var {π = π} τ∈π , S ⟩ ⇝ ⟨ Δ , v , S ⟩

 Var₂ : ∀ {τ τ'} {π : Context} {Δ Δ' : Heap l π} {S : Stack l π τ τ'} {v : Term π τ}
        -> (τ∈π : τ ∈⟨ l ⟩ᴿ π)
        -> (val : Value v)
        -> (uᴴ : Δ' ≔ Δ [ τ∈π ↦ v ]ᴴ)
        -> ⟨ Δ , v , (# τ∈π) ∷ S ⟩ ⇝ ⟨  Δ' , v , S ⟩

 If : ∀ {π τ τ'} {Δ : Heap l π} {S : Stack l π τ τ'} {t₁ : Term π Bool} {t₂ t₃ : Term π τ} ->
        ⟨ Δ , (If t₁ Then t₂ Else t₃) , S ⟩ ⇝ ⟨ Δ , t₁ , (Then t₂ Else t₃) ∷ S ⟩

 IfTrue : ∀ {π τ τ'} {Δ : Heap l π} {S : Stack l π τ τ'} {t₂ t₃ : Term π τ} ->
            ⟨ Δ , True {π = π}, (Then t₂ Else t₃) ∷ S ⟩ ⇝ ⟨ Δ , t₂ , S ⟩

 IfFalse : ∀ {π τ τ'} {Δ : Heap l π} {S : Stack l π τ τ'} {t₂ t₃ : Term π τ} ->
             ⟨ Δ , False {π = π}, (Then t₂ Else t₃) ∷ S ⟩ ⇝ ⟨ Δ , t₂ , S ⟩

 Return : ∀ {π τ τ'} {Δ : Heap l π} {S : Stack l π _ τ'} {t : Term π τ} ->
            ⟨ Δ , Return l t , S ⟩ ⇝ ⟨ Δ , Mac l t , S ⟩

 Bind₁ : ∀ {π α β τ'} {Δ : Heap l π} {S : Stack l π _ τ'} {t₁ : Term π (Mac l α)} {t₂ : Term π (α => Mac l β)} ->
           ⟨ Δ , t₁ >>= t₂ , S ⟩ ⇝ ⟨ Δ , t₁ , (Bind t₂ ∷ S ) ⟩

 Bind₂ : ∀ {π α β τ'} {Δ : Heap l π} {S : Stack l π _ τ'} {t₁ : Term π α} {t₂ : Term π (α => (Mac l β))} ->
           ⟨ Δ , Mac l t₁ , Bind t₂ ∷ S ⟩ ⇝ ⟨ Δ , App t₂ t₁ , S ⟩

 Label' : ∀ {π h τ τ'} {Δ : Heap l π} {S : Stack l π _ τ'} {t : Term π τ} -> (p : l ⊑ h) ->
            ⟨ Δ , label p t , S ⟩ ⇝ ⟨ Δ , (Return l (Res h (Id t))) , S ⟩

 Label'∙ : ∀ {π h τ τ'} {Δ : Heap l π} {S : Stack l π _ τ'} {t : Term π τ} -> (p : l ⊑ h) ->
            ⟨ Δ , label∙ p t , S ⟩ ⇝ ⟨ Δ , (Return l (Res {π = π} h ∙)) , S ⟩

 Unlabel₁ : ∀ {π τ τ' l'} {Δ : Heap l π} {S : Stack l π _ τ'} {t : Term π (Labeled l' τ)} -> (p : l' ⊑ l) ->
              ⟨ Δ , unlabel p t , S ⟩ ⇝ ⟨ Δ , t , unlabel p ∷ S ⟩

 Unlabel₂ : ∀ {π τ τ' l'} {Δ : Heap l π} {S : Stack l π _ τ'} {t : Term π (Id τ)} -> (p : l' ⊑ l) ->
              ⟨ Δ , Res l' t , unlabel p ∷ S ⟩ ⇝ ⟨ Δ , Return l (unId t) , S ⟩

 UnId₁ : ∀ {π τ τ'} {Δ : Heap l π} {S : Stack l π τ τ'} {t : Term π (Id τ)} ->
           ⟨ Δ , unId t , S ⟩ ⇝ ⟨ Δ , t , unId ∷ S ⟩

 UnId₂ : ∀ {π τ τ'} {Δ : Heap l π} {S : Stack l π τ τ'} {t : Term π τ} ->
           ⟨ Δ , Id t , unId ∷ S ⟩ ⇝ ⟨ Δ , t , S ⟩

 Hole₁ : ∀ {τ} -> ∙ {τ = τ} ⇝ ∙

 Hole₂ : ∀ {τ} {π} -> ⟨ ∙ {{π}} , ∙ {{τ}} , ∙ ⟩ ⇝ ⟨ ∙ {{π}} , ∙ , ∙ ⟩  -- TODO remove?

 New₁ : ∀ {τ τ' H} {π : Context} {Δ : Heap l π} {S : Stack l π _ τ'} {l⊑h : l ⊑ H} {t : Term π τ}
         -> (¬var : ¬ (IsVar t)) ->
         ⟨ Δ , new {π = π} l⊑h t , S ⟩ ⇝ ⟨ just t ∷ Δ , new l⊑h (Var {π = τ ∷ π} {l} ⟪ hereᴿ ⟫) , wkenˢ S (drop refl-⊆) ⟩

 New∙₁ : ∀ {τ τ' H} {π : Context} {Δ : Heap l π} {S : Stack l π _ τ'} {l⊑h : l ⊑ H} {t : Term π τ}
         -> (¬var : ¬ (IsVar t)) ->
         ⟨ Δ , new∙ {π = π} l⊑h t , S ⟩ ⇝ ⟨ just t ∷ Δ , new∙ l⊑h (Var {π = τ ∷ π} {l} ⟪ hereᴿ ⟫) , wkenˢ S (drop refl-⊆) ⟩

 Write₁ : ∀ {τ τ' H} {π : Context} {Δ : Heap l π} {S : Stack l π _ τ'} {t₁ : Term π (Ref H τ)} {t₂ : Term π τ} {l⊑H : l ⊑ H} ->
            ⟨ Δ , write l⊑H t₁ t₂ , S ⟩ ⇝ ⟨ (just t₂ ∷ Δ) , wken t₁ (drop refl-⊆) , write l⊑H ⟪ hereᴿ ⟫ ∷ wkenˢ S (drop refl-⊆) ⟩

 Write∙₁ : ∀ {τ τ' H} {π : Context} {Δ : Heap l π} {S : Stack l π _ τ'} {t₁ : Term π (Ref H τ)} {t₂ : Term π τ} {l⊑H : l ⊑ H} ->
             ⟨ Δ , write∙ l⊑H t₁ t₂ , S ⟩ ⇝ ⟨ just t₂ ∷ Δ , wken t₁ (drop refl-⊆) , write∙ {π = τ ∷ π} l⊑H ⟪ hereᴿ ⟫ ∷ wkenˢ S (drop refl-⊆) ⟩

 Read₁ : ∀ {τ τ' L} {π : Context} {Δ : Heap l π} {S : Stack l π _ τ'} {t : Term π (Ref L τ)} {L⊑l : L ⊑ l} ->
         ⟨ Δ , read {τ = τ} L⊑l t , S ⟩ ⇝ ⟨ Δ , t , read L⊑l ∷ S ⟩

-- Semantics for stateful operations (with memory)
data _⟼_ {l ls} : ∀ {τ} -> Program l ls τ -> Program l ls τ -> Set where

  Pure : ∀ {Ms Γ Γ' π₁ π₂ τ₁ τ₂ τ₃} {t₁ : Term π₁ τ₁} {t₂ : Term π₂ τ₂}
           {S₁ : Stack l π₁ τ₁ τ₃} {S₂ : Stack l π₂ τ₂ τ₃} {Δ₁ : Heap l π₁} {Δ₂ : Heap l π₂}
         -> (l∈Γ : l ↦ ⟨ Δ₁ ⟩ ∈ᴱ Γ)
         -> (step : ⟨ Δ₁ , t₁ , S₁ ⟩ ⇝ ⟨ Δ₂ , t₂ , S₂ ⟩)
         -> (uᴹ : Γ' ≔ Γ [ l ↦  ⟨ Δ₂ ⟩ ]ᴱ)
         -> ⟨ Ms , Γ , ⟨ t₁ , S₁ ⟩ ⟩ ⟼ ⟨ Ms , Γ' , ⟨ t₂ , S₂ ⟩ ⟩

   -- We have to write the term in the memory segment labeled as the reference (H)
   -- so that it can be correctly read by threads labeled with H or more.
   -- Note that if the current thread can also read the reference, then l ≡ H and we
   -- are still writing in the right memory.
  New : ∀ {Ms Ms' Γ τ τ' H} {π : Context} {M : Memory H} {S : Stack l π _ τ'} {τ∈π : τ ∈⟨ l ⟩ᴿ π} {l⊑H : l ⊑ H}
         -> (H∈Ms : H ↦  M ∈ˢ Ms)
         -> (uᴹ : Ms' ≔ Ms [ H ↦ newᴹ ∥ l⊑H , τ∈π ∥ M ]ˢ ) ->
         ⟨ Ms , Γ , ⟨ new {π = π} l⊑H (Var τ∈π) , S ⟩ ⟩ ⟼ ⟨ Ms' , Γ , ⟨ Return l (Res {π = π} H #[ lengthᴹ M ]) , S ⟩ ⟩

  New∙ : ∀ {Ms Γ τ τ' H} {π : Context} {S : Stack l π _ τ'} {l⊑H : l ⊑ H} {τ∈π : τ ∈⟨ l ⟩ᴿ π} ->
         ⟨ Ms , Γ , ⟨ new∙ l⊑H (Var τ∈π) , S ⟩ ⟩ ⟼ ⟨ Ms , Γ , ⟨ Return l (Res {π = π} H ∙) , S ⟩ ⟩

  Write₂ : ∀ {Ms Ms' Γ τ τ' n π H} {M M' : Memory H} {S : Stack l π _ τ'} {l⊑H : l ⊑ H} {τ∈π : τ ∈⟨ l ⟩ᴿ π}
          -> (H∈Ms : H ↦ M  ∈ˢ Ms)
          -> (uᴹ : M' ≔ M [ n ↦ ∥ l⊑H , τ∈π ∥ ]ᴹ)
          -> (uˢ : Ms' ≔ Ms [ H ↦ M' ]ˢ) ->
         ⟨ Ms , Γ , ⟨ Res {π = π} H #[ n ] , write l⊑H τ∈π ∷ S ⟩ ⟩ ⟼ ⟨ Ms' , Γ , ⟨ Return {π = π} l （） , S ⟩ ⟩

  Writeᴰ₂ : ∀ {Ms Ms' Γ τ τ' n π H} {M M' : Memory H} {S : Stack l π _ τ'} {l⊑H : l ⊑ H} {τ∈π : τ ∈⟨ l ⟩ᴿ π}
          -> (H∈Ms : H ↦ M  ∈ˢ Ms)
          -> (uᴹ : M' ≔ M [ n ↦ ∥ l⊑H , τ∈π ∥ ]ᴹ)
          -> (uˢ : Ms' ≔ Ms [ H ↦ M' ]ˢ) ->
         ⟨ Ms , Γ , ⟨ Res {π = π} H #[ n ]ᴰ , write l⊑H τ∈π ∷ S ⟩ ⟩ ⟼ ⟨ Ms' , Γ , ⟨ Return {π = π} l （） , S ⟩ ⟩

  Write∙₂ :  ∀ {Ms Γ τ τ' H} {π : Context} {S : Stack l π _ τ'} {l⊑H : l ⊑ H} {t : Term π (Addr τ)} {τ∈π : τ ∈⟨ l ⟩ᴿ π} ->
            ⟨ Ms , Γ , ⟨ Res {π = π} H t , write∙ l⊑H τ∈π ∷ S ⟩ ⟩ ⟼ ⟨ Ms , Γ , ⟨ Return {π = π} l （） , S ⟩ ⟩

  -- If we read without duplicating it must be from the same level, otherwise we are leaking
  -- (We could write this using different L and l and from the inequalities L ⊑ l and l ⊑ L conclude the same,
  -- but I don't know if I should
  Read₂ : ∀ {Ms Γ τ τ' n} {π : Context} {M : Memory l} {S : Stack l π _ τ'} {τ∈π : τ ∈⟨ l ⟩ᴿ π}
         -> (l∈Γ : l ↦ M ∈ˢ Ms)
         -> (n∈M : n ↦ ∥ refl-⊑ , τ∈π ∥ ∈ᴹ M) ->
           ⟨ Ms , Γ , ⟨ Res {π = π} l #[ n ] , read refl-⊑ ∷ S ⟩ ⟩ ⟼ ⟨ Ms , Γ , ⟨ Return {π = π} l (Var τ∈π) , S ⟩ ⟩

  -- When we read a reference from a possibly lower level we must deepDup that
  Readᴰ₂ : ∀ {Ms Γ τ τ' n L} {π : Context} {M : Memory L} {S : Stack l π _ τ'} {τ∈π : τ ∈⟨ L ⟩ᴿ π} {L⊑l : L ⊑ l}
         -> (L∈Ms : L ↦ M ∈ˢ Ms)
         -> (n∈M : n ↦ ∥ refl-⊑ , τ∈π ∥ ∈ᴹ M) ->
           ⟨ Ms , Γ , ⟨ Res {π = π} L #[ n ]ᴰ , read L⊑l ∷ S ⟩ ⟩ ⟼ ⟨ Ms , Γ , ⟨ Return {π = π} l (deepDup (Var τ∈π)) , S ⟩ ⟩


  -- If the argument to deepDup is not a variable we introduce a new fresh variable (similarly to
  -- so that next rule DeepDup will apply.
  DeepDup₁ : ∀ {Ms Γ Γ' π τ τ'} {Δ : Heap l π} {t : Term π τ} {S : Stack l π τ τ'}
            -> (¬var : ¬ (IsVar t))
            -> (l∈Γ : l ↦ ⟨ Δ ⟩ ∈ᴱ Γ)
             -> (uᴱ : Γ' ≔ Γ [ l ↦  ⟨ just t ∷ Δ ⟩ ]ᴱ)
            -> ⟨ Ms , Γ , ⟨ deepDup t , S ⟩ ⟩ ⟼ ⟨ Ms , Γ' , ⟨ deepDup (Var {l = l} ⟪ hereᴿ ⟫) , wkenˢ S (drop refl-⊆) ⟩ ⟩

  -- deepDupᵀ t takes care of replacing unguarded free variables with deepDup.
  -- Note that deepDupᵀ (deepDup t) = deepDup t, so also in case of
  -- nested deepDup (e.g. deepDup (deepDup t)) we make progress.
  DeepDup₂ : ∀ {Ms Γ Γ' π L τ τ'} {Δᴸ : Heap L π} {Δˡ : Heap l π} {t : Term π τ}  {S : Stack l π τ τ'} {L⊑l : L ⊑ l}
             -- We need the constraint L ⊑ l when showing Stuck (ε t) => Stuck t (lemma sim⟼)
             -> (τ∈π : τ ∈⟨ L ⟩ᴿ π)
             -> (L∈Γ : L ↦ ⟨ Δᴸ ⟩ ∈ᴱ Γ)
             -> (t∈Δ : τ∈π ↦ t ∈ᴴ Δᴸ)
             -> (l∈Γ : l ↦ ⟨ Δˡ ⟩ ∈ᴱ Γ)
             -> (uᴱ : Γ' ≔ Γ [ l ↦  ⟨ just (deepDupᵀ t) ∷ Δˡ ⟩ ]ᴱ)
             -> ⟨ Ms , Γ , ⟨ deepDup (Var {π = π} τ∈π) , S ⟩ ⟩ ⟼ ⟨ Ms , Γ' , ⟨ Var {π = τ ∷ π} {l} ⟪ hereᴿ ⟫ , wkenˢ S (drop refl-⊆) ⟩ ⟩

  Hole : ∀ {τ} {Ms : Memories ls} {Γ : Heaps ls} -> ⟨ Ms , Γ , ∙ {τ = τ} ⟩ ⟼ ⟨ Ms , Γ , ∙ ⟩

--------------------------------------------------------------------------------

data IsForkTS {l τ} : TS∙ l τ -> Set where
  isForkTS : ∀ {π τ' S} {t : Term π τ'} -> IsFork t -> IsForkTS ⟨ t , S ⟩

¬IsForkTs¬IsFork : ∀ {π l τ₁ τ₂} {t : Term π τ₁} {S : Stack l _ _ τ₂} -> ¬ IsForkTS ⟨ t , S ⟩ -> ¬ IsFork t
¬IsForkTs¬IsFork ¬fork isF = ¬fork (isForkTS isF)

data IsDoneTS {l τ} : TS∙ l τ -> Set where
  isDoneTS : ∀ {π} {v : Term π τ} -> (isVal : Value v) -> IsDoneTS ⟨ v , [] ⟩

Doneᴾ : ∀ {l ls τ} -> Program l ls τ -> Set
Doneᴾ p = IsDoneTS (TS p)

data Redexᴾ {l ls τ} (p : Program l ls τ) : Set where
  Step : ∀ {p'} -> p ⟼ p' -> Redexᴾ p

open import Data.Product using (proj₁ ; proj₂ ; _×_)
open import Data.Empty

Stuckᴾ : ∀ {l ls τ} -> Program l ls τ -> Set
Stuckᴾ p = (¬ Doneᴾ p) × (¬ (Redexᴾ p)) × ¬ IsForkTS (TS p)

-- ¬Done⇒¬Val :  ∀ {l π ls τ Ms} {Γ : Heaps ls} {t : Term π τ} -> ¬ (Doneᴾ {l} ⟨ Ms , Γ , t , [] ⟩) -> ¬ Value t
-- ¬Done⇒¬Val x v = ⊥-elim (x (Done v))

Redex-¬IsForkTS : ∀ {l ls τ} {p : Program l ls τ} -> Redexᴾ p -> ¬ IsForkTS (TS p)
Redex-¬IsForkTS (Step (Pure _ (Var₂ a () c) _)) (isForkTS (Fork p t))
Redex-¬IsForkTS (Step (Pure _ (Var₂ a () c) _)) (isForkTS (Fork∙ p t))

Forkᴾ : ∀ {l ls τ} -> Program l ls τ -> Set
Forkᴾ p = IsForkTS (TS p)

data Stateᴾ {l ls τ} (p : Program l ls τ) : Set where
  isD :  Doneᴾ p -> Stateᴾ p
  isR : Redexᴾ p -> Stateᴾ p
  isS : Stuckᴾ p -> Stateᴾ p
  isF : Forkᴾ p -> Stateᴾ p

--------------------------------------------------------------------------------
-- Lemmas

⊥-stuckSteps : ∀ {l ls τ} {p₁ : Program l ls τ } -> Stuckᴾ p₁ -> ¬ (Redexᴾ p₁)
⊥-stuckSteps x y = proj₁ (proj₂ x) y

⊥-stuckForks : ∀ {l ls π τ₁ τ₂} {Ms : Memories ls} {Γ : Heaps ls} {t : Term π τ₁} {S : Stack l _ _ τ₂} -> Stuckᴾ ⟨ Ms , Γ , ⟨ t , S ⟩ ⟩ -> ¬ (IsFork t)
⊥-stuckForks stuck x = proj₂ (proj₂ stuck) (isForkTS x)

⊥-doneSteps : ∀ {l ls τ} {p₁ : Program l ls τ} -> Doneᴾ p₁ -> ¬ (Redexᴾ p₁)
⊥-doneSteps (isDoneTS （）) (Step (Pure l∈Γ () uᴴ))
⊥-doneSteps (isDoneTS True) (Step (Pure l∈Γ () uᴴ))
⊥-doneSteps (isDoneTS False) (Step (Pure l∈Γ () uᴴ))
⊥-doneSteps (isDoneTS (Abs t)) (Step (Pure l∈Γ () uᴴ))
⊥-doneSteps (isDoneTS (Id t)) (Step (Pure l∈Γ () uᴴ))
⊥-doneSteps (isDoneTS (Mac t)) (Step (Pure l∈Γ () uᴴ))
⊥-doneSteps (isDoneTS (Res t)) (Step (Pure l∈Γ () uᴴ))
⊥-doneSteps (isDoneTS #[ n ]) (Step (Pure l∈Γ () uᴴ))
⊥-doneSteps (isDoneTS #[ n ]ᴰ) (Step (Pure l∈Γ () uᴴ))

⊥-stuckDone : ∀ {l ls τ} {p : Program l ls τ} -> Stuckᴾ p -> ¬ (Doneᴾ p)
⊥-stuckDone stuck don = proj₁ stuck don

⊥-doneForks : ∀ {l ls π τ₁ τ₂} {Ms : Memories ls} {Γ : Heaps ls} {t : Term π τ₁} {S : Stack l _ _ τ₂} -> Doneᴾ ⟨ Ms , Γ , ⟨ t , S ⟩ ⟩ -> ¬ (IsFork t)
⊥-doneForks (isDoneTS ()) (Fork p t)
⊥-doneForks (isDoneTS ()) (Fork∙ p t)

--------------------------------------------------------------------------------

step-⊆ : ∀ {l τ τ₁ τ₂ π₁ π₂} {t₁ : Term π₁ τ₁} {t₂ : Term π₂ τ₂}
           {S₁ : Stack l π₁ τ₁ τ} {S₂ : Stack l π₂ τ₂ τ} {Δ₁ : Heap l π₁} {Δ₂ : Heap l π₂}  ->
           ⟨ Δ₁ , t₁ , S₁ ⟩ ⇝ ⟨ Δ₂ , t₂ , S₂ ⟩ -> π₁ ⊆ π₂
step-⊆ App₁ = drop refl-⊆
step-⊆ (App₂ α∈π) = refl-⊆
step-⊆ (Var₁ τ∈π t∈Δ ¬val rᴴ) = refl-⊆
step-⊆ (Var₁' τ∈π v∈Δ val) = refl-⊆
step-⊆ (Var₂ τ∈π val uᴴ) = refl-⊆
step-⊆ If = refl-⊆
step-⊆ IfTrue = refl-⊆
step-⊆ IfFalse = refl-⊆
step-⊆ Return = refl-⊆
step-⊆ Bind₁ = refl-⊆
step-⊆ Bind₂ = refl-⊆
step-⊆ (Label' p) = refl-⊆
step-⊆ (Label'∙ p) = refl-⊆
step-⊆ (Unlabel₁ p) = refl-⊆
step-⊆ (Unlabel₂ p) = refl-⊆
step-⊆ UnId₁ = refl-⊆
step-⊆ UnId₂ = refl-⊆
step-⊆ Hole₂ = refl-⊆
step-⊆ (New₁ ¬var) = drop refl-⊆
step-⊆ (New∙₁ ¬var) = drop refl-⊆
step-⊆ Write₁ = drop refl-⊆
step-⊆ Write∙₁ = drop refl-⊆
step-⊆ Read₁ = refl-⊆

stepᴾ-⊆ : ∀ {l ls τ τ₁ τ₂ π₁ π₂ Ms₁ Ms₂} {t₁ : Term π₁ τ₁} {t₂ : Term π₂ τ₂}
           {S₁ : Stack l π₁ τ₁ τ} {S₂ : Stack l π₂ τ₂ τ} {Γ₁ Γ₂ : Heaps ls} ->
           ⟨ Ms₁ , Γ₁ , ⟨ t₁ , S₁ ⟩ ⟩ ⟼ ⟨ Ms₂ , Γ₂ , ⟨ t₂ , S₂ ⟩ ⟩ -> π₁ ⊆ π₂
stepᴾ-⊆ (Pure l∈Γ step uᴴ) = step-⊆ step
stepᴾ-⊆ (New H∈Γ uᴴ) = refl-⊆
stepᴾ-⊆ New∙ = refl-⊆
stepᴾ-⊆ (Write₂ H∈Γ uᴹ uᴴ) = refl-⊆
stepᴾ-⊆ (Writeᴰ₂ H∈Γ uᴹ uᴴ) = refl-⊆
stepᴾ-⊆ Write∙₂ = refl-⊆
stepᴾ-⊆ (Read₂ l∈Γ n∈M) = refl-⊆
stepᴾ-⊆ (Readᴰ₂ L∈Γ n∈M) = refl-⊆
stepᴾ-⊆ (DeepDup₁ ¬var l∈Γ uᴱ) = drop refl-⊆
stepᴾ-⊆ (DeepDup₂ τ∈π L∈Γ t∈Δ l∈Γ uᴱ) = drop refl-⊆
