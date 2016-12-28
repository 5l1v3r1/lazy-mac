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

-- Unguarded free variables
-- It should be a set, but there is no simple standard implementation of sets,
-- therefore I will start with a simple list and see where this takes us.
ufv : Term -> List ℕ
ufv （） = []
ufv True = []
ufv False = []
ufv (Id t) = ufv t
ufv (unId t) = ufv t
ufv (Var x) = x ∷ []
ufv (Abs n t) = filter (λ m → not ⌊ n ≟ m ⌋) (ufv t)
ufv (App t t₁) = ufv t ++ ufv t₁
ufv (If t Then t₁ Else t₂) = ufv t ++ ufv t₁ ++ ufv t₂
ufv (Return l t) = ufv t
ufv (Bind l t t₁) = ufv t ++ ufv t₁
ufv (Mac l t) = ufv t
ufv (Res l t) = ufv t
ufv (label l⊑h t) = ufv t
ufv (label∙ l⊑h t) = ufv t
ufv (unlabel l⊑h t) = ufv t
ufv (fork l⊑h t) = ufv t
ufv (deepDup x) = [] -- Unguarded
ufv ∙ = []

-- Unguareded Free Variables (we might need this as a data type)
data UFV : Term -> List ℕ -> Set where
-- ...

-- DeepDupHeap l Γ ns ns' Γ' corresponds to Γ' = Γ[ n' ↦ deepDup n | (n , n') <- zip ns ns']
data DeepDupHeap (l : Label) : Heap -> List ℕ -> List ℕ -> Heap -> Set where
  done : ∀ {Γ} -> DeepDupHeap l Γ [] [] Γ
  addNext : ∀ {Γ₁ Γ₂ Γ₃ n n' ns ns'} -> Γ₂ ≔ᴬ Γ₁ [ n' ↦ (l , deepDup n) ]
                                     -> DeepDupHeap l Γ₂ ns ns' Γ₃
                                     -> DeepDupHeap l Γ₁ (n ∷ ns) (n' ∷ ns') Γ₃

-- Syntatic Sugar for DeepDupHeap
_≔ᴰ_[_↦_] : Heap -> Heap -> List ℕ -> Label × List ℕ -> Set
Γ' ≔ᴰ Γ [ ns' ↦ (l , ns) ] = DeepDupHeap l Γ ns ns' Γ'

--------------------------------------------------------------------------------

-- Operational Semantics
-- Here since we use the Substs proof we implicitly rule out name clashes in substitutions.
-- Terms that do not comply with this assumption are not reducible according to this semantics,
-- however they could be after α-conversion (we simply don't want to deal with that,
-- and assume they have already been α-converted).
-- Note that stuck terms will be dealt with in the concurrent semantics.
data _⇝_ {l : Label} : State l -> State l -> Set where

 App₁ : ∀ {Γ Γ' S t₁ t₂ n} -> Γ' ≔ᴬ Γ [ n ↦ (l , t₂) ]
                           -> ⟨ Γ , App t₁ t₂ , S ⟩ ⇝ ⟨ Γ' , t₁ , Var n ∷ S ⟩

 App₂ : ∀ {Γ n m t t' S} -> Subst m (Var n) t t' -> ⟨ Γ , Abs m t , Var n ∷ S ⟩ ⇝ ⟨ Γ , t' , S ⟩
 
 Var₁ : ∀ {Γ Γ' n t S l'} -> ¬ (Value t)
                          -> Γ ≔ᴿ Γ' [ n ↦ (l' , t) ]
                          -> ⟨ Γ' , Var n , S ⟩ ⇝ ⟨ Γ , t , (# l n) ∷ S ⟩

 Var₁' : ∀ {Γ n v S l'} -> Value v
                           -> n ↦ (l' , v) ∈ Γ
                           -> ⟨ Γ , Var n , S ⟩ ⇝ ⟨ Γ , v , S ⟩

 Var₂ : ∀ {Γ Γ' n v S} -> Γ' ≔ᴾ Γ [ n ↦ (l , v) ]
                       -> Value v
                       -> ⟨ Γ , v , (# l n) ∷ S ⟩ ⇝ ⟨ Γ' , v , S ⟩

 If : ∀ {Γ t₁ t₂ t₃ S} -> ⟨ Γ , (If t₁ Then t₂ Else t₃) , S ⟩ ⇝ ⟨ Γ , t₁ , (Then t₂ Else t₃) ∷ S ⟩
 IfTrue : ∀ {Γ t₂ t₃ S} -> ⟨ Γ , True , (Then t₂ Else t₃) ∷ S ⟩ ⇝ ⟨ Γ , t₂ , S ⟩
 IfFalse : ∀ {Γ t₂ t₃ S} -> ⟨ Γ , False , (Then t₂ Else t₃) ∷ S ⟩ ⇝ ⟨ Γ , t₃ , S ⟩

 Return : ∀ {Γ t S} -> ⟨ Γ , Return l t , S ⟩ ⇝ ⟨ Γ , Mac l t , S ⟩
 Bind₁ : ∀ {Γ t₁ t₂ S} -> ⟨ Γ , Bind l t₁ t₂ , S ⟩ ⇝ ⟨ Γ , t₁ , (Bind l t₂ ∷ S ) ⟩
 Bind₂ : ∀ {Γ t₁ t₂ S} -> ⟨ Γ , Mac l t₁ , Bind l t₂ ∷ S ⟩ ⇝ ⟨ Γ , App t₂ t₁ , S  ⟩

 Label' : ∀ {Γ t S h} -> (p : l ⊑ h) -> ⟨ Γ , label p t , S ⟩ ⇝ ⟨ Γ , (Return l (Res h (Id t))) , S ⟩

 Unlabel₁ : ∀ {Γ t S l'} -> (p : l' ⊑ l) -> ⟨ Γ , unlabel p t , S ⟩ ⇝ ⟨ Γ , t , unlabel p ∷ S ⟩
 Unlabel₂ : ∀ {Γ t S l'} -> (p : l' ⊑ l) -> ⟨ Γ , Res l' t , unlabel p ∷ S ⟩ ⇝ ⟨ Γ , Return l (unId t) , S ⟩

 UnId₁ : ∀ {Γ t S} -> ⟨ Γ , unId t , S ⟩ ⇝ ⟨ Γ , t , unId ∷ S ⟩ 
 UnId₂ : ∀ {Γ t S} -> ⟨ Γ , Id t , unId ∷ S ⟩ ⇝ ⟨ Γ , t , S ⟩ 

 Fork : ∀ {Γ t S h} -> (p : l ⊑ h) -> ⟨ Γ , (fork p t) , S ⟩ ⇝ ⟨ Γ , Return l （） , S ⟩ 

 Hole : ∀ {Γ S} -> ⟨ Γ , ∙ , S ⟩ ⇝ ⟨ Γ , ∙ , S ⟩

 DeepDup : ∀ {Γ₁ Γ₂ Γ₃ n n' ns' S l' t t'} -> n ↦ (l' , t) ∈ Γ₁
                                -> Substs t (ufv t) ns' t'
                                -> Γ₂ ≔ᴰ Γ₁ [ ns' ↦ (l , ufv t) ]
                                -> Γ₃ ≔ᴬ Γ₂ [ n' ↦ (l , t') ]
                                -> ⟨ Γ₁ , (deepDup n) , S ⟩ ⇝ ⟨ Γ₃ , Var n' , S ⟩


add-wt : ∀ {π₁ π₂ π₃ Γ₁ Γ₂ n l t τ}
         -> π₁ ⊢ᴴ Γ₁ ∷ π₂ -> Γ₂ ≔ᴬ Γ₁ [ n ↦ l , t ]
         -> π₃ ≔ᴹ π₁ ⊔ π₂ -> π₃ ⊢ t ∷ τ
         -> ∃ (λ π₃' -> π₃' ≔ᴹ π₁ ⊔ {!!} × π₁ ⊢ᴴ Γ₂ ∷ π₃')
add-wt = {!!}

-- wken-

-- 1) Define ⊂ for mapping
-- 2) Define wken for Heap, Stack and Terms
-- 3)

--wt-subst : Subst n' (Var n) t t₂ -> 

wt-lookup : ∀ {n l t Γ τ π₁ π₂ π₃} -> π₁ ⊢ᴴ Γ ∷ π₂
                                   -> π₃ ≔ᴹ π₁ ⊔ π₂
                                   -> n ↦ τ ∈ π₃
                                   -> n ↦ (l , t) ∈ Γ
                                   -> π₃ ⊢ t ∷ τ
wt-lookup (Cons wt-Γ ∅₁ wt-t a-π a-Γ) ∅₁ here here = {!!}
wt-lookup (Cons wt-Γ ∅₂ wt-t a-π a-Γ) ∅₁ here here = {!!}
wt-lookup (Cons wt-Γ π₁-⊔-π₂ wt-t a-π a-Γ) ∅₂ here here = {!!}
wt-lookup (Cons wt-Γ π₁-⊔-π₂ wt-t a-π a-Γ) (x ∷ m) here here = {!!}
wt-lookup wt-Γ m wt-n (next n∈Γ) = {!!}

-- Type preservation
ty-preservation : ∀ {l π τ Γ₁ Γ₂ t₁ t₂} {S₁ S₂ : Stack l} ->
                   let s₁ = ⟨ Γ₁ , t₁ , S₁ ⟩
                       s₂ = ⟨ Γ₂ , t₂ , S₂ ⟩ in π ⊢ˢ s₁ ∷ τ -> s₁ ⇝ s₂ -> π ⊢ˢ s₂ ∷ τ
ty-preservation WT[ π₁-⊔-π₂ ]⟨ wt-Γ , App wt-t wt-t₁ , wt-S ⟩ (App₁ x) = WT[ {!!} ]⟨ {!!} , wt-t , (Var {!!} ∷ wt-S) ⟩
ty-preservation WT[ π₁-⊔-π₂ ]⟨ wt-Γ , Abs x wt-t , Var wt-n ∷ wt-S ⟩ (App₂ x₁) = WT[ π₁-⊔-π₂ ]⟨ wt-Γ , {!!} , wt-S ⟩
ty-preservation WT[ π₁-⊔-π₂ ]⟨ wt-Γ , Var x , wt-S ⟩ (Var₁ x₁ x₂) = WT[ {!!} ]⟨ {!!} , {!!} , (# _ _ ∷ wt-S) ⟩
ty-preservation WT[ π₁-⊔-π₂ ]⟨ wt-Γ , Var x , wt-S ⟩ (Var₁' x₁ x₂) = WT[ π₁-⊔-π₂ ]⟨ wt-Γ , wt-lookup wt-Γ π₁-⊔-π₂ x x₂ , wt-S ⟩
ty-preservation wt (Var₂ x x₁) = {!!}
ty-preservation WT[ π₁-⊔-π₂ ]⟨ wt-Γ , If wt-t Then wt-t₁ Else wt-t₂ , wt-S ⟩ If = WT[ π₁-⊔-π₂ ]⟨ wt-Γ , wt-t , (Then wt-t₁ Else wt-t₂) ∷ wt-S ⟩
ty-preservation WT[ π₁-⊔-π₂ ]⟨ wt-Γ , True , (Then wt-t₂ Else wt-t₃) ∷ wt-S ⟩ IfTrue = WT[ π₁-⊔-π₂ ]⟨ wt-Γ , wt-t₂ , wt-S ⟩
ty-preservation WT[ π₁-⊔-π₂ ]⟨ wt-Γ , False , (Then wt-t₂ Else wt-t₃) ∷ wt-S ⟩ IfFalse = WT[ π₁-⊔-π₂ ]⟨ wt-Γ , wt-t₃ , wt-S ⟩
ty-preservation WT[ π₁-⊔-π₂ ]⟨ wt-Γ , Return wt-t , wt-S ⟩ Return = WT[ π₁-⊔-π₂ ]⟨ wt-Γ , Mac wt-t , wt-S ⟩
ty-preservation WT[ π₁-⊔-π₂ ]⟨ wt-Γ , Bind wt-t wt-t₁ , wt-S ⟩ Bind₁ = WT[ π₁-⊔-π₂ ]⟨ wt-Γ , wt-t , Bind wt-t₁ ∷ wt-S ⟩
ty-preservation WT[ π₁-⊔-π₂ ]⟨ wt-Γ , Mac wt-t , Bind wt-t₂ ∷ wt-S ⟩ Bind₂ = WT[ π₁-⊔-π₂ ]⟨ wt-Γ , App wt-t₂ wt-t , wt-S ⟩
ty-preservation WT[ π₁-⊔-π₂ ]⟨ wt-Γ , label wt-t , wt-S ⟩ (Label' p) = WT[ π₁-⊔-π₂ ]⟨ wt-Γ , Return (Res (Id wt-t)) , wt-S ⟩
ty-preservation WT[ π₁-⊔-π₂ ]⟨ wt-Γ , unlabel wt-t , wt-S ⟩ (Unlabel₁ p) = WT[ π₁-⊔-π₂ ]⟨ wt-Γ , wt-t , unlabel p ∷ wt-S ⟩
ty-preservation WT[ π₁-⊔-π₂ ]⟨ wt-Γ , Res wt-t , unlabel p ∷ wt-S ⟩ (Unlabel₂ .p) = WT[ π₁-⊔-π₂ ]⟨ wt-Γ , Return (unId wt-t) , wt-S ⟩
ty-preservation WT[ π₁-⊔-π₂ ]⟨ wt-Γ , unId wt-t , wt-S ⟩ UnId₁ = WT[ π₁-⊔-π₂ ]⟨ wt-Γ , wt-t , unId ∷ wt-S ⟩
ty-preservation WT[ π₁-⊔-π₂ ]⟨ wt-Γ , Id wt-t , unId ∷ wt-S ⟩ UnId₂ = WT[ π₁-⊔-π₂ ]⟨ wt-Γ , wt-t , wt-S ⟩
ty-preservation WT[ π₁-⊔-π₂ ]⟨ wt-Γ , fork wt-t , wt-S ⟩ (Fork p) = WT[ π₁-⊔-π₂ ]⟨ wt-Γ , Return （） , wt-S ⟩
ty-preservation WT[ π₁-⊔-π₂ ]⟨ wt-Γ , ∙ , wt-S ⟩ Hole = WT[ π₁-⊔-π₂ ]⟨ wt-Γ , ∙ , wt-S ⟩
ty-preservation WT[ π₁-⊔-π₂ ]⟨ wt-Γ , deepDup x , wt-S ⟩ (DeepDup x₁ x₂ x₃ x₄) = {!!}
