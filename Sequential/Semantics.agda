open import Lattice

module Sequential.Semantics {- (𝓛 : Lattice) -} where

open import Types
open import Sequential.Calculus
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_] ; subst)

--------------------------------------------------------------------------------
-- DeepDup helper functions and data types

open import Data.Bool using (not)
open import Data.List using (filter)
open import Relation.Nullary.Decidable using (⌊_⌋)

-- Unguarded free variables
-- It should be a set, but there is no simple standard implementation of sets,
-- therefore I will start with a simple list and see where this takes us.
ufv : Term -> List Variable
ufv （） = []
ufv True = []
ufv False = []
ufv (Id t) = ufv t
ufv (unId t) = ufv t
ufv (Var x) = x ∷ []
ufv (Abs n t) = filter (λ m → not ⌊ n ≟ⱽ m ⌋) (ufv t)
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
-- data DeepDupHeap (l : Label) : Heap -> List ℕ -> List ℕ -> Heap -> Set where
--   done : ∀ {Γ} -> DeepDupHeap l Γ [] [] Γ
--   addNext : ∀ {Γ₁ Γ₂ Γ₃ n n' ns ns'} -> Γ₂ ≔ᴬ Γ₁ [ n' ↦ (l , deepDup n) ]
--                                      -> DeepDupHeap l Γ₂ ns ns' Γ₃
--                                      -> DeepDupHeap l Γ₁ (n ∷ ns) (n' ∷ ns') Γ₃

-- Syntatic Sugar for DeepDupHeap
-- _≔ᴰ_[_↦_] : Heap -> Heap -> List ℕ -> Label × List ℕ -> Set
-- Γ' ≔ᴰ Γ [ ns' ↦ (l , ns) ] = DeepDupHeap l Γ ns ns' Γ'

--------------------------------------------------------------------------------

-- Operational Semantics
-- Here since we use the Substs proof we implicitly rule out name clashes in substitutions.
-- Terms that do not comply with this assumption are not reducible according to this semantics,
-- however they could be after α-conversion (we simply don't want to deal with that,
-- and assume they have already been α-converted).
-- Note that stuck terms will be dealt with in the concurrent semantics.
data _⇝_ {l : Label} : State l -> State l -> Set where

 App₁ : ∀ {Γ S t₁ t₂ n} -> -- Γ' ≔ᴬ Γ [ n ↦ (l , t₂) ]
                         ⟨ Γ , App t₁ t₂ , S ⟩ ⇝ ⟨ Γ [ l , n ↦ just t₂ ] , t₁ , Var (l , n ) ∷ S ⟩

 App₂ : ∀ {Γ n m t t' S} -> Subst m (Var n) t t' -> ⟨ Γ , Abs m t , Var n ∷ S ⟩ ⇝ ⟨ Γ , t' , S ⟩
 
 Var₁ : ∀ {Γ x t S} -> (x∈Γ : x ↦ just t ∈ Γ)
                    -> (¬val : ¬ (Value t))
                    -> ⟨ Γ , Var x , S ⟩ ⇝ ⟨ Γ [ x ↦ nothing ] , t , # x ∷ S ⟩ 

 Var₁' : ∀ {Γ x v S} -> (val : Value v)
                     -> (x∈Γ : x ↦ just v ∈ Γ)
                     -> ⟨ Γ , Var x , S ⟩ ⇝ ⟨ Γ , v , S ⟩

 Var₂ : ∀ {Γ x v S} -> (val : Value v) -> ⟨ Γ , v , # x ∷ S ⟩ ⇝ ⟨ Γ [ x ↦ nothing ] , v , S ⟩

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

 -- DeepDup : ∀ {Γ₁ Γ₂ Γ₃ n n' ns' S l' t t'} -> ? -- n ↦ (l' , t) ∈ Γ₁
 --                                -> Substs t (ufv t) ns' t'
 --                                -> ?Γ₂ ≔ᴰ Γ₁ [ ns' ↦ (l , ufv t) ]
 --                                -> Γ₃ ≔ᴬ Γ₂ [ n' ↦ (l , t') ]
 --                                -> ⟨ Γ₁ , (deepDup n) , S ⟩ ⇝ ⟨ Γ₃ , Var n' , S ⟩



-- Type preservation
ty-preservation : ∀ {l τ Γ₁ Γ₂ t₁ t₂} {S₁ S₂ : Stack l} ->
                   let s₁ = ⟨ Γ₁ , t₁ , S₁ ⟩
                       s₂ = ⟨ Γ₂ , t₂ , S₂ ⟩ in ⊢ˢ s₁ ∷ τ -> s₁ ⇝ s₂ -> ⊢ˢ s₂ ∷ τ
ty-preservation s step = {!!}
