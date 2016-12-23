open import Lattice

module Sequential.Semantics (𝓛 : Lattice) where

open import Types 𝓛
open import Sequential.Calculus 𝓛
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

 Var₁' : ∀ {Γ Γ' n v S l'} -> Value v
                           -> n ↦ (l' , v) ∈ Γ
                           -> ⟨ Γ' , Var n , S ⟩ ⇝ ⟨ Γ , v , S ⟩

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
 Unlabel₂ : ∀ {Γ t S l'} -> (p : l' ⊑ l) -> ⟨ Γ , Res l t , unlabel p ∷ S ⟩ ⇝ ⟨ Γ , t , unId ∷ S ⟩

 UnId₁ : ∀ {Γ t S} -> ⟨ Γ , unId t , S ⟩ ⇝ ⟨ Γ , t , unId ∷ S ⟩ 
 UnId₂ : ∀ {Γ t S} -> ⟨ Γ , Id t , unId ∷ S ⟩ ⇝ ⟨ Γ , t , S ⟩ 

 Fork : ∀ {Γ t S h} -> (p : l ⊑ h) -> ⟨ Γ , (fork p t) , S ⟩ ⇝ ⟨ Γ , Return l t , S ⟩ 

 Hole : ∀ {Γ S} -> ⟨ Γ , ∙ , S ⟩ ⇝ ⟨ Γ , ∙ , S ⟩

 DeepDup : ∀ {Γ₁ Γ₂ Γ₃ Γ n n' ns' S l' t t'} -> n ↦ (l' , t) ∈ Γ
                                -> Substs t (ufv t) ns' t'
                                -> Γ₂ ≔ᴰ Γ₁ [ ns' ↦ (l , ufv t) ]
                                -> Γ₃ ≔ᴬ Γ₂ [ n' ↦ (l , t') ]
                                -> ⟨ Γ₁ , (deepDup n) , S ⟩ ⇝ ⟨ Γ₃ , Var n' , S ⟩
