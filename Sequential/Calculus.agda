open import Lattice

module Sequential.Calculus (𝓛 : Lattice) where

open import Types 𝓛
open import Relation.Binary.PropositionalEquality hiding ([_] ; subst)
open import Data.List.All
open import Data.Nat using (ℕ ; zero ; suc) public
import Data.List as L

mutual 

  -- The basic Term Δ τ is a term that has type τ in the context Δ
  -- Δ is extended uniquely by lambda abstractions, which add the type of their argument to it.
  data Term (Δ : Context) : Ty -> Set where
    （） : Term Δ （）

    True : Term Δ Bool 
    False : Term Δ Bool

    Id : ∀ {τ} -> Term Δ τ -> Term Δ (Id τ)
    unId : ∀ {τ} -> Term Δ (Id τ) -> Term Δ τ

    Var : ∀ {τ} -> τ ∈ Δ -> Term Δ τ
    Abs : ∀ {α β} -> Term (α ∷ Δ) β -> Term Δ (α => β)
    App : ∀ {α β} -> Term Δ (α => β) -> Term Δ α -> Term Δ β

    If_Then_Else_ : ∀ {α} -> Term Δ Bool -> Term Δ α -> Term Δ α -> Term Δ α

    Return : ∀ {l} {α} -> Term Δ α -> Term Δ (Mac l α)
    _>>=_ : ∀ {l} {α β} -> Term Δ (Mac l α) -> Term Δ (α => Mac l β) -> Term Δ (Mac l β)

    Mac : ∀ {l α} -> Term Δ α -> Term Δ (Mac l α)

    Res : ∀ {l α} -> Term Δ α -> Term Δ (Res l α)

    label : ∀ {l h α} -> l ⊑ h -> Term Δ α -> Term Δ (Mac l (Labeled h α))
    label∙ : ∀ {l h α} -> l ⊑ h -> Term Δ α -> Term Δ (Mac l (Labeled h α))

    unlabel : ∀ {l h α} -> l ⊑ h -> Term Δ (Labeled l α) -> Term Δ (Mac h α)

    -- read : ∀ {α l h} -> l ⊑ h -> Term Δ (Ref l α) -> Term Δ (Mac h α)
    -- write : ∀ {α l h} -> l ⊑ h -> Term Δ (Ref h α) -> Term Δ α -> Term Δ (Mac l （）)
    -- new : ∀ {α l h} -> l ⊑ h -> Term Δ α -> Term Δ (Mac l (Ref h α))

    -- Concurrency
    fork : ∀ {l h} -> l ⊑ h -> Term Δ (Mac h  （）) -> Term Δ (Mac l  （）)

    -- Represent sensitive information that has been erased.
    ∙ : ∀ {{τ}} -> Term Δ τ

  -- A closed term is a term typable in the empty context, i.e. it does not contain free variables.
  CTerm : Ty -> Set
  CTerm τ = Term [] τ

  data Status : Set where
    F : Status -- Full memory cell
    E : Status -- Empty memory cell

  -- A memory cell of a certain type
  data Cell (τ : Ty) : Status -> Set where
    ⊞ : Cell τ E
    ⟦_⟧ : CTerm τ -> Cell τ F

  -- A memory is a list of closed terms.
  -- The label l represents the sensitivity level of the terms contained in the memory.
  data Memory (l : Label) : Set where
    ∙ : Memory l  
    [] : Memory l
    _∷_ : ∀ {c τ} -> Cell τ c -> Memory l -> Memory l

  -- A store contains several memories divided by level.
  -- Furthermore it requires each level to be unique.
  data Store : (List Label) -> Set where
    [] : Store []
    _∷_ : ∀ {l ls} {{u : Unique l ls}} -> Memory l -> Store ls -> Store (l ∷ ls)

  -- Type synonym that ensures no duplicates in a list.
  Unique : Label -> List Label -> Set
  Unique l₁ ls = All (λ l₂ → ¬ (l₁ ≡ l₂)) ls

--------------------------------------------------------------------------------

∈-not-unique : ∀ {l ls} -> l ∈ ls -> Unique l ls -> ⊥
∈-not-unique Here (px ∷ q) = ⊥-elim (px refl)
∈-not-unique (There p) (px ∷ q) = ∈-not-unique p q

store-unique : ∀ {l ls} -> Store ls -> (x y : l ∈ ls) -> x ≡ y
store-unique s Here Here = refl
store-unique (_∷_ {{u = u}} x s) Here (There y) = ⊥-elim (∈-not-unique y u)
store-unique (_∷_ {{u = u}} x s) (There x₁) Here = ⊥-elim (∈-not-unique x₁ u)
store-unique (l ∷ s) (There x) (There y) = cong There (store-unique s x y)

--------------------------------------------------------------------------------

-- data TypedIx {l} (τ : Ty) : Status -> CTerm Nat -> Memory l -> Set where
--   Here : ∀ {m p} {c : Cell τ p} -> TypedIx τ p zero (c ∷ m)
--   There : ∀ {m n p p' τ'} {c : Cell τ' p'} -> TypedIx τ p n m -> TypedIx τ p (suc n) (c ∷ m)
--   ∙ : ∀ {n} -> TypedIx τ F n ∙

-- index-unique : ∀ {τ n p l} {m : Memory l} -> (i j : TypedIx τ p n m) -> i ≡ j
-- index-unique Here Here = refl
-- index-unique (There i) (There j) rewrite index-unique i j = refl
-- index-unique ∙ ∙ = refl

-- index-unique-status : ∀ {τ n l} {m : Memory l} -> TypedIx τ F n m -> TypedIx τ E n m -> ⊥
-- index-unique-status Here ()
-- index-unique-status (There x) (There y) = index-unique-status x y
-- index-unique-status ∙ ()

-- liftLabeled : ∀ {p τ l} -> Cell τ p -> Cell (Labeled l τ) p
-- liftLabeled ⊞ = ⊞
-- liftLabeled ⟦ x ⟧ = ⟦ (Res (Id x)) ⟧

-- -- TODO : better name / symbol
-- get : ∀ {τ} -> Cell τ F -> CTerm τ
-- get ⟦ x ⟧ = x

-- -- Read from memory
-- _[_] : ∀ {τ l n p} -> (m : Memory l) -> TypedIx τ p n m -> Cell (Labeled l τ) p
-- (c ∷ m) [ Here ] = liftLabeled c
-- (c ∷ m) [ There i ] = _[_] m i 
-- _[_] {p = F} ∙ ∙ = ⟦ Res ∙ ⟧

-- -- Update something in memory
-- _[_]≔_ : ∀ {p₁ p₂ l τ n} -> (m : Memory l) -> TypedIx τ p₁ n m -> Cell τ p₂ -> Memory l
-- (_ ∷ m) [ Here ]≔ c = c ∷ m
-- (c ∷ m) [ There i ]≔ c₁ = c ∷ (m [ i ]≔ c₁)
-- ∙ [ ∙ ]≔ c = ∙

-- infixr 2 _[_]≔_

-- -- Snoc for memory
-- _∷ʳ_ : ∀ {τ l p} -> Memory l -> Cell p τ ->  Memory l 
-- [] ∷ʳ c = c ∷ []
-- (x ∷ m) ∷ʳ c = x ∷ (m ∷ʳ c)
-- ∙  ∷ʳ c  = ∙

-- getMemory : ∀ {l ls} -> l ∈ ls -> Store ls ->  Memory l
-- getMemory Here (x ∷ s) = x
-- getMemory (There q) (x ∷ s) = getMemory q s

-- updateMemory : ∀ {l ls} -> l ∈ ls -> Store ls -> Memory l -> Store ls
-- updateMemory Here (x ∷ s) m = m ∷ s
-- updateMemory (There q) (x ∷ s) m = x ∷ updateMemory q s m

-- count : ∀ {l} -> Memory l -> CTerm Nat
-- count ∙ = ∙
-- count [] = zero
-- count (x ∷ m) = suc (count m)

-- -- Every piece of information that comes from the memory must be labeled with the same
-- -- security level.
-- lengthᵐ : ∀ {l} -> Memory l -> CTerm (Res l Nat)
-- lengthᵐ m = Res (count m)

-- -- Read from memory in store
-- _[_][_]ᶜ : ∀ {p τ ls l n} -> (s : Store ls) (q : l ∈ ls) -> TypedIx τ p n (getMemory q s) -> Cell (Labeled l τ) p
-- (m ∷ s) [ Here ][ r ]ᶜ = m [ r ]
-- (x ∷ s) [ There q ][ r ]ᶜ = s [ q ][ r ]ᶜ

-- _[_][_] : ∀ {τ ls l n} -> (s : Store ls) (q : l ∈ ls) -> TypedIx τ F n (getMemory q s) -> CTerm (Labeled l τ)
-- s [ q ][ r ] = get (s [ q ][ r ]ᶜ)

-- -- Write a cell to memory in store.
-- _[_][_]≔_ : ∀ {τ ls l n p₁ p₂} -> (s : Store ls) (q : l ∈ ls) -> TypedIx τ p₁ n (getMemory q s) -> Cell τ p₂ -> Store ls
-- (m ∷ s) [ Here ][ r ]≔ c = (m [ r ]≔ c) ∷ s
-- (x ∷ s) [ There q ][ r ]≔ c = x ∷ (s [ q ][ r ]≔ c)

-- newˢ : ∀ {p l ls τ} -> l ∈ ls -> Store ls -> Cell τ p -> Store ls
-- newˢ Here (m ∷ s) c = (m ∷ʳ c) ∷ s
-- newˢ (There q) (x ∷ s) c = x ∷ newˢ q s c

-- --------------------------------------------------------------------------------

-- The proof that a certain term is a value
data IsValue {Δ : Context} : ∀ {τ} -> Term Δ τ -> Set where
  （） : IsValue （）
  True : IsValue True
  False : IsValue False
  Abs : ∀ {α β} (t : Term (α ∷ Δ) β) -> IsValue (Abs t)
  Id : ∀ {τ} -> (t : Term Δ τ) -> IsValue (Id t) 
  Mac : ∀ {α} {l : Label} (t : Term Δ α) -> IsValue (Mac {l = l} t)
  Res : ∀ {α} {l : Label} (t : Term Δ α) -> IsValue (Res {l = l} t)

--------------------------------------------------------------------------------

-- The context of a term can be extended without harm
wken : ∀ {τ Δ₁ Δ₂} -> Term Δ₁ τ -> Δ₁ ⊆ˡ Δ₂ -> Term Δ₂ τ
wken （） p = （）
wken True p = True
wken False p = False
wken (Id t) p = Id (wken t p)
wken (unId t) p = unId (wken t p)
wken (Var x) p = Var (wken-∈ x p)
wken (Abs t) p = Abs (wken t (cons p))
wken (App t t₁) p = App (wken t p) (wken t₁ p)
wken (If t Then t₁ Else t₂) p = If (wken t p) Then (wken t₁ p) Else (wken t₂ p)
wken (Return t) p = Return (wken t p)
wken (t >>= t₁) p = (wken t p) >>= (wken t₁ p)
wken (Mac t) p = Mac (wken t p)
wken (Res t) p = Res (wken t p)
wken (label x t) p = label x (wken t p)
wken (label∙ x t) p = label∙ x (wken t p)
wken (unlabel x t) p = unlabel x (wken t p)
-- wken (read x t) p = read x (wken t p)
-- wken (write x t t₁) p = write x (wken t p) (wken t₁ p)
-- wken (new x t) p = new x (wken t p)
wken (fork x t) p = fork x (wken t p)
-- wken (newMVar {α = α} x) p = newMVar {α = α} x
-- wken (takeMVar t) p = takeMVar (wken t p)
-- wken (putMVar t₁ t₂) p = putMVar (wken t₁ p) (wken t₂ p)
wken ∙ p = ∙

_↑¹ : ∀ {α β Δ} -> Term Δ α -> Term (β ∷ Δ) α
t ↑¹ = wken t (drop refl-⊆ˡ)

-- Performs the variable-term substitution.
var-subst : ∀ {α β} (Δ₁ Δ₂ : Context) -> Term Δ₂ α -> β ∈ (Δ₁ ++ L.[ α ] ++ Δ₂) -> Term (Δ₁ ++ Δ₂) β
var-subst [] Δ₂ t Here = t
var-subst [] Δ t (There p) = Var p
var-subst (β ∷ Δ₁) Δ₂ t Here = Var Here
var-subst (x ∷ Δ₁) Δ₂ t (There p) = (var-subst Δ₁ Δ₂ t p) ↑¹

tm-subst : ∀ {α τ} (Δ₁ Δ₂ : Context) -> Term Δ₂ α -> Term (Δ₁ ++ L.[ α ] ++ Δ₂) τ -> Term (Δ₁ ++ Δ₂) τ
tm-subst Δ₁ Δ₂ v （） = （）
tm-subst Δ₁ Δ₂ v True = True
tm-subst Δ₁ Δ₂ v False = False
tm-subst Δ₁ Δ₂ v (Id t) = Id (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (unId t) = unId (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (Var x) = var-subst Δ₁ Δ₂ v x
tm-subst Δ₁ Δ₂ v (Abs t) = Abs (tm-subst (_ ∷ Δ₁) Δ₂ v t)
tm-subst Δ₁ Δ₂ v (App t t₁) = App (tm-subst Δ₁ Δ₂ v t) (tm-subst Δ₁ Δ₂ v t₁)
tm-subst Δ₁ Δ₂ v (If t Then t₁ Else t₂) = If (tm-subst Δ₁ Δ₂ v t) Then (tm-subst Δ₁ Δ₂ v t₁) Else (tm-subst Δ₁ Δ₂ v t₂)
tm-subst Δ₁ Δ₂ v (Return t) = Return (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (t >>= t₁) = (tm-subst Δ₁ Δ₂ v t) >>= (tm-subst Δ₁ Δ₂ v t₁)
tm-subst Δ₁ Δ₂ v (Mac t) = Mac (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (Res t) = Res (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (label x t) = label x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (label∙ x t) = label∙ x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (unlabel x t) = unlabel x (tm-subst Δ₁ Δ₂ v t)
-- tm-subst Δ₁ Δ₂ v (read x t) = read x (tm-subst Δ₁ Δ₂ v t)
-- tm-subst Δ₁ Δ₂ v (write x t t₁) = write x (tm-subst Δ₁ Δ₂ v t) (tm-subst Δ₁ Δ₂ v t₁)
-- tm-subst Δ₁ Δ₂ v (new x t) = new x (tm-subst Δ₁ Δ₂ v t)
tm-subst Δ₁ Δ₂ v (fork x t) = fork x (tm-subst Δ₁ Δ₂ v t)
-- tm-subst Δ₁ Δ₂ v (newMVar {α = α} x) = newMVar {α = α} x
-- tm-subst Δ₁ Δ₂ v (takeMVar t) = takeMVar (tm-subst Δ₁ Δ₂ v t)
-- tm-subst Δ₁ Δ₂ v (putMVar t₁ t₂) = putMVar (tm-subst Δ₁ Δ₂ v t₁) (tm-subst Δ₁ Δ₂ v t₂)
tm-subst Δ₁ Δ₂ v ∙ = ∙

subst : ∀ {Δ α β} -> Term Δ α -> Term (α ∷ Δ) β -> Term Δ β
subst {Δ} v t = tm-subst [] Δ v t

--------------------------------------------------------------------------------

-- A program is made of a labeled store and a closed term
record Program (ls : List Label) (τ : Ty) : Set where
  constructor ⟨_∥_⟩
  field store : Store ls
  field term : CTerm τ

open Program

term-≡ : ∀ {ls τ} {p₁ p₂ : Program ls τ} -> p₁ ≡ p₂ -> term p₁ ≡ term p₂
term-≡ refl = refl

store-≡ : ∀ {ls τ} {p₁ p₂ : Program ls τ} -> p₁ ≡ p₂ -> store p₁ ≡ store p₂
store-≡ refl = refl


--------------------------------------------------------------------------------

Thread : Label -> Set
Thread l = CTerm (Mac l （）)

data IsFork : ∀ {τ} -> CTerm τ -> Set where
  fork : ∀ {l h} -> (p : l ⊑ h) (t : Thread h ) -> IsFork (fork p t)

isFork? : ∀ {τ} -> (t : CTerm τ) -> Dec (IsFork t)
isFork? （） = no (λ ())
isFork? True = no (λ ())
isFork? False = no (λ ())
isFork? (Var x) = no (λ ())
isFork? (Abs t) = no (λ ())
isFork? (App t t₁) = no (λ ())
isFork? (If t Then t₁ Else t₂) = no (λ ())
isFork? (Id t) = no (λ ())
isFork? (unId t) = no (λ ())
isFork? (Return t) = no (λ ())
isFork? (t >>= t₁) = no (λ ())
isFork? (Mac t) = no (λ ())
isFork? (Res t) = no (λ ())
isFork? (label x t) = no (λ ())
isFork? (label∙ x t) = no (λ ())
isFork? (unlabel x t) = no (λ ())
-- isFork? (read x t) = no (λ ())
-- isFork? (write x t t₁) = no (λ ())
-- isFork? (new x t) = no (λ ())
isFork? (fork x t) = yes (fork x t)
-- isFork? (newMVar x) = no (λ ())
-- isFork? (takeMVar t) = no (λ ())
-- isFork? (putMVar t t₁) = no (λ ())
isFork? ∙ = no (λ ())

-- TODO this can be just a synonym of = ∙.
data Is∙ {τ : Ty} : CTerm τ -> Set where
  ∙ : Is∙ ∙

is∙? : ∀ {τ} -> (c : CTerm τ) -> Dec (Is∙ c)
is∙? （） = no (λ ())
is∙? True = no (λ ())
is∙? False = no (λ ())
is∙? (Var x) = no (λ ())
is∙? (Abs c) = no (λ ())
is∙? (App c c₁) = no (λ ())
is∙? (If c Then c₁ Else c₂) = no (λ ())
is∙? (Id t) = no (λ ())
is∙? (unId t) = no (λ ())
is∙? (Return c) = no (λ ())
is∙? (c >>= c₁) = no (λ ())
is∙? (Mac c) = no (λ ())
is∙? (Res c) = no (λ ())
is∙? (label x c) = no (λ ())
is∙? (label∙ x c) = no (λ ())
is∙? (unlabel x c) = no (λ ())
-- is∙? (read x c) = no (λ ())
-- is∙? (write x c c₁) = no (λ ())
-- is∙? (new x c) = no (λ ())
is∙? (fork x c) = no (λ ())
-- is∙? (newMVar x) = no (λ ())
-- is∙? (takeMVar c) = no (λ ())
-- is∙? (putMVar c c₁) = no (λ ())
is∙? ∙ = yes ∙
