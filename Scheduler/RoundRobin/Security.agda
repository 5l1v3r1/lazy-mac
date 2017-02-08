import Lattice as L

module Scheduler.RoundRobin.Security {𝓛 : L.Lattice} (A : L.Label 𝓛) where

open import Data.Product
open import Relation.Nullary

open L.Lattice 𝓛
import Scheduler.RoundRobin.Base as R
open R 𝓛
open import Scheduler.Base 𝓛 renaming (_,_,_ to ⟪_,_,_⟫)
open import Scheduler.Security 𝓛 A

open import Data.List
open import Data.Empty
open import Data.Nat
open import Data.Product


εˢ : State -> State
εˢ [] = []
εˢ ((l , n) ∷ s) with l ⊑? A
εˢ ((l , n) ∷ s) | yes p = (l , n) ∷ (εˢ s)
εˢ ((l , n) ∷ s) | no ¬p = εˢ s

open import Relation.Binary.PropositionalEquality hiding ([_])

εˢ-append-yes : ∀ {l} {{n}} -> (xs : State) -> l ⊑ A -> εˢ xs ++ [ l , n ] ≡ εˢ (xs ++ [ l , n ])
εˢ-append-yes {l} [] ¬p with l ⊑? A
εˢ-append-yes [] p' | yes p = refl
εˢ-append-yes [] p | no ¬p = ⊥-elim (¬p p)
εˢ-append-yes {{n}} ((l' , n') ∷ xs) p with l' ⊑? A
... | yes p' rewrite εˢ-append-yes {{n}} xs p = refl
... | no ¬p rewrite εˢ-append-yes {{n}} xs p = refl


εˢ-append-no : ∀ {l} {{n}} -> (xs : State) -> ¬ (l ⊑ A) -> εˢ xs ≡ εˢ (xs ++ [ l , n ])
εˢ-append-no {l} [] ¬p with l ⊑? A
εˢ-append-no [] ¬p | yes p = ⊥-elim (¬p p)
εˢ-append-no [] ¬p₁ | no ¬p = refl
εˢ-append-no {{n}} ((l' , n') ∷ xs) ¬p with l' ⊑? A
... | yes p rewrite εˢ-append-no {{n}} xs ¬p  = refl
... | no ¬p' rewrite εˢ-append-no {{n}} xs ¬p  = refl

-- TODO use this more general concept instead of append-yes or append-no
ε-++ : (s₁ s₂ : State) -> εˢ (s₁ ++ s₂) ≡ (εˢ s₁) ++ (εˢ s₂)
ε-++ [] s₂ = refl
ε-++ ((l , n) ∷ s₁) s₂ with l ⊑? A
ε-++ ((l , n) ∷ s₁) s₂ | yes p rewrite ε-++ s₁ s₂ = refl
ε-++ ((l , n) ∷ s₁) s₂ | no ¬p = ε-++ s₁ s₂

++[] :  (s : State) -> s ++ [] ≡ s
++[] [] = refl
++[] (x ∷ s) rewrite ++[] s = refl

ε-sch-dist : ∀ {l s₁ s₂} {m : Message l} -> (x : Dec (l ⊑ A)) -> s₁ ⟶ s₂ ↑ m -> (εˢ s₁) ⟶ (εˢ s₂) ↑ (εᴹ x m)
ε-sch-dist = {!!}
-- ε-sch-dist {s₁ = (l , n) ∷ s} (yes p) step with l ⊑? A
-- ε-sch-dist {s₁ = (l , n) ∷ s} (yes p₁) step | yes p rewrite sym (εˢ-append-yes {{n}} s p) = step
-- ε-sch-dist {s₁ = (l , n) ∷ s} (yes p) step | no ¬p = ⊥-elim (¬p p)
-- ε-sch-dist {s₁ = (l , n) ∷ s₁} (no ¬p) step with l ⊑? A
-- ε-sch-dist {s₁ = (l , n) ∷ s₁} (no ¬p) step | yes p = ⊥-elim (¬p p)
-- ε-sch-dist {s₁ = (l , n) ∷ s₁} (no ¬p₁) step | no ¬p rewrite εˢ-append-no {{n}} s₁ ¬p = hole
-- ε-sch-dist  (yes p) (fork {s} {l} {n} {h} {m} p') rewrite ε-++ s (((h , m) ∷ (l , n) ∷ [])) with l ⊑? A | h ⊑? A
-- ε-sch-dist  (yes p₂) (fork {l = l} p') | yes p | yes p₁ with l ⊑? A
-- ε-sch-dist (yes p₃) (fork p') | yes p₁ | yes p₂ | yes p = fork p'
-- ε-sch-dist (yes p₂) (fork p') | yes p | yes p₁ | no ¬p = ⊥-elim (¬p p₂)
-- ε-sch-dist (yes p₁) (fork {l = l} p') | yes p | no ¬p with l ⊑? A
-- ε-sch-dist (yes p₂) (fork p') | yes p₁ | no ¬p | yes p = step
-- ε-sch-dist (yes p₁) (fork p') | yes p | no ¬p₁ | no ¬p = ⊥-elim (¬p p₁)
-- ε-sch-dist (yes p) (fork p') | no ¬p | b = ⊥-elim (¬p p)
-- ε-sch-dist (no ¬p) (fork {s} {l} {n} p') with l ⊑? A
-- ε-sch-dist (no ¬p) (fork p') | yes p = ⊥-elim (¬p p)
-- ε-sch-dist (no ¬p₁) (fork {s} {l} {n} {h} {m} p') | no ¬p rewrite ε-++ s (((h , m) ∷ (l , n) ∷ [])) with h ⊑? A
-- ... | yes p = ⊥-elim (trans-⋢ p' ¬p₁ p)
-- ... | no ¬p' with l ⊑? A
-- ... | yes p'' = ⊥-elim (¬p₁ p'')
-- ... | no ¬p'' rewrite ++[] (εˢ s) = hole
-- ε-sch-dist {l} {A} (yes p) done = ?
-- -- with l ⊑? A
-- ε-sch-dist (yes p₁) done | yes p = done
-- ε-sch-dist (yes p) done | no ¬p = ⊥-elim (¬p p)
-- ε-sch-dist {l} {A} (no ¬p) done with l ⊑? A
-- ε-sch-dist (no ¬p) done | yes p = ⊥-elim (¬p p)
-- ε-sch-dist (no ¬p₁) done | no ¬p = hole
-- ε-sch-dist {l} {A} (yes p) skip with l ⊑? A
-- ε-sch-dist (yes p₁) (skip {s = s} {n = n}) | yes p rewrite sym (εˢ-append-yes {{n}} s p) = skip
-- ε-sch-dist (yes p) (skip {s = s} {n = n}) | no ¬p = ⊥-elim (¬p p)
-- ε-sch-dist {l} {A} (no ¬p) skip with l ⊑? A
-- ε-sch-dist (no ¬p) skip | yes p = ⊥-elim (¬p p)
-- ε-sch-dist (no ¬p₁) (skip {s = s} {n = n}) | no ¬p rewrite εˢ-append-no {{n}} s ¬p = hole
-- ε-sch-dist (yes p) hole = hole
-- ε-sch-dist (no ¬p) hole = hole

-- mutual
--   data _≈ˢ_ {{l : Label}} : State -> State -> Set where
--     nil : [] ≈ˢ []
--     consᴸ : ∀ {l n s₁ s₂} -> (p : l ⊑ A) ->  s₁ ≈ˢ-⟨ ⟩ s₂ -> ((l , n) ∷ s₁) ≈ˢ ((l , n) ∷ s₂)
--     cons₁ᴴ : ∀ {h n s₁ s₂ } -> (¬p  : ¬ (h ⊑ A)) -> s₁ ≈ˢ-⟨ ⟩ s₂ -> ((h , n) ∷ s₁) ≈ˢ s₂
--     cons₂ᴴ : ∀ {h n s₁ s₂} -> (¬p  : ¬ (h ⊑ A)) -> s₁ ≈ˢ-⟨ ⟩ s₂ -> s₁ ≈ˢ ((h , n) ∷ s₂)

--   _≈ˢ-⟨_⟩_ : State -> Label -> State -> Set
--   s₁ ≈ˢ-⟨ ⟩ s₂ = s₁ ≈ˢ s₂

-- ≈ˢ-≡ : ∀ {s₁ s₂} -> s₁ ≈ˢ s₂ -> εˢ s₁ ≡ εˢ s₂
-- ≈ˢ-≡ nil = refl
-- ≈ˢ-≡ {A} (consᴸ {l} p x) with l ⊑? A
-- ≈ˢ-≡ (consᴸ p₁ x) | yes p rewrite ≈ˢ-≡ x = refl
-- ≈ˢ-≡ (consᴸ p x) | no ¬p = ⊥-elim (¬p p)
-- ≈ˢ-≡ {A} (cons₁ᴴ {h} ¬p x) with h ⊑? A
-- ≈ˢ-≡ (cons₁ᴴ ¬p x) | yes p = ⊥-elim (¬p p)
-- ≈ˢ-≡ (cons₁ᴴ ¬p₁ x) | no ¬p =  ≈ˢ-≡ x
-- ≈ˢ-≡ {A} (cons₂ᴴ {h} ¬p x) with h ⊑? A
-- ≈ˢ-≡ (cons₂ᴴ ¬p x) | yes p = ⊥-elim (¬p p)
-- ≈ˢ-≡ (cons₂ᴴ ¬p₁ x) | no ¬p = ≈ˢ-≡ x

-- ∷-≡ : ∀ {x y : Label × ℕ} {s₁ s₂ : State} -> _≡_ {A = State} (x ∷ s₁) (y ∷ s₂) -> x ≡ y × s₁ ≡ s₂
-- ∷-≡ refl = refl , refl

-- ≡-≈ˢ : ∀ {s₁ s₂} -> εˢ s₁ ≡ εˢ s₂ -> s₁ ≈ˢ s₂

-- ≡-≈ˢ₁ : ∀ {l n s₁ s₂} -> l ⊑ -> (l , n) ∷ εˢ s₁ ≡ εˢ s₂ -> ((l , n) ∷ s₁) ≈ˢ-⟨ ⟩ s₂
-- ≡-≈ˢ₁ {s₂ = []} p ()
-- ≡-≈ˢ₁ {A} {s₂ = (l' , n') ∷ s₂} p eq with l' ⊑? A
-- ≡-≈ˢ₁ {A} {l} {n} {s₁} {(l' , n') ∷ s₂} p₁ eq | yes p with ∷-≡ eq
-- ≡-≈ˢ₁ {A} {l'} {n'} {s₁} {(.l' , .n') ∷ s₂} p₁ eq | yes p | refl , eq₂ = consᴸ p₁ (≡-≈ˢ eq₂)
-- ≡-≈ˢ₁ {A} {l} {n} {s₁} {(l' , n') ∷ s₂} p eq | no ¬p = cons₂ᴴ ¬p (≡-≈ˢ₁ p eq)

-- ≡-≈ˢ {s₁ = []} {[]} eq = nil
-- ≡-≈ˢ {A} {s₁ = []} {(l , n) ∷ s₂} eq with l ⊑? A
-- ≡-≈ˢ {A} {[]} {(l , n) ∷ s₂} () | yes p
-- ≡-≈ˢ {A} {[]} {(l , n) ∷ s₂} eq | no ¬p = cons₂ᴴ ¬p (≡-≈ˢ eq)
-- ≡-≈ˢ {A} {s₁ = (l , n) ∷ s₁} {[]} eq with l ⊑? A
-- ≡-≈ˢ {A} {(l , n) ∷ s₁} {[]} () | yes p
-- ≡-≈ˢ {A} {(l , n) ∷ s₁} {[]} eq | no ¬p = cons₁ᴴ ¬p (≡-≈ˢ eq)
-- ≡-≈ˢ {A} {s₁ = (l , n) ∷ s₁} {(l' , n') ∷ s₂} eq with l ⊑? A
-- ≡-≈ˢ {A} {(l , n) ∷ s₁} {(l' , n') ∷ s₂} eq | yes p with l' ⊑? A
-- ≡-≈ˢ {A} {(l , n) ∷ s₁} {(l' , n') ∷ s₂} eq | yes p₁ | yes p with ∷-≡ eq
-- ≡-≈ˢ {A} {(l' , n) ∷ s₁} {(.l' , .n) ∷ s₂} eq | yes p₁ | yes p | refl , eq₂ = consᴸ p₁ (≡-≈ˢ eq₂)
-- ≡-≈ˢ {A} {(l , n) ∷ s₁} {(l' , n') ∷ s₂} eq | yes p | no ¬p = cons₂ᴴ ¬p (≡-≈ˢ₁ p eq)
-- ≡-≈ˢ {A} {(l , n) ∷ s₁} {(l' , n') ∷ s₂} eq | no ¬p = cons₁ᴴ ¬p (≡-≈ˢ eq)

-- open import Function

-- offset₁ : ∀ {s₁ s₂ A} -> s₁ ≈ˢ-⟨ ⟩ s₂ -> ℕ
-- offset₁ nil = 0
-- offset₁ (consᴸ p x) = 0
-- offset₁ (cons₁ᴴ ¬p x) = suc (offset₁ x)
-- offset₁ (cons₂ᴴ ¬p x) = offset₁ x

-- offset₂ : ∀ {s₁ s₂ A} -> s₁ ≈ˢ-⟨ ⟩ s₂ -> ℕ
-- offset₂ nil = 0
-- offset₂ (consᴸ p x) = 0
-- offset₂ (cons₁ᴴ ¬p x) = offset₂ x
-- offset₂ (cons₂ᴴ ¬p x) = suc (offset₂ x)


-- mutual
--   data _≈ˢ-⟨_~_⟩_ {{l : Label}} : State -> ℕ -> ℕ -> State -> Set where
--        nil : [] ≈ˢ-⟨ 0 ~ 0 ⟩ []
--        consᴸ : ∀ {l n s₁ s₂} -> (p : l ⊑ A) ->  s₁ ≈ˢ-⟨ ⟩ s₂ -> ((l , n) ∷ s₁) ≈ˢ-⟨ 0 ~ 0 ⟩ ((l , n) ∷ s₂)
--        cons₁ᴴ : ∀ {h n s₁ s₂ i j} -> (¬p  : ¬ (h ⊑ A)) -> s₁ ≈ˢ-⟨ i ~ ~ j ⟩ s₂ -> ((h , n) ∷ s₁) ≈ˢ-⟨ suc i ~ j ⟩ s₂
--        cons₂ᴴ : ∀ {h n s₁ s₂ i j} -> (¬p  : ¬ (h ⊑ A)) -> s₁ ≈ˢ-⟨ i ~ ~ j ⟩ s₂ -> s₁ ≈ˢ-⟨ i ~ suc j ⟩ ((h , n) ∷ s₂)

--   _≈ˢ-⟨_~_~_⟩_ : State -> ℕ -> Label -> ℕ -> State -> Set
--   _≈ˢ-⟨_~_~_⟩_ s₁ n m s₂ = s₁ ≈ˢ-⟨ n ~ m ⟩ s₂

-- align : ∀ {s₁ s₂} -> (eq : s₁ ≈ˢ-⟨ ⟩ s₂) -> s₁ ≈ˢ-⟨ offset₁ eq ~ ~ offset₂ eq ⟩ s₂
-- align nil = nil
-- align (consᴸ p x) = consᴸ p x
-- align (cons₁ᴴ ¬p x) = cons₁ᴴ ¬p (align x)
-- align (cons₂ᴴ ¬p x) = cons₂ᴴ ¬p (align x)

-- dealign : ∀ {s₁ s₂ i j} -> s₁ ≈ˢ-⟨ i ~ ~ j ⟩ s₂ -> s₁ ≈ˢ-⟨ ⟩ s₂
-- dealign nil = nil
-- dealign (consᴸ p x) = consᴸ p x
-- dealign (cons₁ᴴ ¬p x) = cons₁ᴴ ¬p (dealign x)
-- dealign (cons₂ᴴ ¬p x) = cons₂ᴴ ¬p (dealign x)

-- open import Concurrent.Security.Scheduler State _⟶_↑_ εˢ _≈ˢ-⟨_⟩_ _≈ˢ-⟨_~_~_⟩_

-- ++-≈ˢ : ∀ {s₁ s₂ x} -> s₁ ≈ˢ s₂ -> (s₁ ++ x) ≈ˢ (s₂ ++ x)
-- ++-≈ˢ {x = x} nil = ≡-≈ˢ refl
-- ++-≈ˢ (consᴸ p x₁) = consᴸ p (++-≈ˢ x₁)
-- ++-≈ˢ (cons₁ᴴ ¬p x₁) = cons₁ᴴ ¬p (++-≈ˢ x₁)
-- ++-≈ˢ (cons₂ᴴ ¬p x₁) = cons₂ᴴ ¬p (++-≈ˢ x₁)

-- ++₁-≈ˢ : ∀ {s₁ s₂ h} {{n}} -> ¬ (h ⊑ A) -> s₁ ≈ˢ-⟨ ⟩ s₂ -> s₁ ≈ˢ-⟨ ⟩ (s₂ ++ [ h , n ])
-- ++₁-≈ˢ ¬p nil = cons₂ᴴ ¬p nil
-- ++₁-≈ˢ ¬p (consᴸ p x) = consᴸ p (++₁-≈ˢ ¬p x)
-- ++₁-≈ˢ ¬p (cons₁ᴴ ¬p₁ x) = cons₁ᴴ ¬p₁ (++₁-≈ˢ ¬p x)
-- ++₁-≈ˢ ¬p (cons₂ᴴ ¬p₁ x) = cons₂ᴴ ¬p₁ (++₁-≈ˢ ¬p x)

-- ++₂-≈ˢ : ∀ {s₁ s₂ h₁ h₂ n₁ n₂} -> ¬ (h₁ ⊑ A) -> ¬ (h₂ ⊑ A) -> s₁ ≈ˢ-⟨ ⟩ s₂ -> s₁ ≈ˢ-⟨ ⟩ (s₂ ++  (h₁ , n₁) ∷ ((h₂ , n₂) ∷ []))
-- ++₂-≈ˢ ¬p₁ ¬p₂ nil = cons₂ᴴ ¬p₁ (cons₂ᴴ ¬p₂ nil)
-- ++₂-≈ˢ ¬p₁ ¬p₂ (consᴸ p x) = consᴸ p (++₂-≈ˢ ¬p₁ ¬p₂ x)
-- ++₂-≈ˢ ¬p₁ ¬p₂ (cons₁ᴴ ¬p x) = cons₁ᴴ ¬p (++₂-≈ˢ ¬p₁ ¬p₂ x)
-- ++₂-≈ˢ ¬p₁ ¬p₂ (cons₂ᴴ ¬p x) = cons₂ᴴ ¬p (++₂-≈ˢ ¬p₁ ¬p₂ x)

-- --fork-≈ˢ : ∀ {s₁ s₂}

-- aligned : ∀ {l i e n s₁ s₂ s₁'}  -> l ⊑ -> s₁ ⟶ s₂ ↑ ⟪ l , n , e ⟫ -> e ≢ ∙ -> s₁ ≈ˢ-⟨ i ~ ~ 0 ⟩ s₁' -> Aligned s₁ s₂ s₁' ⟪ l , n , e ⟫ A
-- aligned p hole e≠∙ nil = ⊥-elim (e≠∙ refl)
-- aligned p step e≠∙ (consᴸ p₁ x) = low step (++-≈ˢ x)
-- aligned p (fork p₁) e≠∙ (consᴸ p₂ x) = low (fork p₁) (++-≈ˢ x)
-- aligned p done e≠∙ (consᴸ p₁ x) = low done x
-- aligned p skip e≠∙ (consᴸ p₁ x) = low skip (++-≈ˢ x)
-- aligned p hole e≠∙ (consᴸ p₁ x) = ⊥-elim (e≠∙ refl)
-- aligned p step e≠∙ (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
-- aligned p (fork p₁) e≠∙ (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
-- aligned p done e≠∙ (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
-- aligned p skip e≠∙ (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
-- aligned p hole e≠∙ (cons₁ᴴ ¬p x) = ⊥-elim (e≠∙ refl)

-- open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)

-- lemma : ∀ {s₁ s₁' s₂ i j h n n' l e} -> ¬ h ⊑ -> l ⊑ -> s₁ ⟶ s₂ ↑ ⟪ l , n' , e ⟫ -> e ≢ ∙ -> s₁ ≈ˢ-⟨ i ~ ~ j ⟩ s₁'
--               -> s₁ ≈ˢ-⟨ i ~ ~ j ⟩ (s₁' ++ [ h , n ])
-- lemma ¬p p hole e≠∙ nil = ⊥-elim (e≠∙ refl)
-- lemma ¬p p s e≠∙  (consᴸ p' x) = consᴸ p' (++₁-≈ˢ ¬p x)
-- lemma ¬p p step e≠∙  (cons₁ᴴ ¬p₁ x) = ⊥-elim (¬p₁ p)
-- lemma ¬p p (fork p') e≠∙  (cons₁ᴴ ¬p₁ x) = ⊥-elim (¬p₁ p)
-- lemma ¬p p done e≠∙ (cons₁ᴴ ¬p₁ x) = ⊥-elim (¬p₁ p)
-- lemma ¬p p skip e≠∙  (cons₁ᴴ ¬p₁ x) = ⊥-elim (¬p₁ p)
-- lemma ¬p p hole e≠∙ (cons₁ᴴ ¬p₁ x) = ⊥-elim (e≠∙ refl)
-- lemma {n = n} ¬p p s e≠∙  (cons₂ᴴ ¬p₁ x) = cons₂ᴴ ¬p₁ (lemma {n = n} ¬p p s e≠∙ x)

-- lemma₂ : ∀ {s₁ s₁' s₂ i j h₁ h₂ n₁ n₂ n' l e} -> ¬ h₁ ⊑ -> ¬ h₂ ⊑ -> l ⊑ -> s₁ ⟶ s₂ ↑ ⟪ l , n' , e ⟫ -> e ≢ ∙ -> s₁ ≈ˢ-⟨ i ~ ~ j ⟩ s₁'
--               -> s₁ ≈ˢ-⟨ i ~ ~ j ⟩ (s₁' ++ ((h₁ , n₁) ∷ (h₂ , n₂) ∷ []))
-- lemma₂ ¬p₁ ¬p₂ p hole e≠∙ nil = ⊥-elim (e≠∙ refl)
-- lemma₂ {n₁ = n₁} {n₂ = n₂} ¬p₁ ¬p₂ p s e≠∙ (consᴸ p₁ x) = consᴸ p₁ (++₂-≈ˢ ¬p₁ ¬p₂ x)
-- lemma₂ ¬p₁ ¬p₂ p step e≠∙ (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
-- lemma₂ ¬p₁ ¬p₂ p (fork p₁) e≠∙ (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
-- lemma₂ ¬p₁ ¬p₂ p done e≠∙ (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
-- lemma₂ ¬p₁ ¬p₂ p skip e≠∙ (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
-- lemma₂ ¬p₁ ¬p₂ p hole e≠∙ (cons₁ᴴ ¬p x) = ⊥-elim (e≠∙ refl)
-- lemma₂ ¬p₁ ¬p₂ p s e≠∙ (cons₂ᴴ ¬p x) = cons₂ᴴ ¬p (lemma₂ ¬p₁ ¬p₂ p s e≠∙ x)

-- highˢ : ∀ {s₁ s₁' s₂ l e n n₁ n₂} -> l ⊑ -> s₁ ⟶ s₂ ↑ ⟪ l , n , e ⟫ -> e ≢ ∙ -> s₁ ≈ˢ-⟨ n₁ ~ ~ suc n₂ ⟩ s₁' ->
--           ∃ λ h -> ∃ λ n -> (e : Event h) -> e ≢ ∙ -> HighStep h n e s₁ s₂ s₁' n₁ n₂
-- highˢ p step e≠∙ (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
-- highˢ p (fork p₁) e≠∙ (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
-- highˢ p done e≠∙ (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
-- highˢ p skip e≠∙ (cons₁ᴴ ¬p x) = ⊥-elim (¬p p)
-- highˢ p hole e≠∙ (cons₁ᴴ ¬p x) = ⊥-elim (e≠∙ refl)
-- highˢ {s₁} {(h , n) ∷ s₁'} {s₂} {l} {A} {e} {n'} {n₁} {n₂} p s e≠∙ (cons₂ᴴ  ¬p x) with lemma {n = n} ¬p p s e≠∙ x
-- ... | eq' = h , (n , aux)
--   where aux : (e : Event h) -> e ≢ ∙ -> HighStep h n e s₁ s₂ ((h , n) ∷ s₁') n₁ n₂
--         aux NoStep e≠∙₁ = high ¬p skip eq'
--         aux Step e≠∙₁ = high ¬p step eq'
--         aux Done e≠∙₁ = high ¬p done x
--         aux (Fork h₁ n₃ h⊑h₁) e≠∙₁ = high ¬p (fork h⊑h₁) (lemma₂ (trans-⋢ h⊑h₁ ¬p) ¬p p s e≠∙ x)
--         aux ∙ e≠∙₁ = ⊥-elim (e≠∙₁ refl)

-- open import Concurrent.Determinism (State) (_⟶_↑_) (determinism)
-- -- open import Concurrent.Security.NonInterference State _⟶_↑_ εˢ ε-sch-dist ε-sch-≡
