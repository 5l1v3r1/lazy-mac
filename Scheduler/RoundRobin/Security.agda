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

εˢ-append-yes : (xs : State) (l : Label) (n : ℕ) -> l ⊑ A -> εˢ (xs ++ [ l , n ]) ≡ εˢ xs ++ [ l , n ]
εˢ-append-yes [] l n ¬p with l ⊑? A
εˢ-append-yes [] l n p' | yes p = refl
εˢ-append-yes [] l n p | no ¬p = ⊥-elim (¬p p)
εˢ-append-yes ((l' , n') ∷ xs) l n p with l' ⊑? A
... | yes p' rewrite εˢ-append-yes xs _ n p = refl
... | no ¬p rewrite εˢ-append-yes xs _ n p = refl


εˢ-append-no : ∀ {l} {{n}} -> (xs : State) -> ¬ (l ⊑ A) -> εˢ xs ≡ εˢ (xs ++ [ l , n ])
εˢ-append-no {l} [] ¬p with l ⊑? A
εˢ-append-no [] ¬p | yes p = ⊥-elim (¬p p)
εˢ-append-no [] ¬p₁ | no ¬p = refl
εˢ-append-no {{n}} ((l' , n') ∷ xs) ¬p with l' ⊑? A
... | yes p rewrite εˢ-append-no {{n}} xs ¬p  = refl
... | no ¬p' rewrite εˢ-append-no {{n}} xs ¬p  = refl

ε-++ : (s₁ s₂ : State) -> εˢ (s₁ ++ s₂) ≡ (εˢ s₁) ++ (εˢ s₂)
ε-++ [] s₂ = refl
ε-++ ((l , n) ∷ s₁) s₂ with l ⊑? A
ε-++ ((l , n) ∷ s₁) s₂ | yes p rewrite ε-++ s₁ s₂ = refl
ε-++ ((l , n) ∷ s₁) s₂ | no ¬p = ε-++ s₁ s₂

εˢ-simᴸ : ∀ {L} {Σ₁ Σ₂ : State} {m : Message L} -> (L⊑A : L ⊑ A) -> Σ₁ ⟶ Σ₂ ↑ m -> (εˢ Σ₁) ⟶ (εˢ Σ₂) ↑ (εᴹ m)
εˢ-simᴸ L⊑A (R.step l n) with l ⊑? A
εˢ-simᴸ L⊑A (R.step {Σ} l n) | yes p rewrite εˢ-append-yes Σ l n L⊑A = step l n
εˢ-simᴸ L⊑A (R.step l n) | no ¬p = ⊥-elim (¬p L⊑A)
εˢ-simᴸ L⊑A (R.fork L n p) with L ⊑? A
εˢ-simᴸ L⊑A (R.fork {Σ} {H} {m} L n p₁) | yes p
  rewrite ε-++ Σ ((H , m) ∷ ((L , n) ∷ [])) with H ⊑? A
εˢ-simᴸ L⊑A (R.fork L n p₂) | yes p₁ | yes p with L ⊑? A
εˢ-simᴸ L⊑A (R.fork L n p₃) | yes p₂ | yes p₁ | yes p = R.fork L n p₃
εˢ-simᴸ L⊑A (R.fork L n p₂) | yes p₁ | yes p | no ¬p = ⊥-elim (¬p L⊑A)
εˢ-simᴸ L⊑A (R.fork L n p₁) | yes p | no ¬p with L ⊑? A
εˢ-simᴸ L⊑A (R.fork L n p₂) | yes p₁ | no ¬p | yes p = R.step L n
εˢ-simᴸ L⊑A (R.fork L n p₁) | yes p | no ¬p₁ | no ¬p = ⊥-elim (¬p L⊑A)
εˢ-simᴸ L⊑A (R.fork L n p) | no ¬p = ⊥-elim (¬p L⊑A)
εˢ-simᴸ L⊑A (R.done L n) with L ⊑? A
εˢ-simᴸ L⊑A (R.done L n) | yes p = R.done L n
εˢ-simᴸ L⊑A (R.done L n) | no ¬p = ⊥-elim (¬p L⊑A)
εˢ-simᴸ L⊑A (R.skip L n) with L ⊑? A
εˢ-simᴸ L⊑A (R.skip {Σ} L n) | yes p rewrite εˢ-append-yes Σ L n L⊑A = R.skip L n
εˢ-simᴸ L⊑A (R.skip L n) | no ¬p = ⊥-elim (¬p L⊑A)

data _≈ˢ_ : State -> State -> Set where
  nil : [] ≈ˢ []
  consᴸ : ∀ {L n Σ₁ Σ₂} -> (L⊑A : L ⊑ A) ->  Σ₁ ≈ˢ Σ₂ -> ((L , n) ∷ Σ₁) ≈ˢ ((L , n) ∷ Σ₂)
  cons₁ᴴ : ∀ {H n Σ₁ Σ₂ } -> (H⋤A  : H ⋤ A) -> Σ₁ ≈ˢ Σ₂ -> ((H , n) ∷ Σ₁) ≈ˢ Σ₂
  cons₂ᴴ : ∀ {H n Σ₁ Σ₂} -> (H⋤A  : H ⋤ A) -> Σ₁ ≈ˢ Σ₂ -> Σ₁ ≈ˢ ((H , n) ∷ Σ₂)


⌜_⌝ : ∀ {Σ₁ Σ₂} -> εˢ Σ₁ ≡ εˢ Σ₂ -> Σ₁ ≈ˢ Σ₂
⌜_⌝ = aux _ _
  where
    ∷-≡ : ∀ {x y : Label × ℕ} {s₁ s₂ : State} -> _≡_ {A = State} (x ∷ s₁) (y ∷ s₂) -> x ≡ y × s₁ ≡ s₂
    ∷-≡ refl = refl , refl

    aux : ∀ (Σ₁ Σ₂ : _) -> εˢ Σ₁ ≡ εˢ Σ₂ -> Σ₁ ≈ˢ Σ₂


    aux₁ : ∀ {l n} (Σ₁ Σ₂ : State) -> (l , n) ∷ εˢ Σ₁ ≡ εˢ Σ₂ -> ((l , n) ∷ Σ₁) ≈ˢ Σ₂
    aux₁ Σ₃ [] ()
    aux₁ Σ₃ ((l' , n) ∷ Σ₄) eq with l' ⊑? A
    aux₁ Σ₃ ((l' , n₁) ∷ Σ₄) eq | yes p with ∷-≡ eq
    aux₁ Σ₃ ((l , n₁) ∷ Σ₄) eq | yes p | refl , eq' = consᴸ p (aux Σ₃ Σ₄ eq')
    aux₁ Σ₃ ((l' , n₁) ∷ Σ₄) eq | no H⋤A = cons₂ᴴ H⋤A (aux₁ Σ₃ Σ₄ eq)


    aux [] [] eq = nil
    aux [] ((l , n) ∷ Σ₂) eq with l ⊑? A
    aux [] ((l , n) ∷ Σ₂) () | yes p
    aux [] ((l , n) ∷ Σ₂) eq | no H⋤A = cons₂ᴴ H⋤A (aux [] Σ₂ eq)
    aux ((l , n) ∷ Σ₁) Σ₂ eq with l ⊑? A
    aux ((l , n) ∷ Σ₃) [] () | yes p
    aux ((l , n) ∷ Σ₃) ((l' , m) ∷ Σ₄) eq | yes p with l' ⊑? A
    aux ((l , n) ∷ Σ₃) ((l' , m) ∷ Σ₄) eq | yes p₁ | yes p with ∷-≡ eq
    aux ((l' , m) ∷ Σ₃) ((.l' , .m) ∷ Σ₄) eq | yes p₁ | yes p | refl , eq₂ = consᴸ p₁ (aux Σ₃ Σ₄ eq₂)
    aux ((l , n) ∷ Σ₃) ((l' , m) ∷ Σ₄) eq | yes p | no H⋤A = cons₂ᴴ H⋤A (aux₁ Σ₃ Σ₄ eq)
    aux ((l , n) ∷ Σ₃) Σ₄ eq | no H⋤A = cons₁ᴴ H⋤A (aux Σ₃ Σ₄ eq)



⌞_⌟ : ∀ {Σ₁ Σ₂} -> Σ₁ ≈ˢ Σ₂ -> εˢ Σ₁ ≡ εˢ Σ₂
⌞ nil ⌟ = refl
⌞ (consᴸ {l} p x) ⌟ with l ⊑? A
⌞ (consᴸ p₁ x) ⌟ | yes p rewrite ⌞_⌟ x = refl
⌞ (consᴸ p x) ⌟ | no H⋤A = ⊥-elim (H⋤A p)
⌞ (cons₁ᴴ {h} H⋤A x) ⌟ with h ⊑? A
⌞ (cons₁ᴴ H⋤A x) ⌟ | yes p = ⊥-elim (H⋤A p)
⌞ (cons₁ᴴ H⋤A₁ x) ⌟ | no H⋤A =  ⌞_⌟ x
⌞ (cons₂ᴴ {h} H⋤A x) ⌟ with h ⊑? A
⌞ (cons₂ᴴ H⋤A x) ⌟ | yes p = ⊥-elim (H⋤A p)
⌞ (cons₂ᴴ H⋤A₁ x) ⌟ | no H⋤A = ⌞ x ⌟

refl-≈ˢ : ∀ {Σ} -> Σ ≈ˢ Σ
refl-≈ˢ = ⌜ refl ⌝

sym-≈ˢ : ∀ {Σ₁ Σ₂} -> Σ₁ ≈ˢ Σ₂ -> Σ₂ ≈ˢ Σ₁
sym-≈ˢ eq = ⌜ (sym ⌞ eq ⌟) ⌝

trans-≈ˢ : ∀ {Σ₁ Σ₂ Σ₃} -> Σ₁ ≈ˢ Σ₂ -> Σ₂ ≈ˢ Σ₃ -> Σ₁ ≈ˢ Σ₃
trans-≈ˢ eq₁ eq₂ = ⌜ (trans ⌞ eq₁ ⌟ ⌞ eq₂ ⌟) ⌝

open import Data.List.All
open import Lemmas

append-≈ˢ : ∀ {Σ₁ Σ₂ Σ₃} -> All (λ x → proj₁ x ⋤ A) Σ₃ -> Σ₁ ≈ˢ Σ₂ -> Σ₁ ≈ˢ (Σ₂ ++ Σ₃)
append-≈ˢ [] nil = nil
append-≈ˢ (px ∷ xs) nil = cons₂ᴴ px (append-≈ˢ xs nil)
append-≈ˢ xs (consᴸ L⊑A eq) = consᴸ L⊑A (append-≈ˢ xs eq)
append-≈ˢ xs (cons₁ᴴ H⋤A eq) = cons₁ᴴ H⋤A (append-≈ˢ xs eq)
append-≈ˢ xs (cons₂ᴴ H⋤A eq) = cons₂ᴴ H⋤A (append-≈ˢ xs eq)

εˢ-simᴴ : ∀ {Σ₁ Σ₂ H} {m : Message H} -> H ⋤ A -> Σ₁ ⟶ Σ₂ ↑ m -> Σ₁ ≈ˢ Σ₂
εˢ-simᴴ H⋤A (R.step l n) = cons₁ᴴ H⋤A (append-≈ˢ (H⋤A ∷ []) refl-≈ˢ)
εˢ-simᴴ H⋤A (R.fork H n L⊑A) = cons₁ᴴ H⋤A (append-≈ˢ ((trans-⋢ L⊑A H⋤A) ∷ (H⋤A ∷ [])) refl-≈ˢ)
εˢ-simᴴ H⋤A (R.done l n) = cons₁ᴴ H⋤A refl-≈ˢ
εˢ-simᴴ H⋤A (R.skip l n) = cons₁ᴴ H⋤A (append-≈ˢ (H⋤A ∷ []) refl-≈ˢ)

-- open import Function

offset₁ : ∀ {s₁ s₂} -> s₁ ≈ˢ s₂ -> ℕ
offset₁ nil = 0
offset₁ (consᴸ L⊑A x) = 0
offset₁ (cons₁ᴴ H⋤A x) = suc (offset₁ x)
offset₁ (cons₂ᴴ H⋤A x) = offset₁ x

offset₂ : ∀ {s₁ s₂} -> s₁ ≈ˢ s₂ -> ℕ
offset₂ nil = 0
offset₂ (consᴸ L⊑A x) = 0
offset₂ (cons₁ᴴ H⋤A x) = offset₂ x
offset₂ (cons₂ᴴ H⋤A x) = suc (offset₂ x)

data _≈ˢ-⟨_,_⟩_ : State -> ℕ -> ℕ -> State -> Set where
  nil : [] ≈ˢ-⟨ 0 , 0 ⟩ []
  consᴸ : ∀ {L n s₁ s₂} -> (L⊑A : L ⊑ A) ->  s₁ ≈ˢ s₂ -> ((L , n) ∷ s₁) ≈ˢ-⟨ 0 , 0 ⟩ ((L , n) ∷ s₂)
  cons₁ᴴ : ∀ {H n s₁ s₂ i j} -> (H⋤A  : H ⋤ A) -> s₁ ≈ˢ-⟨ i , j ⟩ s₂ -> ((H , n) ∷ s₁) ≈ˢ-⟨ suc i , j ⟩ s₂
  cons₂ᴴ : ∀ {H n s₁ s₂ i j} -> (H⋤A  : H ⋤ A) -> s₁ ≈ˢ-⟨ i , j ⟩ s₂ -> s₁ ≈ˢ-⟨ i , suc j ⟩ ((H , n) ∷ s₂)

align : ∀ {s₁ s₂} -> (eq : s₁ ≈ˢ s₂) -> s₁ ≈ˢ-⟨ offset₁ eq , offset₂ eq ⟩ s₂
align nil = nil
align (consᴸ L⊑A x) = consᴸ L⊑A x
align (cons₁ᴴ H⋤A x) = cons₁ᴴ H⋤A (align x)
align (cons₂ᴴ H⋤A x) = cons₂ᴴ H⋤A (align x)

forget : ∀ {s₁ s₂ i j} -> s₁ ≈ˢ-⟨ i , j ⟩ s₂ -> s₁ ≈ˢ s₂
forget nil = nil
forget (consᴸ L⊑A x) = consᴸ L⊑A x
forget (cons₁ᴴ H⋤A x) = cons₁ᴴ H⋤A (forget x)
forget (cons₂ᴴ H⋤A x) = cons₂ᴴ H⋤A (forget x)

RR-is-NI : NIˢ RR
RR-is-NI = record
             { εˢ = εˢ
             ; _≈ˢ_ = _≈ˢ_
             ; ⌞_⌟ = ⌞_⌟
             ; ⌜_⌝ = ⌜_⌝
             ; εˢ-simᴸ = εˢ-simᴸ
             ; εˢ-simᴴ = εˢ-simᴴ
             ; _≈ˢ-⟨_,_⟩_ = _≈ˢ-⟨_,_⟩_
             ; offset₁ = offset₁
             ; offset₂ = offset₂
             ; align = align
             ; forget = forget
             }

squareˢ : ∀ {Σ₁ Σ₁' Σ₂ L e n n₁} -> L ⊑ A -> Σ₁ ≈ˢ-⟨ n₁ , 0 ⟩ Σ₂ -> Σ₁ ⟶ Σ₁' ↑ ⟪ L , n , e ⟫ ->
            ∃ (λ Σ₂' → Σ₂ ⟶ Σ₂' ↑ ⟪ L , n , e ⟫ )
squareˢ L⊑A (consᴸ L⊑A' x) (R.step l n) = , R.step l n
squareˢ L⊑A (cons₁ᴴ H⋤A eq) (R.step h n) = ⊥-elim (H⋤A L⊑A)
squareˢ L⊑A (consᴸ L⊑A' x) (R.fork l n p₁) = , (R.fork l n p₁)
squareˢ L⊑A (cons₁ᴴ H⋤A eq) (R.fork h n p) = ⊥-elim (H⋤A L⊑A)
squareˢ L⊑A (consᴸ L⊑A' x) (R.done l n) = , R.done l n
squareˢ L⊑A (cons₁ᴴ H⋤A eq) (R.done h n) = ⊥-elim (H⋤A L⊑A)
squareˢ L⊑A (consᴸ L⊑A₁ x) (R.skip L n) = , R.skip L n
squareˢ L⊑A (cons₁ᴴ H⋤A eq) (R.skip H n) = ⊥-elim (H⋤A L⊑A)

-- triangleˢ : ∀ {Σ₁ Σ₁' Σ₂ L e n n₁} -> L ⊑ A -> Σ₁ ≈ˢ-⟨ n₁ , 0 ⟩ Σ₂ -> Σ₁ ⟶ Σ₁' ↑ ⟪ L , n , e ⟫ ->
--             ∃ (λ Σ₂' → Σ₂ ⟶ Σ₂' ↑ ⟪ L , n , e ⟫ )

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
-- highˢ {s₁} {(h , n) ∷ s₁'} {s₂} {l} {e} {n'} {n₁} {n₂} p s e≠∙ (cons₂ᴴ  ¬p x) with lemma {n = n} ¬p p s e≠∙ x
-- ... | eq' = h , (n , aux)
--   where aux : (e : Event h) -> e ≢ ∙ -> HighStep h n e s₁ s₂ ((h , n) ∷ s₁') n₁ n₂
--         aux NoStep e≠∙₁ = high ¬p skip eq'
--         aux Step e≠∙₁ = high ¬p step eq'
--         aux Done e≠∙₁ = high ¬p done x
--         aux (Fork h₁ n₃ h⊑h₁) e≠∙₁ = high ¬p (fork h⊑h₁) (lemma₂ (trans-⋢ h⊑h₁ ¬p) ¬p p s e≠∙ x)
--         aux ∙ e≠∙₁ = ⊥-elim (e≠∙₁ refl)

-- open import Concurrent.Determinism (State) (_⟶_↑_) (determinism)
-- -- open import Concurrent.Security.NonInterference State _⟶_↑_ εˢ ε-sch-dist ε-sch-≡
