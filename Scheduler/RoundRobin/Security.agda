import Lattice as L

module Scheduler.RoundRobin.Security {𝓛 : L.Lattice} (A : L.Label 𝓛) where

open import Data.Product
open import Relation.Nullary

open L.Lattice 𝓛
import Scheduler.RoundRobin.Base as R
open R 𝓛
open import Scheduler.Base 𝓛
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
εˢ-simᴴ H⋤A (R.fork H n L⊑A) = cons₁ᴴ H⋤A (append-≈ˢ ((trans-⋤ L⊑A H⋤A) ∷ (H⋤A ∷ [])) refl-≈ˢ)
εˢ-simᴴ H⋤A (R.done l n) = cons₁ᴴ H⋤A refl-≈ˢ
εˢ-simᴴ H⋤A (R.skip l n) = cons₁ᴴ H⋤A (append-≈ˢ (H⋤A ∷ []) refl-≈ˢ)

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
  consᴸ : ∀ {L n Σ₁ Σ₂} -> (L⊑A : L ⊑ A) ->  Σ₁ ≈ˢ Σ₂ -> ((L , n) ∷ Σ₁) ≈ˢ-⟨ 0 , 0 ⟩ ((L , n) ∷ Σ₂)
  cons₁ᴴ : ∀ {H n Σ₁ Σ₂ i j} -> (H⋤A  : H ⋤ A) -> Σ₁ ≈ˢ-⟨ i , j ⟩ Σ₂ -> ((H , n) ∷ Σ₁) ≈ˢ-⟨ suc i , j ⟩ Σ₂
  cons₂ᴴ : ∀ {H n Σ₁ Σ₂ i j} -> (H⋤A  : H ⋤ A) -> Σ₁ ≈ˢ-⟨ i , j ⟩ Σ₂ -> Σ₁ ≈ˢ-⟨ i , suc j ⟩ ((H , n) ∷ Σ₂)

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

append-≈ : ∀ {Σ₁ Σ₂ Σ₃} ->  Σ₁ ≈ˢ Σ₂ -> All (λ x → proj₁ x ⊑ A) Σ₃ -> (Σ₁ ++ Σ₃) ≈ˢ (Σ₂ ++ Σ₃)
append-≈ eq [] = eq
append-≈ nil (px ∷ px₁) = consᴸ px (append-≈ nil px₁)
append-≈ (consᴸ L⊑A eq) px = consᴸ L⊑A (append-≈ eq px)
append-≈ (cons₁ᴴ H⋤A eq) px = cons₁ᴴ H⋤A (append-≈ eq px)
append-≈ (cons₂ᴴ H⋤A eq) px = cons₂ᴴ H⋤A (append-≈ eq px)

_++-≈_ : ∀ {Σ₁ Σ₂ Σ₃ Σ₄} ->  Σ₁ ≈ˢ Σ₂ -> Σ₃ ≈ˢ Σ₄ -> (Σ₁ ++ Σ₃) ≈ˢ (Σ₂ ++ Σ₄)
nil ++-≈ eq₂ = eq₂
consᴸ L⊑A eq₁ ++-≈ eq₂ = consᴸ L⊑A (eq₁ ++-≈ eq₂)
cons₁ᴴ H⋤A eq₁ ++-≈ eq₂ = cons₁ᴴ H⋤A (eq₁ ++-≈ eq₂)
cons₂ᴴ H⋤A eq₁ ++-≈ eq₂ = cons₂ᴴ H⋤A (eq₁ ++-≈ eq₂)

squareˢ : ∀ {Σ₁ Σ₁' Σ₂ L e n n₁} -> L ⊑ A -> Σ₁ ≈ˢ-⟨ n₁ , 0 ⟩ Σ₂ -> Σ₁ ⟶ Σ₁' ↑ ⟪ L , n , e ⟫ ->
            ∃ (λ Σ₂' → Σ₂ ⟶ Σ₂' ↑ ⟪ L , n , e ⟫ × Σ₁' ≈ˢ Σ₂')
squareˢ {_ ∷ Σ₁} L⊑A (consᴸ L⊑A₁ x) (R.step L n) = _ , (step L n , append-≈ x (L⊑A₁ ∷ []) )
squareˢ L⊑A (cons₁ᴴ H⋤A eq) (R.step H n) = ⊥-elim (H⋤A L⊑A)
squareˢ L⊑A (consᴸ L⊑A₁ x) (R.fork {h = h} L n p) with h ⊑? A
squareˢ L⊑A (consᴸ L⊑A₁ x) (R.fork L n p₁) | yes p =  _ , ( fork L n p₁ , append-≈ x (p ∷ (L⊑A₁ ∷ [])))
squareˢ L⊑A (consᴸ L⊑A₁ x) (R.fork L n p) | no ¬p = _ , (fork L n p) , x ++-≈ (refl-≈ˢ { (_ , _) ∷ (L , n) ∷ [] })
squareˢ L⊑A (cons₁ᴴ H⋤A eq) (R.fork H n p) = ⊥-elim (H⋤A L⊑A)
squareˢ L⊑A (consᴸ L⊑A₁ x) (R.done L n) = _ , ((done L n) , x )
squareˢ L⊑A (cons₁ᴴ H⋤A eq) (R.done H n) = ⊥-elim (H⋤A L⊑A)
squareˢ L⊑A (consᴸ L⊑A₁ x) (R.skip L n) = _ , (skip L n , append-≈ x (L⊑A₁ ∷ []) )
squareˢ L⊑A (cons₁ᴴ H⋤A eq) (R.skip H n) = ⊥-elim (H⋤A L⊑A)

append-≈ˢ′ : ∀ {Σ₁ Σ₁' Σ₂ Σ₃ n₁ n₂ L} {m : Message L} -> (L⊑A : L ⊑ A) -> Σ₁ ⟶ Σ₁' ↑ m ->
             Σ₁ ≈ˢ-⟨ n₁ , n₂ ⟩ Σ₂ -> All (λ x → proj₁ x ⋤ A) Σ₃ -> Σ₁ ≈ˢ-⟨ n₁ , n₂ ⟩ (Σ₂ ++ Σ₃)
append-≈ˢ′ L⊑A () nil ps
append-≈ˢ′ L⊑A s (consᴸ L⊑A₁ x) ps = consᴸ L⊑A₁ (append-≈ˢ ps x)
append-≈ˢ′ L⊑A (R.step l n) (cons₁ᴴ H⋤A eq) ps = ⊥-elim (H⋤A L⊑A)
append-≈ˢ′ L⊑A (R.fork L n p) (cons₁ᴴ H⋤A eq) ps = ⊥-elim (H⋤A L⊑A)
append-≈ˢ′ L⊑A (R.done l n) (cons₁ᴴ H⋤A eq) ps = ⊥-elim (H⋤A L⊑A)
append-≈ˢ′ L⊑A (R.skip l n) (cons₁ᴴ H⋤A eq) ps = ⊥-elim (H⋤A L⊑A)
append-≈ˢ′ L⊑A s (cons₂ᴴ H⋤A eq) ps = cons₂ᴴ H⋤A (append-≈ˢ′ L⊑A s eq ps)

triangleˢ : ∀ {Σ₁ Σ₁' Σ₂ L e n n₁ n₂} -> L ⊑ A -> Σ₁ ≈ˢ-⟨ n₁ , suc n₂ ⟩ Σ₂ -> Σ₁ ⟶ Σ₁' ↑ ⟪ L , n , e ⟫ ->
                 ∃ (λ H → ∃ (λ m → H ⋤ A × ∀ (e : Event H) → ∃ (λ Σ₂' → Σ₁ ≈ˢ-⟨ n₁ , n₂ ⟩ Σ₂' ×  Σ₂ ⟶ Σ₂' ↑ ⟪ H , m , e ⟫ )))
triangleˢ L⊑A (cons₁ᴴ H⋤A eq) (R.step l n) = ⊥-elim (H⋤A L⊑A)
triangleˢ L⊑A (cons₁ᴴ H⋤A eq) (R.fork L n p) = ⊥-elim (H⋤A L⊑A)
triangleˢ L⊑A (cons₁ᴴ H⋤A eq) (R.done l n) = ⊥-elim (H⋤A L⊑A)
triangleˢ L⊑A (cons₁ᴴ H⋤A eq) (R.skip l n) = ⊥-elim (H⋤A L⊑A)
triangleˢ {Σ₁} {n₁ = n₁} {n₂} L⊑A (cons₂ᴴ {H} {n} {Σ₂ = Σ₂} H⋤A eq) s = H , (n , (H⋤A , aux))
  where aux : (e : Event H) ->  ∃ (λ Σ₂' → Σ₁ ≈ˢ-⟨ n₁ , n₂ ⟩ Σ₂' × ((H , n) ∷ Σ₂) ⟶ Σ₂' ↑ ⟪ H , n , e ⟫)
        aux Skip = _ , (append-≈ˢ′ L⊑A s eq (H⋤A ∷ []) , (skip H n))
        aux Step = _ , (append-≈ˢ′ L⊑A s eq (H⋤A ∷ []) , (step H n))
        aux Done = _ , (eq , (done H n))
        aux (Fork h n₃ x) = _ , (append-≈ˢ′ L⊑A s eq (trans-⋤ x H⋤A ∷ H⋤A ∷ []) , fork H n x )

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
             ; id-≈ˢ = {!!}
             ; step-≈ˢ = {!!}
             ; fork-≈ˢ = {!!}
             ; squareˢ = squareˢ
             ; triangleˢ = triangleˢ
             }
