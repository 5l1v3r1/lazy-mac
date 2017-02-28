import Lattice as L

module Sequential.Determinism (𝓛 : L.Lattice) where

open import Types 𝓛
open import Sequential.Calculus 𝓛
open import Sequential.Semantics 𝓛

open import Data.Product
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality

open import Data.Empty

updateᴴ-≡ : ∀ {π π' τ l} {mt : Maybe (Term π' τ)} {Δ Δ₁ Δ₂ : Heap l π} {τ∈π : τ ∈⟨ l ⟩ π}
           -> Updateᴴ mt τ∈π Δ Δ₁ -> Updateᴴ mt τ∈π Δ Δ₂ -> Δ₁ ≡ Δ₂
updateᴴ-≡ here here = refl
updateᴴ-≡ (there a) (there b) rewrite updateᴴ-≡ a b = refl

-- My own heterogeneous equality for terms to ease unification
data _≅ᵀ_ {π τ} (t : Term π τ) : ∀ {π'} -> Term π' τ -> Set where
  refl : t ≅ᵀ t

memberᴴ-≅ᵀ : ∀ {τ l π π₁ π₂} {Δ : Heap l π} {t₁ : Term π₁ τ} {t₂ : Term π₂ τ} (τ∈π : τ ∈⟨ l ⟩ᴿ π) -> τ∈π ↦ t₁ ∈ᴴ Δ -> τ∈π ↦ t₂ ∈ᴴ Δ -> t₁ ≅ᵀ t₂
memberᴴ-≅ᵀ τ∈π x y = aux x y
  where aux : ∀ {τ l π π₁ π₂} {Δ : Heap l π} {t₁ : Term π₁ τ} {t₂ : Term π₂ τ} {τ∈π : τ ∈⟨ l ⟩ π}
                   -> Memberᴴ (just t₁) τ∈π Δ -> Memberᴴ (just t₂) τ∈π Δ -> t₁ ≅ᵀ t₂
        aux here here = refl
        aux (there x) (there y) with aux x y
        ... | refl = refl

determinism : ∀ {l τ} {s₁ s₂ s₃ : State l τ} -> s₁ ⇝ s₂ -> s₁ ⇝ s₃ -> s₂ ≡ s₃
determinism App₁ App₁ = refl
determinism App₁ (Var₂ τ∈π () uᴱ)
determinism (App₂ α∈π) (App₂ .α∈π) = refl
determinism (Var₁ τ∈π t∈Δ ¬val rᴴ) (Var₁ .τ∈π t∈Δ₁ ¬val₁ rᴴ₁) with memberᴴ-≅ᵀ τ∈π t∈Δ t∈Δ₁
... | refl rewrite updateᴴ-≡ rᴴ rᴴ₁ = refl
determinism (Var₁ τ∈π t∈Δ ¬val rᴴ) (Var₁' .τ∈π v∈Δ val) with memberᴴ-≅ᵀ τ∈π t∈Δ v∈Δ
... | refl = ⊥-elim (¬val val)
determinism (Var₁ τ∈π t∈Δ ¬val rᴴ) (Var₂ τ∈π₁ () uᴴ)
determinism (Var₁' τ∈π v∈Δ val) (Var₁ .τ∈π t∈Δ ¬val rᴴ) with memberᴴ-≅ᵀ τ∈π t∈Δ v∈Δ
... | refl = ⊥-elim (¬val val)
determinism (Var₁' τ∈π v∈Δ val) (Var₁' .τ∈π v∈Δ₁ val₁) with memberᴴ-≅ᵀ τ∈π v∈Δ v∈Δ₁
... | refl = refl
determinism (Var₁' τ∈π v∈Δ val) (Var₂ τ∈π₁ () uᴱ)
determinism (Var₂ τ∈π () uᴱ) App₁
determinism (Var₂ τ∈π () uᴱ) (Var₁ τ∈π₁ t∈Δ ¬val rᴱ)
determinism (Var₂ τ∈π () uᴱ) (Var₁' τ∈π₁ v∈Δ val₁)
determinism (Var₂ τ∈π val uᴱ) (Var₂ .τ∈π val₁ uᴱ₁) rewrite updateᴴ-≡ uᴱ uᴱ₁ = refl
determinism (Var₂ τ∈π () uᴱ) If
determinism (Var₂ τ∈π () uᴱ) Return
determinism (Var₂ τ∈π () uᴱ) Bind₁
determinism (Var₂ τ∈π () uᴱ) (Label' p)
determinism (Var₂ τ∈π () uᴱ) (Label'∙ p)
determinism (Var₂ τ∈π () uᴱ) (Unlabel₁ p)
determinism (Var₂ τ∈π () uᴱ) UnId₁
determinism (Var₂ τ∈π () uᴱ) (New₁ ¬var)
determinism (Var₂ τ∈π () uᴱ) (New∙₁ ¬var)
determinism (Var₂ τ∈π () uᴱ) Write₁
determinism (Var₂ τ∈π () uᴱ) Write∙₁
determinism (Var₂ τ∈π () uᴱ) Read₁
determinism If (Var₂ τ∈π () uᴱ)
determinism If If = refl
determinism IfTrue IfTrue = refl
determinism IfFalse IfFalse = refl
determinism Return (Var₂ τ∈π () uᴱ)
determinism Return Return = refl
determinism Bind₁ (Var₂ τ∈π () uᴱ)
determinism Bind₁ Bind₁ = refl
determinism Bind₂ Bind₂ = refl
determinism (Label' p) (Var₂ τ∈π () uᴱ)
determinism (Label' p) (Label' .p) = refl
determinism (Label'∙ p) (Var₂ τ∈π () uᴱ)
determinism (Label'∙ p) (Label'∙ .p) = refl
determinism (Unlabel₁ p) (Var₂ τ∈π () uᴱ)
determinism (Unlabel₁ p) (Unlabel₁ .p) = refl
determinism (Unlabel₂ p) (Unlabel₂ .p) = refl
determinism UnId₁ (Var₂ τ∈π () uᴱ)
determinism UnId₁ UnId₁ = refl
determinism UnId₂ UnId₂ = refl
determinism (New₁ ¬var) (Var₂ τ∈π () uᴱ)
determinism (New₁ ¬var) (New₁ ¬var₁) = refl
determinism (New∙₁ ¬var) (Var₂ τ∈π () uᴱ)
determinism (New∙₁ ¬var) (New∙₁ ¬var₁) = refl
determinism Write₁ (Var₂ τ∈π () uᴱ)
determinism Write₁ Write₁ = refl
determinism Write∙₁ (Var₂ τ∈π () uᴱ)
determinism Write∙₁ Write∙₁ = refl
determinism Read₁ (Var₂ τ∈π () uᴱ)
determinism Read₁ Read₁ = refl
determinism Hole₁ Hole₁ = refl
determinism Hole₂ Hole₂ = refl

memberᴱ-≅ : ∀ {l ls π₁ π₂} {Γ : Heaps ls} {Δ₁ : Heap l π₁} {Δ₂ : Heap l π₂} ->
            l ↦ ⟨ Δ₁ ⟩ ∈ᴱ Γ -> l ↦ ⟨ Δ₂ ⟩ ∈ᴱ Γ -> Δ₁ ≅ Δ₂
memberᴱ-≅ here here = refl
memberᴱ-≅ here (there {u = u} b) = ⊥-elim (∈-not-unique (memberᴱ-∈ b) u)
memberᴱ-≅ (there {u = u} a) here = ⊥-elim (∈-not-unique (memberᴱ-∈ a) u)
memberᴱ-≅ (there a) (there b) = memberᴱ-≅ a b

updateᴱ-≡ : ∀ {l ls π} {Γ Γ₁ Γ₂ : Heaps ls} {Δ : Heap l π} -> Γ₁ ≔ Γ [ l ↦ ⟨ Δ ⟩ ]ᴱ -> Γ₂ ≔ Γ [ l ↦ ⟨ Δ ⟩ ]ᴱ -> Γ₁ ≡ Γ₂
updateᴱ-≡ here here = refl
updateᴱ-≡ here (there {u = u} b) = ⊥-elim (∈-not-unique (updateᴱ-∈ b) u)
updateᴱ-≡ (there {u = u} a) here = ⊥-elim (∈-not-unique (updateᴱ-∈ a) u)
updateᴱ-≡ (there a) (there b) rewrite updateᴱ-≡ a b = refl


memberˢ-≅ : ∀ {l ls} {Ms : Memories ls} {M₁ : Memory l} {M₂ : Memory l} ->
            l ↦ M₁ ∈ˢ Ms -> l ↦ M₂ ∈ˢ Ms -> M₁ ≡ M₂
memberˢ-≅ here here = refl
memberˢ-≅ here (there {u = u} b) = ⊥-elim (∈-not-unique (memberˢ-∈  b) u)
memberˢ-≅ (there {u = u} a) here = ⊥-elim (∈-not-unique (memberˢ-∈  a) u)
memberˢ-≅ (there a) (there b) = memberˢ-≅ a b

updateˢ-≡ : ∀ {l ls} {Ms Ms₁ Ms₂ : Memories ls} {M : Memory l} -> Ms₁ ≔ Ms [ l ↦ M ]ˢ -> Ms₂ ≔ Ms [ l ↦ M ]ˢ -> Ms₁ ≡ Ms₂
updateˢ-≡ here here = refl
updateˢ-≡ here (there {u = u} b) = ⊥-elim (∈-not-unique (updateˢ-∈ b) u)
updateˢ-≡ (there {u = u} a) here = ⊥-elim (∈-not-unique (updateˢ-∈ a) u)
updateˢ-≡ (there a) (there b) rewrite updateˢ-≡ a b = refl

updateᴹ-≡ : ∀ {l n τ} {M₁ M₂ M₃ : Memory l} {c : Cell l τ} -> M₂ ≔ M₁ [ n ↦ c ]ᴹ -> M₃ ≔ M₁ [ n ↦ c ]ᴹ -> M₂ ≡ M₃
updateᴹ-≡ here here = refl
updateᴹ-≡ (there x) (there y) rewrite updateᴹ-≡ x y = refl

memberᴹ-≡ : ∀ {l n τ} {M : Memory l} {c₁ c₂ : Cell l τ} -> n ↦ c₁ ∈ᴹ M -> n ↦ c₂ ∈ᴹ M -> c₁ ≡ c₂
memberᴹ-≡ here here = refl
memberᴹ-≡ (there x) (there y) rewrite memberᴹ-≡ x y = refl

determinismᴾ : ∀ {l ls τ} {p₁ p₂ p₃ : Program l ls τ} -> p₁ ⟼ p₂ -> p₁ ⟼ p₃ -> p₂ ≡ p₃
determinismᴾ (Pure l∈Γ step uᴴ) (Pure l∈Γ₁ step₁ uᴴ₁) with memberᴱ-≅ l∈Γ l∈Γ₁
... | refl with determinism step step₁
... | refl rewrite updateᴱ-≡ uᴴ uᴴ₁ = refl
determinismᴾ (Pure l∈Γ (Var₂ τ∈π () uˢ) uᴴ) (New H∈Γ uᴴ₁)
determinismᴾ (Pure l∈Γ (New₁ ¬var) uᴴ) (New H∈Γ uᴴ₁) = ⊥-elim (¬var (Var ⟪ _ ⟫))
determinismᴾ (Pure l∈Γ (Var₂ τ∈π () uˢ) uᴴ) New∙
determinismᴾ (Pure l∈Γ (New∙₁ ¬var) uᴴ) New∙ = ⊥-elim (¬var (Var ⟪ _ ⟫))
determinismᴾ (Pure l∈Γ () uᴴ) (Write₂ H∈Γ uᴹ uᴴ₁)
determinismᴾ (Pure l∈Γ () uᴴ) (Writeᴰ₂ H∈Γ uᴹ uᴴ₁)
determinismᴾ (Pure l∈Γ () uᴴ) Write∙₂
determinismᴾ (Pure l∈Γ () uᴴ) (Read₂ l∈Γ₁ n∈M)
determinismᴾ (Pure l∈Γ () uᴴ) (Readᴰ₂ L∈Γ t∈M)
determinismᴾ (New H∈Γ uᴴ) (Pure l∈Γ (Var₂ τ∈π () uˢ) uᴴ₁)
determinismᴾ (New H∈Γ uᴴ) (Pure l∈Γ (New₁ ¬var) uᴴ₁) = ⊥-elim (¬var (Var ⟪ _ ⟫))
determinismᴾ (New H∈Γ uᴴ) (New H∈Γ₁ uᴴ₁) with memberˢ-≅ H∈Γ H∈Γ₁
... | refl rewrite updateˢ-≡ uᴴ uᴴ₁ = refl
determinismᴾ New∙ (Pure l∈Γ (Var₂ τ∈π () uˢ) uᴴ)
determinismᴾ New∙ (Pure l∈Γ (New∙₁ ¬var) uᴴ) = ⊥-elim (¬var (Var ⟪ _ ⟫))
determinismᴾ New∙ New∙ = refl
determinismᴾ (Write₂ H∈Γ uᴹ uᴴ) (Pure l∈Γ () uᴴ₁)
determinismᴾ (Write₂ H∈Γ uᴹ uᴴ) (Write₂ H∈Γ₁ uᴹ₁ uᴴ₁) with memberˢ-≅ H∈Γ H∈Γ₁
... | refl rewrite updateᴹ-≡ uᴹ uᴹ₁ | updateˢ-≡ uᴴ uᴴ₁ = refl
determinismᴾ (Writeᴰ₂ H∈Γ uᴹ uᴴ) (Pure l∈Γ () uᴴ₁)
determinismᴾ (Writeᴰ₂ H∈Γ uᴹ uᴴ) (Writeᴰ₂ H∈Γ₁ uᴹ₁ uᴴ₁) with memberˢ-≅ H∈Γ H∈Γ₁
... | refl rewrite updateᴹ-≡ uᴹ uᴹ₁ | updateˢ-≡ uᴴ uᴴ₁ = refl
determinismᴾ Write∙₂ (Pure l∈Γ () uᴴ)
determinismᴾ Write∙₂ Write∙₂ = refl
determinismᴾ (Read₂ l∈Γ n∈M) (Pure l∈Γ₁ () uᴴ)
determinismᴾ (Read₂ l∈Γ n∈M) (Read₂ l∈Γ₁ n∈M₁) with memberˢ-≅ l∈Γ l∈Γ₁
... | refl with memberᴹ-≡ n∈M n∈M₁
... | refl = refl
determinismᴾ (Readᴰ₂ L∈Γ t∈M) (Pure l∈Γ () uᴴ)
determinismᴾ (Readᴰ₂ L∈Γ n∈M) (Readᴰ₂ L∈Γ₁ n∈M₁) with memberˢ-≅ L∈Γ L∈Γ₁
... | refl with memberᴹ-≡ n∈M n∈M₁
... | refl = refl
determinismᴾ (Pure l∈Γ (Var₂ τ∈π () uᴴ₁) uᴴ) (DeepDup₁ ¬var l∈Γ₁ uᴱ)
determinismᴾ (Pure l∈Γ (Var₂ τ∈π () uᴴ₁) uᴴ) (DeepDup₂ τ∈π₁ L∈Γ t∈Δ l∈Γ₁ uᴱ)
determinismᴾ (DeepDup₁ ¬var l∈Γ uᴱ) (Pure l∈Γ₁ (Var₂ τ∈π () uᴴ) uᴴ₁)
determinismᴾ (DeepDup₁ ¬var l∈Γ uᴱ) (DeepDup₁ ¬var₁ l∈Γ₁ uᴱ₁) with memberᴱ-≅ l∈Γ l∈Γ₁
... | refl rewrite updateᴱ-≡ uᴱ uᴱ₁ = refl
determinismᴾ (DeepDup₁ ¬var l∈Γ uᴱ) (DeepDup₂ τ∈π L∈Γ t∈Δ l∈Γ₁ uᴱ₁) with memberᴱ-≅ l∈Γ l∈Γ₁
... | refl = ⊥-elim (¬var (Var τ∈π))
determinismᴾ (DeepDup₂ τ∈π L∈Γ t∈Δ l∈Γ uᴱ) (Pure l∈Γ₁ (Var₂ τ∈π₁ () uᴴ) uᴴ₁)
determinismᴾ (DeepDup₂ τ∈π L∈Γ t∈Δ l∈Γ uᴱ) (DeepDup₁ ¬var l∈Γ₁ uᴱ₁) with memberᴱ-≅ l∈Γ l∈Γ₁
... | refl = ⊥-elim (¬var (Var τ∈π))
determinismᴾ (DeepDup₂ τ∈π L∈Γ t∈Δ l∈Γ uᴱ) (DeepDup₂ .τ∈π L∈Γ₁ t∈Δ₁ l∈Γ₁ uᴱ₁) with memberᴱ-≅ L∈Γ L∈Γ₁
... | refl with memberᴱ-≅ l∈Γ l∈Γ₁
... | refl with memberᴴ-≅ᵀ τ∈π t∈Δ t∈Δ₁
... | refl rewrite updateᴱ-≡ uᴱ uᴱ₁ = refl
determinismᴾ Hole Hole = refl
