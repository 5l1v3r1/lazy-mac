import Lattice as L

-- A is the security level of the attacker
module Sequential.Security.Simulation (𝓛 : L.Lattice) (A : L.Label 𝓛) where

open import Types 𝓛
open import Sequential.Calculus 𝓛
open import Sequential.Semantics 𝓛
open import Sequential.Security.Erasure 𝓛 A

open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding (subst ; [_])
open import Relation.Nullary
open import Data.Empty

-- Simulation Property
ε-sim : ∀ {l τ} {s₁ s₂ : State l τ} (x : Dec (l ⊑ A)) -> s₁ ⇝ s₂ -> ε x s₁ ⇝ ε x s₂
-- High-Computations
ε-sim (no x) s = Hole₁
-- Low-Computations
ε-sim (yes y) App₁ = App₁
ε-sim (yes y) (App₂ α∈π) = App₂ α∈π
ε-sim (yes y) (Var₁ τ∈π t∈Δ ¬val rᴱ) = Var₁ τ∈π (memberᴱ τ∈π t∈Δ) (εᵀ¬Val ¬val) (updateᴱ rᴱ)
ε-sim (yes y) (Var₁' τ∈π v∈Δ val) = Var₁' τ∈π (memberᴱ τ∈π v∈Δ) (εᵀ-Val val)
ε-sim (yes y) (Var₂ τ∈π val uᴱ) = Var₂ τ∈π (εᵀ-Val val) (updateᴱ uᴱ)
ε-sim (yes y) If = If
ε-sim (yes y) IfTrue = IfTrue
ε-sim (yes y) IfFalse = IfFalse
ε-sim (yes y) Return = Return
ε-sim (yes y) Bind₁ = Bind₁
ε-sim (yes y) Bind₂ = Bind₂
ε-sim (yes y) (Label' {h = H} p) with H ⊑? A
ε-sim (yes y) (Label' p₁) | yes p = Label' p₁
ε-sim (yes y) (Label' p) | no ¬p = Label'∙ p
ε-sim (yes y) (Label'∙ {h = H} p) with H ⊑? A
ε-sim (yes y) (Label'∙ p₁) | yes p = Label'∙ p₁
ε-sim (yes y) (Label'∙ p) | no ¬p = Label'∙ p
ε-sim (yes y) (Unlabel₁ p) = Unlabel₁ p
ε-sim (yes y) (Unlabel₂ {l' = L} p) with L ⊑? A
ε-sim (yes y) (Unlabel₂ p₁) | yes p = Unlabel₂ p₁
ε-sim (yes y) (Unlabel₂ p) | no ¬p = ⊥-elim (¬p (trans-⊑ p y))
ε-sim (yes y) UnId₁ = UnId₁
ε-sim (yes y) UnId₂ = UnId₂
ε-sim (yes y) (New₁ {H = H} ¬var) with H ⊑? A
ε-sim (yes y) (New₁ ¬var) | yes p = New₁ (εᵀ¬Var ¬var)
ε-sim (yes y) (New₁ ¬var) | no ¬p = New∙₁ (εᵀ¬Var ¬var)
ε-sim (yes y) (New∙₁ ¬var) = New∙₁ (εᵀ¬Var ¬var)
ε-sim (yes y) Read₁ = Read₁
ε-sim (yes y) (Write₁ {H = H}) with H ⊑? A
ε-sim (yes y) Write₁ | yes p = Write₁
ε-sim (yes y) Write₁ | no ¬p = Write∙₁
ε-sim (yes y) Write∙₁ = Write∙₁
ε-sim (yes y) Hole₁ = Hole₁
ε-sim (yes y) Hole₂ = Hole₂

open import Data.Product using (proj₁ ; proj₂)

ε₁ᴾ-sim : ∀ {l ls τ} {p₁ p₂ : Program l ls τ} (x : Dec (l ⊑ A)) -> p₁ ⟼ p₂ -> ε₁ᴾ x p₁ ⟼ ε₁ᴾ x p₂
ε₁ᴾ-sim (yes p) (Pure l∈Γ step uᴴ) = Pure (memberᴴ p l∈Γ) (ε-sim (yes p) step) (updateᴴ p uᴴ)
ε₁ᴾ-sim (yes p) (New {H = H} H∈Γ uᴴ) with H ⊑? A
ε₁ᴾ-sim (yes p₁) (New H∈Γ uᴴ) | yes p = New (memberᴹ p H∈Γ) (updateᴹ p uᴴ)
ε₁ᴾ-sim (yes p) (New {M = M} {τ∈π = ⟪ τ∈π ⟫} {l⊑H = l⊑H}  H∈Γ uᴴ) | no ¬p
  rewrite writeᴹ∙-≡ ¬p H∈Γ uᴴ = New∙
ε₁ᴾ-sim (yes p) (New∙ {H = H}) with H ⊑? A
ε₁ᴾ-sim (yes p₁) New∙ | yes p = New∙
ε₁ᴾ-sim (yes p) New∙ | no ¬p = New∙
ε₁ᴾ-sim (yes p) (Write₂ {H = H} H∈Γ uᴹ uˢ) with H ⊑? A
ε₁ᴾ-sim (yes p₁) (Write₂ H∈Γ uᴹ uˢ) | yes p = Write₂ (memberᴹ p H∈Γ) uᴹ (updateᴹ p uˢ)
ε₁ᴾ-sim (yes p) (Write₂ {l⊑H = l⊑H} H∈Γ uᴹ uˢ) | no ¬p
  rewrite writeᴹ∙-≡ ¬p H∈Γ uˢ = Write∙₂
ε₁ᴾ-sim (yes p) (Writeᴰ₂ {H = H} H∈Γ uᴹ uˢ) with H ⊑? A
ε₁ᴾ-sim (yes p₁) (Writeᴰ₂ H∈Γ uᴹ uˢ) | yes p = Writeᴰ₂ (memberᴹ p H∈Γ) uᴹ (updateᴹ p uˢ)
ε₁ᴾ-sim (yes p) (Writeᴰ₂ {l⊑H = l⊑H} H∈Γ uᴹ uˢ) | no ¬p
  rewrite writeᴹ∙-≡ ¬p H∈Γ uˢ = Write∙₂
ε₁ᴾ-sim (yes p) (Write∙₂ {H = H}) with H ⊑? A
ε₁ᴾ-sim (yes p₁) Write∙₂ | yes p = Write∙₂
ε₁ᴾ-sim (yes p) Write∙₂ | no ¬p = Write∙₂
ε₁ᴾ-sim {l} (yes p) (Read₂ l∈Γ n∈M) with l ⊑? A
ε₁ᴾ-sim (yes p₁) (Read₂ l∈Γ n∈M) | yes p = Read₂ (memberᴹ p₁ l∈Γ) n∈M
ε₁ᴾ-sim (yes p) (Read₂ l∈Γ n∈M) | no ¬p = ⊥-elim (¬p p)
ε₁ᴾ-sim {l} (yes p') (Readᴰ₂ {L = L} {L⊑l = L⊑l} L∈Γ n∈M) with L ⊑? A
... | yes p = Readᴰ₂ (memberᴹ p L∈Γ) n∈M
... | no ¬p = ⊥-elim (¬p (trans-⊑ L⊑l p'))
ε₁ᴾ-sim (yes p) (DeepDup₁ ¬var l∈Γ uᴱ) = DeepDup₁ (εᵀ¬Var ¬var) (memberᴴ p l∈Γ) (updateᴴ p uᴱ)
ε₁ᴾ-sim (yes l⊑A) (DeepDup₂ {L⊑l = L⊑l} τ∈π L∈Γ t∈Δ l∈Γ uᴱ)
  = DeepDup₂ {L⊑l = L⊑l} τ∈π (memberᴴ (trans-⊑ L⊑l l⊑A) L∈Γ) (memberᴱ τ∈π t∈Δ) (memberᴴ l⊑A l∈Γ) (updateᴴ l⊑A uᴱ)
ε₁ᴾ-sim (yes p) Hole = Hole
ε₁ᴾ-sim (no l⋤A) (Pure l∈Γ step uᴴ) rewrite writeᴴ∙-≡ l⋤A l∈Γ uᴴ = Hole
ε₁ᴾ-sim (no H⋤A) (New {l⊑H = l⊑H} H∈Γ uᴴ) rewrite writeᴹ∙-≡ (trans-⋤ l⊑H H⋤A) H∈Γ uᴴ = Hole
ε₁ᴾ-sim (no l⋤A) New∙ = Hole
ε₁ᴾ-sim (no H⋤A) (Write₂ {l⊑H = l⊑H} H∈Γ uᴹ uˢ) rewrite writeᴹ∙-≡ (trans-⋤ l⊑H H⋤A) H∈Γ uˢ = Hole
ε₁ᴾ-sim (no H⋤A) (Writeᴰ₂ {l⊑H = l⊑H} H∈Γ uᴹ uˢ) rewrite writeᴹ∙-≡ (trans-⋤ l⊑H H⋤A) H∈Γ uˢ = Hole
ε₁ᴾ-sim (no l⋤A) Write∙₂ = Hole
ε₁ᴾ-sim (no l⋤A) (Read₂ l∈Γ n∈M) = Hole
ε₁ᴾ-sim (no l⋤A) (Readᴰ₂ L∈Γ n∈M) = Hole
ε₁ᴾ-sim (no l⋤A) (DeepDup₁ ¬var l∈Γ uᴱ) with writeᴴ∙-≡ l⋤A l∈Γ uᴱ
... | eq rewrite eq = Hole
ε₁ᴾ-sim (no l⋤A) (DeepDup₂ τ∈π L∈Γ t∈Δ l∈Γ uᴱ) with writeᴴ∙-≡ l⋤A l∈Γ uᴱ
... | eq rewrite eq = Hole
ε₁ᴾ-sim (no l⋤A) Hole = Hole

εᴾ : ∀ {l ls τ} -> Program l ls τ -> Program l ls τ
εᴾ {l} = ε₁ᴾ (l ⊑? A)

εᴾ-sim : ∀ {l ls τ} {p₁ p₂ : Program l ls τ} -> p₁ ⟼ p₂ -> εᴾ p₁ ⟼ εᴾ p₂
εᴾ-sim {l} = ε₁ᴾ-sim (l ⊑? A)
