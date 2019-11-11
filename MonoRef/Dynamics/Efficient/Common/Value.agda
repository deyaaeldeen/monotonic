open import MonoRef.Static.Types

module MonoRef.Dynamics.Efficient.Common.Value
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.List.Membership.Propositional using (_∈_)

open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Types.Relations
open import MonoRef.Static.Context


data Value : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set

data SimpleValue : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set where

  V-ƛ : ∀ {Σ Γ A B}
    → (N : Σ ∣ Γ , A ⊢ B)
      ------------------
    → SimpleValue (ƛ N)

  V-zero : ∀ {Γ Σ}
      -----------------------------------
    → SimpleValue (`zero {Σ = Σ} {Γ = Γ})

  V-suc : ∀ {Σ Γ} {V : Σ ∣ Γ ⊢ `ℕ}
    → Value V
      --------------------
    → SimpleValue (`suc V)

  V-unit : ∀ {Σ Γ}
      ----------------------------------
    → SimpleValue (unit {Σ = Σ} {Γ = Γ})

  V-addr : ∀ {A B Σ Γ}
    → (x : A ∈ Σ)
    → (y : A ⊑ B)
      ------------------------------
    → SimpleValue (addr {Γ = Γ} x y)

  V-pair : ∀ {Σ Γ A B}
           {V₁ : Σ ∣ Γ ⊢ A} {V₂ : Σ ∣ Γ ⊢ B}
    → Value V₁
    → Value V₂
      ---------------------
    → SimpleValue (V₁ `× V₂)

data Value where

  S-Val : ∀ {Σ Γ A} {V : Σ ∣ Γ ⊢ A}
    → SimpleValue V
      -------------
    → Value V

  V-cast : ∀ {Σ Γ A B} {V : Σ ∣ Γ ⊢ A} {c : A ⟹ B}
    → SimpleValue V
    → Inert c
      ---------------
    → Value (V < c >)
