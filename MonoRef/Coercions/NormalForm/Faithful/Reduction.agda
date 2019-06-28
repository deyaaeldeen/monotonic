module MonoRef.Coercions.NormalForm.Faithful.Reduction where

open import MonoRef.Coercions.NormalForm.Faithful.Compose
open import MonoRef.Coercions.NormalForm.Faithful.Syntax
open import MonoRef.Dynamics.Efficient.Value
  NormalFormCoercion InertNormalForm
open import MonoRef.Language.TargetWithoutBlame
  NormalFormCoercion InertNormalForm


infix 3 _⟶ᵤ_

data _⟶ᵤ_ {Γ Σ} : ∀ {A} → Σ ∣ Γ ⊢ A → Σ ∣ Γ ⊢ A → Set where

  ι : ∀ {A} {V : Σ ∣ Γ ⊢ A} → SimpleValue V
      ------------------------------
    → V < final (middle id) > ⟶ᵤ V

  `× : ∀ {A B A' B'}
         {V₁ : Σ ∣ Γ ⊢ A} {V₂ : Σ ∣ Γ ⊢ B}
         {c : NormalFormCoercion A A'} {d : NormalFormCoercion B B'}
    → Value V₁ → Value V₂
      --------------------------------------------------------------------
    → (V₁ `× V₂) < final (middle (prod c d)) > ⟶ᵤ (V₁ < c >) `× (V₂ < d >)

  compose-casts : ∀ {A B C} {M : Σ ∣ Γ ⊢ A} {c : NormalFormCoercion A B} {d : NormalFormCoercion B C}
      -----------------------------------
    → M < c > < d > ⟶ᵤ M < compose c d >

  `⊥ : ∀ {A B} {V : Σ ∣ Γ ⊢ A} → SimpleValue V
      ------------------------------------
    → V < final (fail {B = B}) > ⟶ᵤ error

  ⊥ₘ : ∀ {A B} {V : Σ ∣ Γ ⊢ A} → SimpleValue V
      ------------------------------------
    → V < final (middle (fail {B = B})) > ⟶ᵤ error
