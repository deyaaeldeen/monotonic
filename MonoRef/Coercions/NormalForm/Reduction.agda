module MonoRef.Coercions.NormalForm.Reduction where

open import MonoRef.Coercions.NormalForm.Compose
open import MonoRef.Coercions.NormalForm.Syntax
open import MonoRef.Dynamics.Efficient.Value
  NormalFormCoercion InertNormalForm
open import MonoRef.Language.TargetWithoutBlame
  NormalFormCoercion InertNormalForm


infix 3 _⟶ᵤ_

data _⟶ᵤ_ {Γ Σ} : ∀ {A} → Σ ∣ Γ ⊢ A → Σ ∣ Γ ⊢ A → Set where

  ι : ∀ {A} {V : Σ ∣ Γ ⊢ A} → Value V
      ------------------------------
    → V < final (middle id) > ⟶ᵤ V

  `× : ∀ {A B A' B'}
         {V₁ : Σ ∣ Γ ⊢ A} {V₂ : Σ ∣ Γ ⊢ B}
         {c : NormalFormCoercion A A'} {d : NormalFormCoercion B B'}
    → Value V₁ → Value V₂
      --------------------------------------------------------------------
    → (V₁ `× V₂) < final (middle (prod c d)) > ⟶ᵤ (V₁ < c >) `× (V₂ < d >)

  compose-crcn : ∀ {A B C} {V : Σ ∣ Γ ⊢ A}
    → Value V
    → (c : NormalFormCoercion A B)
    → (d : NormalFormCoercion B C)
      -----------------------------------
    → V < c > < d > ⟶ᵤ V < compose c d >

  `⊥ : ∀ {A B} {V : Σ ∣ Γ ⊢ A} → Value V
      ------------------------------------
    → V < final (fail {B = B}) > ⟶ᵤ error
