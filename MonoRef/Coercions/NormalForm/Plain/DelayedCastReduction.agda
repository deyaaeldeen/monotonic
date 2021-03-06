module MonoRef.Coercions.NormalForm.Plain.DelayedCastReduction where

open import MonoRef.Coercions.NormalForm.Plain.Compose
open import MonoRef.Coercions.NormalForm.Plain.Syntax
open import MonoRef.Dynamics.Efficient.Common.Value
  NormalFormCoercion InertNormalForm
open import MonoRef.Language.TargetWithoutBlame
  NormalFormCoercion InertNormalForm
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations

infix 3 _⟶ᵤᶜᵛ_

data _⟶ᵤᶜᵛ_ {Γ Σ} : ∀ {A} → Σ ∣ Γ ⊢ A → Σ ∣ Γ ⊢ A → Set where

  ι⋆ : ∀ {V : Σ ∣ Γ ⊢ ⋆} → SimpleValue V
      ---------------------------------
    → V < id⋆ > ⟶ᵤᶜᵛ V

  ι : ∀ {A} {V : Σ ∣ Γ ⊢ A} → (iA : Injectable A) → SimpleValue V
      ----------------------------------------------------------
    → V < final (middle (id iA)) > ⟶ᵤᶜᵛ V

  pair-simple : ∀ {A B A' B'}
         {V₁ : Σ ∣ Γ ⊢ A} {V₂ : Σ ∣ Γ ⊢ B}
         {c : NormalFormCoercion A A'} {d : NormalFormCoercion B B'}
    → SimpleValue V₁ → SimpleValue V₂
      --------------------------------------------------------------------
    → (V₁ `× V₂) < final (middle (prod c d)) > ⟶ᵤᶜᵛ (V₁ < c >) `× (V₂ < d >)

  pair-cast-left : ∀ {A B A' A'' B'}
         {V₁ : Σ ∣ Γ ⊢ A} {V₂ : Σ ∣ Γ ⊢ B}
         {c' : NormalFormCoercion A A'}
         {c : NormalFormCoercion A' A''} {d : NormalFormCoercion B B'}
    → SimpleValue V₁ → SimpleValue V₂
      ----------------------------------------------------------------------------------------
    → ((V₁ < c' >) `× V₂) < final (middle (prod c d)) > ⟶ᵤᶜᵛ (V₁ < compose c' c >) `× (V₂ < d >)

  pair-cast-right : ∀ {A B A' B' B''}
         {V₁ : Σ ∣ Γ ⊢ A} {V₂ : Σ ∣ Γ ⊢ B}
         {d' : NormalFormCoercion B B'}
         {c : NormalFormCoercion A A'} {d : NormalFormCoercion B' B''}
    → SimpleValue V₁ → SimpleValue V₂
      ----------------------------------------------------------------------------------------
    → (V₁ `× (V₂ < d' >)) < final (middle (prod c d)) > ⟶ᵤᶜᵛ (V₁ < c >) `× (V₂ < compose d' d >)

  pair-cast-both : ∀ {A B A' A'' B' B''}
         {V₁ : Σ ∣ Γ ⊢ A} {V₂ : Σ ∣ Γ ⊢ B}
         {c' : NormalFormCoercion A A'} {d' : NormalFormCoercion B B'}
         {c : NormalFormCoercion A' A''} {d : NormalFormCoercion B' B''}
    → SimpleValue V₁ → SimpleValue V₂
      ------------------------------------------------------------------------------------------------------------
    → ((V₁ < c' >) `× (V₂ < d' >)) < final (middle (prod c d)) > ⟶ᵤᶜᵛ (V₁ < compose c' c >) `× (V₂ < compose d' d >)

  `⊥ : ∀ {A B} {V : Σ ∣ Γ ⊢ A} → SimpleValue V
      ----------------------------------------------
    → V < final (middle (fail {A} {B})) > ⟶ᵤᶜᵛ error
