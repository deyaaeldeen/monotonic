module MonoRef.Coercions.Annotated.Reduction where

open import Relation.Nullary using (¬_)

open import MonoRef.Coercions.Annotated.Syntax
open import MonoRef.Dynamics.Simple.Common.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Types.Relations


infix 3 _⟶ᵤ_

data _⟶ᵤ_ {Γ Σ} : ∀ {A} → Σ ∣ Γ ⊢ A → Σ ∣ Γ ⊢ A → Set where

  ι : ∀ {A} {V : Σ ∣ Γ ⊢ A} → Value V
      ------------------------------
    → V < ι A > ⟶ᵤ V

  !? : ∀ {A B} {V : Σ ∣ Γ ⊢ A} {iA : Injectable A} {iB : Injectable B}
    → Value V
      -----------------------------------------------------------------------------------------------
    → V < inj iA > < prj iB > ⟶ᵤ V < make-coercion (injectable-to-type iA) (injectable-to-type iB) >

  `× : ∀ {A B A' B'} {V₁ : Σ ∣ Γ ⊢ A} {V₂ : Σ ∣ Γ ⊢ B}
         {c₁ : A ⟹ A'} {c₂ : B ⟹ B'}
    → Value V₁ → Value V₂
      ----------------------------------------------------
    → (V₁ `× V₂) < c₁ `× c₂ > ⟶ᵤ (V₁ < c₁ >) `× (V₂ < c₂ >)

  `⊥ : ∀ {A B} {V : Σ ∣ Γ ⊢ A}
    → Value V → (A≁B : ¬ A ∼ B)
      --------------------------
    → V < `⊥ A B A≁B > ⟶ᵤ error
