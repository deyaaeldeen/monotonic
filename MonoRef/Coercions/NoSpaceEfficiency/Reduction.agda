module MonoRef.Coercions.NoSpaceEfficiency.Reduction where

open import Relation.Nullary using (¬_)

open import MonoRef.Coercions.NoSpaceEfficiency.Syntax
open import MonoRef.Dynamics.Substitution
open import MonoRef.Language.Surface
open import MonoRef.Language.TargetWithoutBlameNoSE
open import MonoRef.Static.Context
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations

infix 3 _⟶ᵤ_


data _⟶ᵤ_ {Γ Σ} : ∀ {A} → Σ ∣ Γ ⊢ A → Σ ∣ Γ ⊢ A → Set where

  ι : ∀ {A} {V : Σ ∣ Γ ⊢ A}
    → Value V
      -----------------------------
    → V < ι > ⟶ᵤ V

  !?₁ : ∀ {A B} {V : Σ ∣ Γ ⊢ A}
    → Value V
    → A ∼ B
      -----------------------------
    → V < A ! > < B `? > ⟶ᵤ V < coerce A B >

  !?₂ : ∀ {A B} {V : Σ ∣ Γ ⊢ A}
    → Value V
    → ¬ A ∼ B
      -----------------------------
    → V < A ! > < B `? > ⟶ᵤ error

  ⇒ : ∀ {A B A' B'}
        {V : Σ ∣ Γ ⊢ A ⇒ B}
        {c₁ : A' ⟹ A}
        {c₂ : B ⟹ B'}
    → Value V
      -------------------------------
    → V < c₁ ⇒ c₂ > ⟶ᵤ ƛₚ V (c₁ ⇒ c₂)

  `× : ∀ {A B A' B'}
         {V₁ : Σ ∣ Γ ⊢ A}
         {V₂ : Σ ∣ Γ ⊢ B}
         {c₁ : A ⟹ A'}
         {c₂ : B ⟹ B'}
    → Value V₁
    → Value V₂
      -----------------------------
    → (V₁ `× V₂) < c₁ `× c₂ > ⟶ᵤ ((V₁ < c₁ >) `× (V₂ < c₂ >))

  ▹ : ∀ {A B C}
        {V : Σ ∣ Γ ⊢ A}
        {c₁ : A ⟹ B}
        {c₂ : B ⟹ C}
    → Value V
    → V < c₁ ▹ c₂ > ⟶ᵤ V < c₁ > < c₂ >

  `⊥ : ∀ {A B} {V : Σ ∣ Γ ⊢ A}
    → Value V
      -----------------------------
    → V < `⊥ {B = B} > ⟶ᵤ error
