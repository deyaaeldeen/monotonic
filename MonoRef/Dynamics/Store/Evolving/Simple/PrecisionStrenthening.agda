open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Evolving.Simple.PrecisionStrenthening
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import MonoRef.Dynamics.Simple.Common.Value
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.Simple.DelayedCast
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Simple.PrecisionStrenthening
  _⟹_ Inert public
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Types.Relations


typeprecise-strenthen-cv : ∀ {Σ Σ' Γ A} {e : Σ ∣ Γ ⊢ A}
  → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
  → DelayedCast e
  → DelayedCast (typeprecise-strenthen-expr Σ'⊑ₕΣ e)
typeprecise-strenthen-cv Σ'⊑ₕΣ (v⇑ x) = v⇑ typeprecise-strenthen-val Σ'⊑ₕΣ x
typeprecise-strenthen-cv Σ'⊑ₕΣ (cast-val cv c) =
  cast-val (typeprecise-strenthen-cv Σ'⊑ₕΣ cv) c
typeprecise-strenthen-cv Σ'⊑ₕΣ (cv-pair cv cv₁) =
  cv-pair (typeprecise-strenthen-cv Σ'⊑ₕΣ cv)
          (typeprecise-strenthen-cv Σ'⊑ₕΣ cv₁)
