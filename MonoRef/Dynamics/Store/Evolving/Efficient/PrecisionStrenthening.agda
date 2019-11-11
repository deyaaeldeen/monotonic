open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Evolving.Efficient.PrecisionStrenthening
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import MonoRef.Dynamics.Store.Evolving.Efficient.DelayedCast
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Efficient.PrecisionStrenthening
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert


typeprecise-strenthen-cv : ∀ {Σ Σ' Γ A} {e : Σ ∣ Γ ⊢ A} → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
  → DelayedCast e → DelayedCast (typeprecise-strenthen-expr Σ'⊑ₕΣ e)
typeprecise-strenthen-cv Σ'⊑ₕΣ (v⇑ x) = v⇑ typeprecise-strenthen-val Σ'⊑ₕΣ x
typeprecise-strenthen-cv Σ'⊑ₕΣ (cast-val v c) =
  cast-val (typeprecise-strenthen-sval Σ'⊑ₕΣ v) c
typeprecise-strenthen-cv Σ'⊑ₕΣ (cv-pair cv cv₁) =
  cv-pair (typeprecise-strenthen-cv Σ'⊑ₕΣ cv)
          (typeprecise-strenthen-cv Σ'⊑ₕΣ cv₁)
