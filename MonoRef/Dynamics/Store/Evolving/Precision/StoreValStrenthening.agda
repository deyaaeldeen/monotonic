open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Evolving.Precision.StoreValStrenthening
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert


module ParamPrecisionStoreValStrenthening
  (DelayedCast : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (typeprecise-strenthen-cv : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A}
    → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
    → DelayedCast v
    → DelayedCast (typeprecise-strenthen-expr Σ'⊑ₕΣ v))
  where

  open import MonoRef.Dynamics.Store.Evolving.Value _⟹_ Inert
  open ParamStoreValue DelayedCast
  
  typeprecise-strenthen-evolvingstoreval : ∀ {Σ Σ' t} → Σ' ⊑ₕ Σ
    → EvolvingStoreValue t Σ
    → EvolvingStoreValue t Σ'
  typeprecise-strenthen-evolvingstoreval Σ'⊑ₕΣ (intro cv ty) =
    intro (typeprecise-strenthen-cv Σ'⊑ₕΣ cv) ty
  
  typeprecise-strenthen-storeval : ∀ {Σ Σ' t} → Σ' ⊑ₕ Σ
    → StoreValue t Σ
    → StoreValue t Σ'
  typeprecise-strenthen-storeval Σ'⊑ₕΣ (fromDelayedCast (intro cv ty)) =
    fromDelayedCast (intro (typeprecise-strenthen-cv Σ'⊑ₕΣ cv) ty)
