open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Std.Precision.StoreValStrenthening
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert


module ParamPrecisionStoreValStrenthening
  (Value             : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (typeprecise-strenthen-val : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A} → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
    → Value v
    → Value (typeprecise-strenthen-expr Σ'⊑ₕΣ v))
  where

  open import MonoRef.Dynamics.Store.Std.Value _⟹_ Inert
  open ParamStoreValue Value
  
  typeprecise-strenthen-storeval : ∀ {Σ Σ' t} → Σ' ⊑ₕ Σ
    → StoreValue t Σ
    → StoreValue t Σ'
  typeprecise-strenthen-storeval Σ'⊑ₕΣ (intro v ty) =
    intro (typeprecise-strenthen-val Σ'⊑ₕΣ v) ty
