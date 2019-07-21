open import MonoRef.Static.Types

module MonoRef.Dynamics.EvolvingStore.Precision.StoreValStrenthening
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import MonoRef.Dynamics.EvolvingStore.Precision
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert


module ParamPrecisionStoreValStrenthening
  (Value             : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (DelayedCast       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (StrongDelayedCast : ∀ {Σ Γ A} {e : Σ ∣ Γ ⊢ A} → DelayedCast e → Set)
  (typeprecise-strenthen-cv : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A} → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
    → DelayedCast v
    → DelayedCast (typeprecise-strenthen-expr Σ'⊑ₕΣ v))
  (typeprecise-strenthen-val : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A} → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
    → Value v
    → Value (typeprecise-strenthen-expr Σ'⊑ₕΣ v))
  where

  open import MonoRef.Dynamics.EvolvingStore.Value _⟹_ Inert
  open ParamStoreValue Value DelayedCast StrongDelayedCast
  
  typeprecise-strenthen-evolvingstoreval : ∀ {Σ Σ' t} → Σ' ⊑ₕ Σ
    → EvolvingStoreValue t Σ
    → EvolvingStoreValue t Σ'
  typeprecise-strenthen-evolvingstoreval Σ'⊑ₕΣ (intro cv ty) =
    intro (typeprecise-strenthen-cv Σ'⊑ₕΣ cv) ty
  
  typeprecise-strenthen-storeval : ∀ {Σ Σ' t} → Σ' ⊑ₕ Σ
    → StoreValue t Σ
    → StoreValue t Σ'
  typeprecise-strenthen-storeval Σ'⊑ₕΣ (fromNormalValue (intro v ty)) =
    fromNormalValue (intro (typeprecise-strenthen-val Σ'⊑ₕΣ v) ty)
  typeprecise-strenthen-storeval Σ'⊑ₕΣ (fromDelayedCast (intro cv ty)) =
    fromDelayedCast (intro (typeprecise-strenthen-cv Σ'⊑ₕΣ cv) ty)
