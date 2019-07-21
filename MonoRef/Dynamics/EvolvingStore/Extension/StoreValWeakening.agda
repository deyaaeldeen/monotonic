open import MonoRef.Static.Types

module MonoRef.Dynamics.EvolvingStore.Extension.StoreValWeakening
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

-- standard library++
open import Data.List.Prefix using (_⊑_ ; ∈-⊒)

open import MonoRef.Dynamics.EvolvingStore.Extension
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert


module ParamExtensionStoreValWeakening
  (Value             : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (DelayedCast       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (StrongDelayedCast : ∀ {Σ Γ A} {e : Σ ∣ Γ ⊢ A} → DelayedCast e → Set)
  (prefix-weaken-cv  : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A} → (Σ⊑Σ' : Σ ⊑ Σ')
    → DelayedCast v → DelayedCast (prefix-weaken-expr Σ⊑Σ' v))
  (prefix-weaken-val : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A} → (Σ⊑Σ' : Σ ⊑ Σ')
    → Value v → Value (prefix-weaken-expr Σ⊑Σ' v))
  where

  open import MonoRef.Dynamics.EvolvingStore.Value _⟹_ Inert
  open ParamStoreValue Value DelayedCast StrongDelayedCast
  
  prefix-weaken-storeval  : ∀ {A Σ Σ'}
    → Σ ⊑ Σ' → StoreValue A Σ → StoreValue A Σ'
  prefix-weaken-storeval Σ⊑Σ' (fromNormalValue (intro v t)) =
    fromNormalValue (intro (prefix-weaken-val Σ⊑Σ' v) t)
  prefix-weaken-storeval Σ⊑Σ' (fromDelayedCast (intro cv t)) =
    fromDelayedCast (intro (prefix-weaken-cv Σ⊑Σ' cv) t)
