open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Evolving.Extension.StoreValWeakening
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

-- standard library++
open import Data.List.Prefix using (_⊑_)

open import MonoRef.Dynamics.Store.Extension
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert


module ParamExtensionStoreValWeakening
  (DelayedCast       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (prefix-weaken-cv  : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A} → (Σ⊑Σ' : Σ ⊑ Σ')
    → DelayedCast v → DelayedCast (prefix-weaken-expr Σ⊑Σ' v))
  where

  open import MonoRef.Dynamics.Store.Evolving.Value _⟹_ Inert
  open ParamStoreValue DelayedCast
  
  prefix-weaken-storeval  : ∀ {A Σ Σ'}
    → Σ ⊑ Σ' → StoreValue A Σ → StoreValue A Σ'
  prefix-weaken-storeval Σ⊑Σ' (fromDelayedCast (intro cv t)) =
    fromDelayedCast (intro (prefix-weaken-cv Σ⊑Σ' cv) t)
