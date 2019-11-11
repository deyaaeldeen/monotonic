open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Std.Extension.StoreValWeakening
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
  (Value             : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (prefix-weaken-val : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A} → (Σ⊑Σ' : Σ ⊑ Σ')
    → Value v → Value (prefix-weaken-expr Σ⊑Σ' v))
  where

  open import MonoRef.Dynamics.Store.Std.Value _⟹_ Inert
  open ParamStoreValue Value
  
  prefix-weaken-storeval  : ∀ {A Σ Σ'}
    → Σ ⊑ Σ' → StoreValue A Σ → StoreValue A Σ'
  prefix-weaken-storeval Σ⊑Σ' (intro v t) = intro (prefix-weaken-val Σ⊑Σ' v) t
