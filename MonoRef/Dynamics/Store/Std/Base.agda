{-

  MonoRef.Dynamics.Store.Std.Base provides ν-cast and store, where the former casts
  the store to a more precise type and the latter extends the store with one
  more element.

-}

open import MonoRef.Static.Types

open import Data.Empty using (⊥ ; ⊥-elim)

module MonoRef.Dynamics.Store.Std.Base
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.List using (_∷ʳ_)
open import Data.List.All using (All ; map)
open import Data.List.Membership.Propositional using (_∈_)

-- standard library++
open import Data.List.Prefix renaming (_⊑_ to _⊑ₗ_)
open import Data.List.All.Properties.Extra using (_all-∷ʳ_)

open import MonoRef.Dynamics.Store.Extension
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Std.Extension.StoreValWeakening
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Std.Precision.StoreValStrenthening
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Std.Store
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Std.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Std.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


module ParamBase
  (SimpleValue       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (Value             : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)

  {- These utilities depend on the definition of Value -}
  (ref⟹T : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → Type)
  (ref⟹∈ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ∈ Σ)
  (ref⟹⊑ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ⊑ A)
  where

  open ParamStoreValue Value
  open ParamStoreDef StoreValue
  open ParamStore SimpleValue Value ref⟹T ref⟹∈ ref⟹⊑

  module StoreExtend
    (prefix-weaken-val : ∀ {Σ Σ' Γ A} {e : Σ ∣ Γ ⊢ A}
      → (Σ⊑ₗΣ' : Σ ⊑ₗ Σ')
      → Value e → Value (prefix-weaken-expr Σ⊑ₗΣ' e))
    where

    open ParamExtensionStoreValWeakening Value prefix-weaken-val

    store : ∀ {Σ A} {e : Σ ∣ ∅ ⊢ A} → Value e → Store Σ Σ → Store (Σ ∷ʳ A) (Σ ∷ʳ A)
    store v ν =
      (map (prefix-weaken-storeval Σ⊑ₗΣ') ν) all-∷ʳ (prefix-weaken-storeval Σ⊑ₗΣ' (intro v (Type⇑ _)))
      where
        Σ⊑ₗΣ' = ∷ʳ-⊒ _ _
