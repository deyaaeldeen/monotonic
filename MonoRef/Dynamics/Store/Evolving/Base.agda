{-

  MonoRef.Dynamics.Store.Evolving.Base provides ν-cast and store, where the former casts
  the store to a more precise type and the latter extends the store with one
  more element.

-}

open import MonoRef.Static.Types

open import Data.Empty using (⊥ ; ⊥-elim)

module MonoRef.Dynamics.Store.Evolving.Base
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
open import MonoRef.Dynamics.Store.Evolving.Extension.StoreValWeakening
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.Precision.StoreValStrenthening
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.Store
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


module ParamBase
  (SimpleValue       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (Value             : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (DelayedCast       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (v⇑_ : ∀ {Σ Γ A} {t : Σ ∣ Γ ⊢ A} → Value t → DelayedCast t)

  {- These utilities depend on the definition of Value -}
  (ref⟹T : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → Type)
  (ref⟹∈ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ∈ Σ)
  (ref⟹⊑ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ⊑ A)
  where

  open ParamStoreValue DelayedCast
  open ParamStoreDef StoreValue
  open ParamStore SimpleValue Value DelayedCast v⇑_ ref⟹T ref⟹∈ ref⟹⊑

  module StoreExtend
    (prefix-weaken-cv  : ∀ {Σ Σ' Γ A} {e : Σ ∣ Γ ⊢ A}
      → (Σ⊑ₗΣ' : Σ ⊑ₗ Σ')
      → DelayedCast e
      → DelayedCast (prefix-weaken-expr Σ⊑ₗΣ' e))
    where

    open ParamExtensionStoreValWeakening DelayedCast prefix-weaken-cv

    store : ∀ {Σ A} {e : Σ ∣ ∅ ⊢ A} → Value e → Store Σ → Store (Σ ∷ʳ A)
    store v ν =
      (map (prefix-weaken-storeval Σ⊑ₗΣ') ν) all-∷ʳ (prefix-weaken-storeval Σ⊑ₗΣ' v')
      where
        v' = fromDelayedCast (intro (v⇑ v) (Type⇑ _)) -- v
        Σ⊑ₗΣ' = ∷ʳ-⊒ _ _

  module Corollary1
    (typeprecise-strenthen-cv : ∀ {Σ Σ' Γ A} {e : Σ ∣ Γ ⊢ A}
      → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
      → DelayedCast e
      → DelayedCast (typeprecise-strenthen-expr Σ'⊑ₕΣ e))
    (all-⊑ₕ : ∀ {Σ Σ'}
      → All (λ ty → StoreValue ty Σ') Σ
      → Σ' ⊑ₕ Σ
      → All (λ ty → StoreValue ty Σ') Σ')
    where

    open ParamPrecisionStoreValStrenthening DelayedCast typeprecise-strenthen-cv

    {- Corollary 1 (Monotonic heap update). -}

    ν-cast : ∀ {Σ A B}
      → (A∈Σ : A ∈ Σ)
      → (ν : Store Σ)
      → B ⊑ (store-lookup-rtti A∈Σ ν)
      → Store (Σ-cast A∈Σ B)
    ν-cast {Σ} {B = B} A∈Σ ν B⊑A =
      all-⊑ₕ (map (typeprecise-strenthen-storeval Σ'⊑ₕΣ) ν) Σ'⊑ₕΣ
      where
        Σ'⊑ₕΣ : (Σ-cast A∈Σ B) ⊑ₕ Σ
        Σ'⊑ₕΣ rewrite mem-rtti-preserves-Σ A∈Σ ν = build-prec A∈Σ B⊑A
