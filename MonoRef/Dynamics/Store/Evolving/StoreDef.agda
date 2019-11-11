{-

  MonoRef.Dynamics.Store.StoreDef exports the definition of the store.

-}

open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Evolving.StoreDef
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.List.All using (All)

open import MonoRef.Dynamics.Store.StoreDef
  _⟹_ Inert
open import MonoRef.Static.Types.Relations using (StoreTyping)


module ParamStoreDef
  (StoreValue : (A : Type) → (Σ : StoreTyping) → Set)
  where

    open ParamGenStoreDef StoreValue public

    Store : (Σ : StoreTyping) → Set
    Store Σ = GenStore Σ Σ
