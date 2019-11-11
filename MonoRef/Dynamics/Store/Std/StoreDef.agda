{-

  MonoRef.Dynamics.Store.StoreDef exports the definition of the store.

-}

open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Std.StoreDef
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import MonoRef.Dynamics.Store.StoreDef
  _⟹_ Inert
open import MonoRef.Static.Types.Relations using (StoreTyping)


module ParamStoreDef
  (StoreValue : (A : Type) → (Σ : StoreTyping) → Set)
  where
    open ParamGenStoreDef StoreValue public

    Store : (Σ Σ' : StoreTyping) → Set
    Store = GenStore
