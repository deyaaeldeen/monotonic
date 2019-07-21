{-

  MonoRef.Dynamics.EvolvingStore.StoreDeff exports the definition of the store.

-}

open import MonoRef.Static.Types

module MonoRef.Dynamics.EvolvingStore.StoreDef
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.List.All using (All)

open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Types.Relations using (StoreTyping)


module ParamStoreDef
  (StoreValue : (A : Type) → (Σ : StoreTyping) → Set)
  where

  {- A more general version of the Store type. -}
  StoreUnder : (Σ Σ' : StoreTyping) → Set
  StoreUnder Σ Σ' = All (λ ty → StoreValue ty Σ) Σ'

  Store : (Σ : StoreTyping) → Set
  Store Σ = StoreUnder Σ Σ
