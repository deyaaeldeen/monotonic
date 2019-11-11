open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Evolving.Value
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


module ParamStoreValue
  (DelayedCast : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  where
  
  data EvolvingStoreValue (A : Type) (Σ : StoreTyping) : Set where
  
    intro : ∀ {e : Σ ∣ ∅ ⊢ A}
      → DelayedCast e
      → Ty A
        ----------------------
      → EvolvingStoreValue A Σ
  
  data StoreValue (A : Type) (Σ : StoreTyping) :  Set where
  
    fromDelayedCast : EvolvingStoreValue A Σ → StoreValue A Σ
