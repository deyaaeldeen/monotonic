open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Std.Value
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


module ParamStoreValue
  (Value : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  where

  data StoreValue (A : Type) (Σ : StoreTyping) : Set where
  
    intro : ∀ {V : Σ ∣ ∅ ⊢ A}
      → Value V
      → Ty A
        --------------
      → StoreValue A Σ
  
  toStoreValue : ∀ {Σ A} {v : Σ ∣ ∅ ⊢ A} → Value v → StoreValue A Σ
  toStoreValue v = intro v (Type⇑ _)
