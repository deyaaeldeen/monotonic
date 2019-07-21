open import MonoRef.Static.Types

module MonoRef.Dynamics.EvolvingStore.Value
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


module ParamStoreValue
  (Value : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (DelayedCast : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (ReducibleDelayedCast : ∀ {Σ Γ A} {e : Σ ∣ Γ ⊢ A} → DelayedCast e → Set)
  where

  data NormalStoreValue (A : Type) (Σ : StoreTyping) : Set where
  
    intro : ∀ {V : Σ ∣ ∅ ⊢ A}
      → Value V
      → Ty A
        --------------------
      → NormalStoreValue A Σ
  
  data EvolvingStoreValue (A : Type) (Σ : StoreTyping) : Set where
  
    intro : ∀ {V : Σ ∣ ∅ ⊢ A}
      → DelayedCast V
      → Ty A
        ----------------------
      → EvolvingStoreValue A Σ
  
  data StoreValue (A : Type) (Σ : StoreTyping) :  Set where
  
    fromNormalValue : NormalStoreValue A Σ → StoreValue A Σ
  
    fromDelayedCast : EvolvingStoreValue A Σ → StoreValue A Σ

  data ReduciblelyEvolvingStoreValue : ∀ {Σ A} → EvolvingStoreValue A Σ → Set where
  
    intro : ∀ {Σ A} {e : Σ ∣ ∅ ⊢ A} {cv : DelayedCast e}
      → ReducibleDelayedCast cv → (A' : Ty A)
        ----------------------------------------
      → ReduciblelyEvolvingStoreValue (intro cv A')

  toNormalStoreValue : ∀ {Σ A} {v : Σ ∣ ∅ ⊢ A} → Value v → NormalStoreValue A Σ
  toNormalStoreValue v = intro v (Type⇑ _)
