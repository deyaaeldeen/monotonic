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
  (CastedValue : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (StrongCastedValue : ∀ {Σ Γ A} {e : Σ ∣ Γ ⊢ A} → CastedValue e → Set)
  where

  data NormalStoreValue (A : Type) (Σ : StoreTyping) : Set where
  
    intro : ∀ {V : Σ ∣ ∅ ⊢ A}
      → Value V
      → Ty A
        --------------------
      → NormalStoreValue A Σ
  
  data EvolvingStoreValue (A : Type) (Σ : StoreTyping) : Set where
  
    intro : ∀ {V : Σ ∣ ∅ ⊢ A}
      → CastedValue V
      → Ty A
        ----------------------
      → EvolvingStoreValue A Σ
  
  data StoreValue (A : Type) (Σ : StoreTyping) :  Set where
  
    fromNormalValue : NormalStoreValue A Σ → StoreValue A Σ
  
    fromCastedValue : EvolvingStoreValue A Σ → StoreValue A Σ

  data StronglyEvolvingStoreValue : ∀ {Σ A} → EvolvingStoreValue A Σ → Set where
  
    intro : ∀ {Σ A} {e : Σ ∣ ∅ ⊢ A} {cv : CastedValue e}
      → StrongCastedValue cv → (A' : Ty A)
        ----------------------------------------
      → StronglyEvolvingStoreValue (intro cv A')

  toNormalStoreValue : ∀ {Σ A} {v : Σ ∣ ∅ ⊢ A} → Value v → NormalStoreValue A Σ
  toNormalStoreValue v = intro v (Type⇑ _)
