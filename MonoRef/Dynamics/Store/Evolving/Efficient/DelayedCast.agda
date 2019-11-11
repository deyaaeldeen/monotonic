{-

  Casted values are special kind of values that can be written to the heap.
  MonoRef.Dynamics.Store.Evolving.Efficient.DelayedCast provides definitions for
  efficient casted values and strong casted values. Reducible casted values are
  casted values that are guaranteed to be productive i.e. have at least one
  active cast.

-}

open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Evolving.Efficient.DelayedCast
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import MonoRef.Dynamics.Efficient.Common.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert


infix 5 v⇑_


data DelayedCast {Σ Γ} : ∀ {A} → Σ ∣ Γ ⊢ A → Set where

  v⇑_ : ∀ {A} {e : Σ ∣ Γ ⊢ A}
    → Value e
      -------------
    → DelayedCast e

  cast-val : ∀ {A B} {e : Σ ∣ Γ ⊢ A}
    → SimpleValue e
    → (c : A ⟹ B)
      ---------------------
    → DelayedCast (e < c >)

  cv-pair : ∀ {A B} {e₁ : Σ ∣ Γ ⊢ A} {e₂ : Σ ∣ Γ ⊢ B}
    → (cv₁ : DelayedCast e₁)
    → (cv₂ : DelayedCast e₂)
      ----------------------
    → DelayedCast (e₁ `× e₂)
