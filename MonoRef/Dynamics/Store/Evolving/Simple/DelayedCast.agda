{-

  Casted values are special kind of values that can be written to the heap.
  MonoRef.Dynamics.Store.Evolving.Simple.DelayedCast provides definitions for simple
  (space-inefficient) casted values and strong casted values. Reducible casted
  values are casted values that are guaranteed to be productive i.e. have at
  least one active cast.

-}

open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Evolving.Simple.DelayedCast
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import MonoRef.Dynamics.Simple.Common.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context


infix 5 v⇑_

data DelayedCast {Σ Γ} : ∀ {A} → Σ ∣ Γ ⊢ A → Set where

  v⇑_ : ∀ {A} {t : Σ ∣ Γ ⊢ A}
    → Value t
      -------------
    → DelayedCast t

  {-

    It is important to clarify why there is no constraint here that B ⊑ A. To
    prove progress when a casted value exists in the heap, we need to prove that
    when a casted value takes a step, the result is also a casted value. In the
    case when the casted value is ⋆ with a projection on it, it can be the case
    that the type projected to is less preciss than the type injected at and B ⊑
    A does not hold.

  -}

  cast-val : ∀ {A B} {e : Σ ∣ Γ ⊢ A}
    → (cv : DelayedCast e)
    → (c : A ⟹ B)
      ---------------------
    → DelayedCast (e < c >)

  cv-pair : ∀ {A B} {e₁ : Σ ∣ Γ ⊢ A} {e₂ : Σ ∣ Γ ⊢ B}
    → (cv₁ : DelayedCast e₁)
    → (cv₂ : DelayedCast e₂)
      ----------------------
    → DelayedCast (e₁ `× e₂)
