open import MonoRef.Static.Types

module MonoRef.Dynamics.Error
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert


data Error {Γ Σ A} : (M : Σ ∣ Γ ⊢ A) → Set where

  E-error : Error error
