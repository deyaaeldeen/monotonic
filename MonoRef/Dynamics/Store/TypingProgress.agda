open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.TypingProgress
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

-- standard library++
open import Data.List.Prefix renaming (_⊑_ to _⊑ₗ_)

open import MonoRef.Dynamics.Store.Extension
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Static.Types.Relations using (StoreTyping)

{-

  The store can change after each reduction step in two orthogonal ways. First,
  one element that is already a member of the store could be more precise. On
  the other hand, the store could be extended by adding a single new element to
  the end.

-}
data StoreTypingProgress (Σ Σ' : StoreTyping) : Set where

  from⊑ₕ : Σ' ⊑ₕ Σ → StoreTypingProgress Σ Σ'

  from⊑ₗ : Σ ⊑ₗ Σ' → StoreTypingProgress Σ Σ'

StoreTypingProgress-refl : ∀ {Σ} → StoreTypingProgress Σ Σ
StoreTypingProgress-refl = from⊑ₕ ⊑ₕ-refl
