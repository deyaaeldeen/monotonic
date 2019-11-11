open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Evolving.Efficient.ExtensionWeakening
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

-- standard library++
open import Data.List.Prefix using (_⊑_)

open import MonoRef.Dynamics.Store.Evolving.Efficient.DelayedCast
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Extension
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Efficient.ExtensionWeakening
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert

prefix-weaken-cv : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A} → (ext : Σ ⊑ Σ')
  → DelayedCast v
  → DelayedCast (prefix-weaken-expr ext v)
prefix-weaken-cv ext (v⇑ x) = v⇑ (prefix-weaken-val ext x)
prefix-weaken-cv ext (cast-val v c) = cast-val (prefix-weaken-sval ext v) c
prefix-weaken-cv ext (cv-pair cv cv₁) =
  cv-pair (prefix-weaken-cv ext cv) (prefix-weaken-cv ext cv₁)
