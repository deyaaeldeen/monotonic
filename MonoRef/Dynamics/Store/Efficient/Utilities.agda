open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Efficient.Utilities
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.List.Membership.Propositional using (_∈_)

open import MonoRef.Dynamics.Efficient.Common.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Types.Relations


ref⟹T : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → Type
ref⟹T (V-addr {A} _ _) = A

ref⟹∈ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ∈ Σ
ref⟹∈ (V-addr mem _) = mem

ref⟹⊑ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ⊑ A
ref⟹⊑ (V-addr _ prec) = prec
