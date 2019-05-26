open import MonoRef.Static.Types

open import Data.Empty using (⊥ ; ⊥-elim)

module MonoRef.Dynamics.Store.Efficient.Utilities
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  (Inert⇒¬Ref : ∀ {A B} {c : A ⟹ Ref B} → Inert c → ⊥)
  where

open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Dynamics.Efficient.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Types.Relations


ref⟹T : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : Value v) → Type
ref⟹T (S-Val (V-addr {A} _ _)) = A
ref⟹T (V-cast _ c)   = ⊥-elim (Inert⇒¬Ref c)

ref⟹∈ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : Value v) → ref⟹T V ∈ Σ
ref⟹∈ (S-Val (V-addr mem _)) = mem
ref⟹∈ (V-cast _ c)           = ⊥-elim (Inert⇒¬Ref c)

ref⟹⊑ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : Value v) → ref⟹T V ⊑ A
ref⟹⊑ (S-Val (V-addr _ prec)) = prec
ref⟹⊑ (V-cast _ c)            = ⊥-elim (Inert⇒¬Ref c)
