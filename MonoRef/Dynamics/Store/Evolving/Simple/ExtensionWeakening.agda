open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Evolving.Simple.ExtensionWeakening
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

-- standard library++
open import Data.List.Prefix using (_⊑_ ; ∈-⊒)

open import MonoRef.Dynamics.Simple.Common.Value
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.Simple.DelayedCast
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Extension
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Simple.ExtensionWeakening
  _⟹_ Inert public
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert


prefix-weaken-cv : ∀ {Σ Σ' Γ A} {e : Σ ∣ Γ ⊢ A}
  → (Σ⊑Σ' : Σ ⊑ Σ') → DelayedCast e → DelayedCast (prefix-weaken-expr Σ⊑Σ' e)

prefix-weaken-cv Σ⊑Σ' (v⇑ x) = v⇑ (prefix-weaken-val Σ⊑Σ' x)
prefix-weaken-cv Σ⊑Σ' (cast-val cv c) = cast-val (prefix-weaken-cv Σ⊑Σ' cv) c
prefix-weaken-cv Σ⊑Σ' (cv-pair cv cv₁) =
  cv-pair (prefix-weaken-cv Σ⊑Σ' cv) (prefix-weaken-cv Σ⊑Σ' cv₁)
