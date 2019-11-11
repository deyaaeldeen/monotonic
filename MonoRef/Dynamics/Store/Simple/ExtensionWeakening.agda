open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Simple.ExtensionWeakening
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

-- standard library++
open import Data.List.Prefix using (_⊑_ ; ∈-⊒)

open import MonoRef.Dynamics.Store.Extension
  _⟹_ Inert
open import MonoRef.Dynamics.Simple.Common.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert


prefix-weaken-val : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A}
  → (Σ⊑Σ' : Σ ⊑ Σ') → Value v → Value (prefix-weaken-expr Σ⊑Σ' v)
prefix-weaken-val Σ⊑Σ' (V-ƛ N) = V-ƛ (prefix-weaken-expr Σ⊑Σ' N)
prefix-weaken-val Σ⊑Σ' (V-cast e c) = V-cast (prefix-weaken-val Σ⊑Σ' e) c
prefix-weaken-val _    V-zero = V-zero
prefix-weaken-val Σ⊑Σ' (V-suc v) = V-suc (prefix-weaken-val Σ⊑Σ' v)
prefix-weaken-val _    V-unit = V-unit
prefix-weaken-val Σ⊑Σ' (V-addr mem p) = V-addr (∈-⊒ mem Σ⊑Σ') p
prefix-weaken-val Σ⊑Σ' (V-pair v v₁) =
  V-pair (prefix-weaken-val Σ⊑Σ' v) (prefix-weaken-val Σ⊑Σ' v₁)
