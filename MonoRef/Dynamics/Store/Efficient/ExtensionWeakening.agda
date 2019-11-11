open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Efficient.ExtensionWeakening
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

-- standard library++
open import Data.List.Prefix using (_⊑_ ; ∈-⊒)

open import MonoRef.Dynamics.Store.Extension
  _⟹_ Inert
open import MonoRef.Dynamics.Efficient.Common.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert


prefix-weaken-val : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A} → (ext : Σ ⊑ Σ')
  → Value v → Value (prefix-weaken-expr ext v)

prefix-weaken-sval : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A} → (ext : Σ ⊑ Σ')
  → SimpleValue v → SimpleValue (prefix-weaken-expr ext v)
prefix-weaken-sval ext (V-ƛ N) = V-ƛ (prefix-weaken-expr ext N)
prefix-weaken-sval _   V-zero = V-zero
prefix-weaken-sval ext (V-suc v) = V-suc (prefix-weaken-val ext v)
prefix-weaken-sval _   V-unit = V-unit
prefix-weaken-sval ext (V-addr mem prec) = V-addr (∈-⊒ mem ext) prec 
prefix-weaken-sval ext (V-pair v v₁) =
  V-pair (prefix-weaken-val ext v) (prefix-weaken-val ext v₁)

prefix-weaken-val ext (S-Val sv) = S-Val (prefix-weaken-sval ext sv)
prefix-weaken-val ext (V-cast e c) = V-cast (prefix-weaken-sval ext e) c
