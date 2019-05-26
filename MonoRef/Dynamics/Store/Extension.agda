open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Extension
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

-- standard library++
open import Data.List.Prefix using (_⊑_ ; ∈-⊒)

open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert


prefix-weaken-expr : ∀ {Σ Σ' Γ A} → Σ ⊑ Σ' → Σ ∣ Γ ⊢ A → Σ' ∣ Γ ⊢ A
prefix-weaken-expr _   (` x) = ` x
prefix-weaken-expr Σ⊑Σ' (ƛ e) = ƛ prefix-weaken-expr Σ⊑Σ' e
prefix-weaken-expr Σ⊑Σ' (e · e₁) =
  prefix-weaken-expr Σ⊑Σ' e · prefix-weaken-expr Σ⊑Σ' e₁
prefix-weaken-expr _   `zero = `zero
prefix-weaken-expr Σ⊑Σ' (`suc e) = `suc prefix-weaken-expr Σ⊑Σ' e
prefix-weaken-expr Σ⊑Σ' (case e e₁ e₂) =
  case (prefix-weaken-expr Σ⊑Σ' e)
       (prefix-weaken-expr Σ⊑Σ' e₁)
       (prefix-weaken-expr Σ⊑Σ' e₂)
prefix-weaken-expr Σ⊑Σ' (ref e) = ref prefix-weaken-expr Σ⊑Σ' e
prefix-weaken-expr Σ⊑Σ' (e `× e₁) =
  prefix-weaken-expr Σ⊑Σ' e `× prefix-weaken-expr Σ⊑Σ' e₁
prefix-weaken-expr Σ⊑Σ' (π₁ e) = π₁ prefix-weaken-expr Σ⊑Σ' e
prefix-weaken-expr Σ⊑Σ' (π₂ e) = π₂ prefix-weaken-expr Σ⊑Σ' e
prefix-weaken-expr Σ⊑Σ' (addr mem prec) = addr (∈-⊒ mem Σ⊑Σ') prec
prefix-weaken-expr Σ⊑Σ' ((!ₛ e) x) = (!ₛ prefix-weaken-expr Σ⊑Σ' e) x
prefix-weaken-expr Σ⊑Σ' ((e :=ₛ e₁) x) =
  (prefix-weaken-expr Σ⊑Σ' e :=ₛ prefix-weaken-expr Σ⊑Σ' e₁) x
prefix-weaken-expr Σ⊑Σ' (! e) = ! prefix-weaken-expr Σ⊑Σ' e
prefix-weaken-expr Σ⊑Σ' (e := e₁) =
  prefix-weaken-expr Σ⊑Σ' e := prefix-weaken-expr Σ⊑Σ' e₁
prefix-weaken-expr _   unit = unit
prefix-weaken-expr Σ⊑Σ' (e < x >) = prefix-weaken-expr Σ⊑Σ' e < x >
prefix-weaken-expr _   error = error
