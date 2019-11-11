open import Relation.Nullary using (Dec ; yes ; no)

open import MonoRef.Static.Types

module MonoRef.Dynamics.Simple.Common.Value.Properties
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  (inertP : ∀ {A B} → (c : A ⟹ B) → Dec (Inert c))
  where

open import Data.List.Membership.Propositional using (_∈_)

open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Types.Relations
open import MonoRef.Static.Context
open import MonoRef.Dynamics.Simple.Common.Value
  _⟹_ Inert

valueP : ∀ {Σ A} → (e : Σ ∣ ∅ ⊢ A) → Dec (Value e)
valueP (` ())
valueP (ƛ e) = yes (V-ƛ e)
valueP (e · e₁) = no (λ ())
valueP `zero = yes V-zero
valueP (`suc e)
  with valueP e
... | yes p = yes (V-suc p)
... | no ¬p = no (λ { (V-suc x) → ¬p x})
valueP (case e e₁ e₂) = no (λ ())
valueP (ref e) = no (λ ())
valueP (e₁ `× e₂)
  with valueP e₁ | valueP e₂
... | yes p | yes p₁ = yes (V-pair p p₁)
... | yes _ | no ¬p = no (λ { (V-pair _ x) → ¬p x})
... | no ¬p | _ = no (λ { (V-pair x _) → ¬p x})
valueP (π₁ e) = no (λ ())
valueP (π₂ e) = no (λ ())
valueP (addr x x₁) = yes (V-addr x x₁)
valueP ((!ₛ e) x) = no (λ ())
valueP ((e :=ₛ e₁) x) = no (λ ())
valueP (! _ _) = no (λ ())
valueP (:= _ _ _) = no (λ ())
valueP unit = yes V-unit
valueP (e < x >)
  with valueP e
... | no ¬p = no (λ { (V-cast x _) → ¬p x})
... | yes p
    with inertP x
...   | yes cp = yes (V-cast p cp)
...   | no ¬p = no (λ { (V-cast x x₁) → ¬p x₁})
valueP error = no (λ ())
