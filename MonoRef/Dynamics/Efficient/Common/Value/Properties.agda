open import Relation.Nullary using (Dec ; yes ; no)

open import MonoRef.Static.Types

module MonoRef.Dynamics.Efficient.Common.Value.Properties
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  (inertP : ∀ {A B} → (c : A ⟹ B) → Dec (Inert c))
  where

open import Data.List.Membership.Propositional using (_∈_)

open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Types.Relations
open import MonoRef.Static.Context
open import MonoRef.Dynamics.Efficient.Common.Value
  _⟹_ Inert


svalueP : ∀ {Σ A} → (e : Σ ∣ ∅ ⊢ A) → Dec (SimpleValue e)
valueP : ∀ {Σ A} → (e : Σ ∣ ∅ ⊢ A) → Dec (Value e)

valueP (` ())
valueP (ƛ e) = yes (S-Val (V-ƛ e))
valueP (_ · _) = no (λ{ (S-Val ())})
valueP `zero = yes (S-Val V-zero)
valueP (`suc e)
  with valueP e
... | yes p = yes (S-Val (V-suc p))
... | no ¬p = no (λ { (S-Val (V-suc x)) → ¬p x})
valueP (case _ _ _) = no (λ{ (S-Val ())})
valueP (ref _) = no (λ{ (S-Val ())})
valueP (e₁ `× e₂)
  with valueP e₁ | valueP e₂
... | yes p | yes p₁ = yes (S-Val (V-pair p p₁))
... | yes _ | no ¬p = no (λ { (S-Val (V-pair _ x)) → ¬p x})
... | no ¬p | _ = no (λ { (S-Val (V-pair x _)) → ¬p x})
valueP (π₁ _) = no (λ{ (S-Val ())})
valueP (π₂ _) = no (λ{ (S-Val ())})
valueP (addr x x₁) = yes (S-Val (V-addr x x₁))
valueP ((!ₛ _) _) = no (λ{ (S-Val ())})
valueP ((_ :=ₛ _) x) = no (λ{ (S-Val ())})
valueP (! _ _) = no (λ{ (S-Val ())})
valueP (:= _ _ _) = no (λ{ (S-Val ())})
valueP unit = yes (S-Val V-unit)
valueP (e < c >)
  with svalueP e
... | no ¬p = no (λ { (V-cast c _) → ¬p c ; (S-Val ())})
... | yes p
    with inertP c
...   | yes cp = yes (V-cast p cp)
...   | no ¬p = no (λ{ (S-Val ()) ; (V-cast _ x₁) → ¬p x₁})
valueP error = no (λ{ (S-Val ())})

svalueP (` ())
svalueP (ƛ e) = yes (V-ƛ e)
svalueP (_ · _) = no λ ()
svalueP `zero = yes V-zero
svalueP (`suc e)
  with valueP e
... | yes p = yes (V-suc p)
... | no ¬p = no (λ { (V-suc x) → ¬p x})
svalueP (case _ _ _) = no (λ ())
svalueP (ref _) = no (λ ())
svalueP (e₁ `× e₂)
  with valueP e₁ | valueP e₂
... | yes p | yes p₁ = yes (V-pair p p₁)
... | yes _ | no ¬p = no (λ { (V-pair _ x) → ¬p x})
... | no ¬p | _ = no (λ { (V-pair x _) → ¬p x})
svalueP (π₁ _) = no (λ ())
svalueP (π₂ _) = no (λ ())
svalueP (addr x x₁) = yes (V-addr x x₁)
svalueP ((!ₛ _) _) = no (λ ())
svalueP ((_ :=ₛ _) x) = no (λ ())
svalueP (! _ _) = no (λ ())
svalueP (:= _ _ _) = no (λ ())
svalueP unit = yes V-unit
svalueP (_ < _ >) = no λ ()
svalueP error = no (λ ())
