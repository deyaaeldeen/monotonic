module MonoRef.Dynamics.Simple.StdStore.NormalStoreProgress where

open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Sum using (inj₁ ; inj₂)

open import MonoRef.Dynamics.Simple.Coercions
open import MonoRef.Dynamics.Simple.Error
open import MonoRef.Dynamics.Simple.StdStore.ApplyCast
open import MonoRef.Dynamics.Simple.StdStore.SuspendedCast
open import MonoRef.Dynamics.Simple.StdStore.ProgProgressDef
open import MonoRef.Dynamics.Simple.StdStore.Reduction
open import MonoRef.Dynamics.Simple.StdStore.Store
open import MonoRef.Dynamics.Simple.Frames
open import MonoRef.Dynamics.Simple.Substitution
open import MonoRef.Dynamics.Simple.TargetWithoutBlame
open import MonoRef.Dynamics.Simple.Value
open import MonoRef.Static.Context
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


progress-normal-store : ∀ {Σ A}
  → (e : Σ ∣ ∅ ⊢ A) → (μ : Store Σ Σ) → ProgProgress e μ

progress-normal-store (` ()) _

progress-normal-store (ƛ e) _ = done (V-ƛ e)

progress-normal-store (e₁ · e₂) ν with progress-normal-store e₁ ν
... | step e₁⟶e₁' = step (ξ (ξ-appₗ e₂) e₁⟶e₁')
... | done v with progress-normal-store e₂ ν
...   | step e₂⟶e₂' = step (ξ (ξ-appᵣ e₁) e₂⟶e₂')
progress-normal-store (_ · _) _ | done (V-ƛ _) | done v' =
  step (β-pure (β-ƛ v'))
progress-normal-store (_ · _) _ | done (V-cast v I-⇒) | done v' =
  step (β-pure (β-ƛₚ v v'))
... | error E-error = step (ξ-error (ξ-appᵣ e₁))
progress-normal-store (.error · e₂) ν | error E-error =
  step (ξ-error (ξ-appₗ e₂))

progress-normal-store `zero _ = done V-zero

progress-normal-store (`suc e) ν with progress-normal-store e ν
... | step e⟶e' = step (ξ ξ-suc e⟶e')
... | done x = done (V-suc x)
... | error E-error = step (ξ-error ξ-suc)

progress-normal-store (case p z s) ν with progress-normal-store p ν
... | step e⟶e' = step (ξ (ξ-caseₚ z s) e⟶e')
... | error E-error = step (ξ-error (ξ-caseₚ z s))
... | done V-zero = step (β-pure β-zero)
... | done (V-suc v) = step (β-pure (β-suc v))
... | done (V-cast _ ())

progress-normal-store (ref A e) ν with progress-normal-store e ν
... | step e⟶e' = step (ξ (ξ-ref A) e⟶e')
progress-normal-store {Σ = Σ} {A = Ref A} (ref A e) ν | done v =
  step (β-mono (β-ref v))
... | error E-error = step (ξ-error (ξ-ref A))

progress-normal-store (e₁ `× e₂) ν with progress-normal-store e₁ ν
... | step e⟶e' = step (ξ (ξ-×ₗ e₂) e⟶e')
... | error E-error = step (ξ-error (ξ-×ₗ e₂))
... | done v₁ with progress-normal-store e₂ ν
...   | step e⟶e'     = step (ξ (ξ-×ᵣ e₁) e⟶e')
...   | done v₂ = done (V-pair v₁ v₂)
...   | error E-error = step (ξ-error (ξ-×ᵣ e₁))

progress-normal-store (π₁ e) ν with progress-normal-store e ν
... | step e⟶e' = step (ξ ξ-πₗ e⟶e')
... | done (V-pair v₁ v₂) = step (β-pure (β-π₁ v₁ v₂))
... | done (V-cast _ ())
... | error E-error = step (ξ-error ξ-πₗ)

progress-normal-store (π₂ e) ν with progress-normal-store e ν
... | step e⟶e' = step (ξ ξ-πᵣ e⟶e')
... | done (V-pair v₁ v₂) = step (β-pure (β-π₂ v₁ v₂))
... | done (V-cast _ ())
... | error E-error = step (ξ-error ξ-πᵣ)

progress-normal-store (addr mem Σ'⊑Σ) _ = done (V-addr mem Σ'⊑Σ)

progress-normal-store ((!ₛ e) A-static) ν with progress-normal-store e ν
... | step e⟶e' = step (ξ (ξ-!ₛ A-static) e⟶e')
... | done v = step (β-mono (β-!ₛ v))
... | error E-error = step (ξ-error (ξ-!ₛ A-static))

progress-normal-store ((e₁ :=ₛ e₂) A-static) ν with progress-normal-store e₁ ν
... | step e⟶e' = step (ξ (ξ-:=ₛₗ A-static e₂) e⟶e')
... | error E-error = step (ξ-error (ξ-:=ₛₗ A-static e₂))
... | done v₁ with progress-normal-store e₂ ν
...   | step e⟶e' = step (ξ (ξ-:=ₛᵣ A-static e₁) e⟶e')
...   | done v₂ = step (β-mono (β-:=ₛ v₁ v₂))
...   | error E-error = step (ξ-error (ξ-:=ₛᵣ A-static e₁))

progress-normal-store (! A x e) ν with progress-normal-store e ν
... | step e⟶e' = step (ξ (ξ-! A x) e⟶e')
... | done v = step (β-mono (β-! x v))
... | error E-error = step (ξ-error (ξ-! A x))

progress-normal-store (:= A x e₁ e₂) ν with progress-normal-store e₁ ν
... | step e⟶e' = step (ξ (ξ-:=ₗ A x e₂) e⟶e')
... | error E-error = step (ξ-error (ξ-:=ₗ A x e₂))
... | done v₁ with progress-normal-store e₂ ν
...   | step e⟶e' = step (ξ (ξ-:=ᵣ A x e₁) e⟶e')
...   | error E-error = step (ξ-error (ξ-:=ᵣ A x e₁))
...   | done v₂ with successful-cast? (apply-cast ⊑ₕ-refl [] v₂ (make-coercion A (store-lookup-rtti/ref v₁ ν)))
...     | inj₁ e = step (β-mono (β-:= x v₁ v₂ e))
...     | inj₂ e = step (β-mono (β-:=/failed x v₁ v₂ e))

progress-normal-store unit _ = done V-unit

progress-normal-store error _ = error E-error

progress-normal-store (e < c >) ν with progress-normal-store e ν
... | step e⟶e' = step (ξ (ξ-<> c) e⟶e')
... | error E-error = step (ξ-error (ξ-<> c))
... | done v
  with successful-cast? (apply-cast ⊑ₕ-refl [] v c)
...   | inj₁ x = step (cast/succeed v x)
...   | inj₂ x = step (cast/fail v x)
