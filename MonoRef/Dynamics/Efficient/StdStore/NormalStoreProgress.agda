module MonoRef.Dynamics.Efficient.StdStore.NormalStoreProgress where

open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Sum using (inj₁ ; inj₂)

open import MonoRef.Dynamics.Efficient.Coercions
open import MonoRef.Dynamics.Efficient.Error
open import MonoRef.Dynamics.Efficient.StdStore.ApplyCast
open import MonoRef.Dynamics.Efficient.StdStore.SuspendedCast
open import MonoRef.Dynamics.Efficient.StdStore.ProgProgressDef
open import MonoRef.Dynamics.Efficient.StdStore.Reduction
open import MonoRef.Dynamics.Efficient.StdStore.Store
open import MonoRef.Dynamics.Efficient.Frames
open import MonoRef.Dynamics.Efficient.Substitution
open import MonoRef.Dynamics.Efficient.TargetWithoutBlame
open import MonoRef.Static.Context
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


progress-normal-store : ∀ {Σ A}
  → (e : Σ ∣ ∅ ⊢ A) → (μ : Store Σ Σ) → ProgProgress e μ

progress-normal-store (` ()) _

progress-normal-store (ƛ e) _ = done (S-Val (V-ƛ e))

progress-normal-store (e₁ · e₂) ν with progress-normal-store e₁ ν
... | step-d e₁⟶e₁' = step-d (ξ (ξ-appₗ e₂) (switch e₁⟶e₁'))
... | step-a e₁⟶e₁' = step-d (ξ (ξ-appₗ e₂) e₁⟶e₁')
... | done v with progress-normal-store e₂ ν
...   | step-d e₂⟶e₂' = step-d (ξ (ξ-appᵣ e₁) (switch e₂⟶e₂'))
...   | step-a e₂⟶e₂' = step-d (ξ (ξ-appᵣ e₁) e₂⟶e₂')
progress-normal-store (_ · _) _ | done (S-Val (V-ƛ _)) | done v' =
  step-d (β-pure (β-ƛ v'))
progress-normal-store (_ · _) _ | done (V-cast v (I-final (I-middle I-fun))) | done v' =
  step-d (β-pure (β-ƛₚ v v')
  )
... | error E-error = step-d (ξ-error (ξ-appᵣ e₁))
progress-normal-store (.error · e₂) ν | error E-error =
  step-d (ξ-error (ξ-appₗ e₂))

progress-normal-store `zero _ = done (S-Val V-zero)

progress-normal-store (`suc e) ν with progress-normal-store e ν
... | step-d e⟶e' = step-d (ξ ξ-suc (switch e⟶e'))
... | step-a e⟶e' = step-d (ξ ξ-suc e⟶e')
... | done x = done (S-Val (V-suc x))
... | error E-error = step-d (ξ-error ξ-suc)

progress-normal-store (case p z s) ν with progress-normal-store p ν
... | step-d e⟶e' = step-d (ξ (ξ-caseₚ z s) (switch e⟶e'))
... | step-a e⟶e' = step-d (ξ (ξ-caseₚ z s) e⟶e')
... | error E-error = step-d (ξ-error (ξ-caseₚ z s))
... | done (S-Val V-zero) = step-d (β-pure β-zero)
... | done (S-Val (V-suc v)) = step-d (β-pure (β-suc v))
... | done (V-cast _ (I-final (I-middle ())))

progress-normal-store (ref A e) ν with progress-normal-store e ν
... | step-d e⟶e' = step-d (ξ (ξ-ref A) (switch e⟶e'))
... | step-a e⟶e' = step-d (ξ (ξ-ref A) e⟶e')
progress-normal-store {Σ = Σ} {A = Ref A} (ref A e) ν | done v =
  step-d (β-mono (β-ref v))
... | error E-error = step-d (ξ-error (ξ-ref A))

progress-normal-store (e₁ `× e₂) ν with progress-normal-store e₁ ν
... | step-d e⟶e' = step-d (ξ (ξ-×ₗ e₂) (switch e⟶e'))
... | step-a e⟶e' = step-d (ξ (ξ-×ₗ e₂) e⟶e')
... | error E-error = step-d (ξ-error (ξ-×ₗ e₂))
... | done v₁ with progress-normal-store e₂ ν
...   | step-d e⟶e'     = step-d (ξ (ξ-×ᵣ e₁) (switch e⟶e'))
...   | step-a e⟶e'     = step-d (ξ (ξ-×ᵣ e₁) e⟶e')
...   | done v₂ = done (S-Val (V-pair v₁ v₂))
...   | error E-error = step-d (ξ-error (ξ-×ᵣ e₁))

progress-normal-store (π₁ e) ν with progress-normal-store e ν
... | step-d e⟶e' = step-d (ξ ξ-πₗ (switch e⟶e'))
... | step-a e⟶e' = step-d (ξ ξ-πₗ e⟶e')
... | done (S-Val (V-pair v₁ v₂)) = step-d (β-pure (β-π₁ v₁ v₂))
... | done (V-cast _ (I-final (I-middle ())))
... | error E-error = step-d (ξ-error ξ-πₗ)

progress-normal-store (π₂ e) ν with progress-normal-store e ν
... | step-d e⟶e' = step-d (ξ ξ-πᵣ (switch e⟶e'))
... | step-a e⟶e' = step-d (ξ ξ-πᵣ e⟶e')
... | done (S-Val (V-pair v₁ v₂)) = step-d (β-pure (β-π₂ v₁ v₂))
... | done (V-cast _ (I-final (I-middle ())))
... | error E-error = step-d (ξ-error ξ-πᵣ)

progress-normal-store (addr mem Σ'⊑Σ) _ = done (S-Val (V-addr mem Σ'⊑Σ))

progress-normal-store ((!ₛ e) A-static) ν with progress-normal-store e ν
... | step-d e⟶e' = step-d (ξ (ξ-!ₛ A-static) (switch e⟶e'))
... | step-a e⟶e' = step-d (ξ (ξ-!ₛ A-static) e⟶e')
... | done (S-Val v) = step-d (β-mono (β-!ₛ v))
... | done (V-cast _ (I-final (I-middle ())))
... | error E-error = step-d (ξ-error (ξ-!ₛ A-static))

progress-normal-store ((e₁ :=ₛ e₂) A-static) ν with progress-normal-store e₁ ν
... | step-d e⟶e' = step-d (ξ (ξ-:=ₛₗ A-static e₂) (switch e⟶e'))
... | step-a e⟶e' = step-d (ξ (ξ-:=ₛₗ A-static e₂) e⟶e')
... | error E-error = step-d (ξ-error (ξ-:=ₛₗ A-static e₂))
... | done (V-cast _ (I-final (I-middle ())))
... | done (S-Val v₁) with progress-normal-store e₂ ν
...   | step-d e⟶e' = step-d (ξ (ξ-:=ₛᵣ A-static e₁) (switch e⟶e'))
...   | step-a e⟶e' = step-d (ξ (ξ-:=ₛᵣ A-static e₁) e⟶e')
...   | done v₂ = step-d (β-mono (β-:=ₛ v₁ v₂))
...   | error E-error = step-d (ξ-error (ξ-:=ₛᵣ A-static e₁))

progress-normal-store (! A e) ν with progress-normal-store e ν
... | step-d e⟶e' = step-d (ξ (ξ-! A) (switch e⟶e'))
... | step-a e⟶e' = step-d (ξ (ξ-! A) e⟶e')
... | done (V-cast _ (I-final (I-middle ())))
... | done (S-Val v) = step-d (β-mono (β-! v))
... | error E-error = step-d (ξ-error (ξ-! A))

progress-normal-store (:= A e₁ e₂) ν with progress-normal-store e₁ ν
... | step-d e⟶e' = step-d (ξ (ξ-:=ₗ A e₂) (switch e⟶e'))
... | step-a e⟶e' = step-d (ξ (ξ-:=ₗ A e₂) e⟶e')
... | error E-error = step-d (ξ-error (ξ-:=ₗ A e₂))
... | done (V-cast _ (I-final (I-middle ())))
... | done (S-Val v₁) with progress-normal-store e₂ ν
...   | step-d e⟶e' = step-d (ξ (ξ-:=ᵣ A e₁) (switch e⟶e'))
...   | step-a e⟶e' = step-d (ξ (ξ-:=ᵣ A e₁) e⟶e')
...   | error E-error = step-d (ξ-error (ξ-:=ᵣ A e₁))
...   | done v₂ with successful-cast? (apply-cast [] v₂ (make-coercion A (store-lookup-rtti/ref v₁ ν)))
...     | inj₁ x = step-d (β-mono (β-:= v₁ v₂ x))
...     | inj₂ x = step-d (β-mono (β-:=/failed v₁ v₂ x))

progress-normal-store unit _ = done (S-Val V-unit)

progress-normal-store error _ = error E-error

progress-normal-store (e < c >) ν with progress-normal-store e ν
... | step-d e⟶e' = step-a (ξ-cast e⟶e')
... | step-a (switch e⟶e') = step-a (ξ-cast e⟶e')
... | step-a (ξ-cast _) = step-d compose-casts
... | step-a ξ-cast-error = step-d compose-casts
... | error E-error = step-a (ξ-cast-error)
... | done v
  with successful-cast? (apply-cast [] v c)
...   | inj₁ x = step-d (cast/succeed v x)
...   | inj₂ x = step-d (cast/fail v x)
