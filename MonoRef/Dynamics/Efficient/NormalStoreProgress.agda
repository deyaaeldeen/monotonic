module MonoRef.Dynamics.Efficient.NormalStoreProgress where

open import Data.Empty using (⊥-elim)

open import MonoRef.Coercions.NormalForm.Compose
open import MonoRef.Coercions.NormalForm.Reduction
open import MonoRef.Coercions.NormalForm.Syntax
  renaming (NormalFormCoercion to _⟹_ ; InertNormalForm to Inert
           ; ActiveNormalForm to Active ; inert-normalform-decidable to inertP
           ; ¬Inert⇒Active-normform to ¬Inert⇒Active)
open import MonoRef.Coercions.NormalForm.Make renaming (make-normal-form-coercion to make-coercion)
open import MonoRef.Dynamics.Efficient.Frames
  _⟹_ Inert
open import MonoRef.Dynamics.Efficient.Reduction
  _⟹_ Inert Active make-coercion Inert⇒¬Ref
open import MonoRef.Dynamics.Store.Efficient
  _⟹_ Inert Active inertP ¬Inert⇒Active make-coercion Inert⇒¬Ref compose
open import MonoRef.Dynamics.Substitution
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Dynamics.Efficient.CastProgress
open import MonoRef.Dynamics.Efficient.ProgProgressDef
open import MonoRef.Dynamics.Error
  _⟹_ Inert
open import MonoRef.Dynamics.Efficient.Value
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types


open ParamReduction SimpleValue Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑
open ParamReduction/ν-cast/ν-update/ref/store/⟶ᵤ ν-cast ν-update/ref store _⟶ᵤ_

progress-normal-store : ∀ {Σ A}
  → (e : Σ ∣ ∅ ⊢ A) → (μ : Store Σ) → NormalStore μ → ProgProgress e μ

progress-normal-store (` ()) _ _

progress-normal-store (ƛ e) _ _ = done (S-Val (V-ƛ e))

progress-normal-store (e₁ · e₂) ν μ-evd with progress-normal-store e₁ ν μ-evd
... | step-d μ-evd' e₁⟶e₁' = step-d μ-evd' (ξ (ξ-appₗ e₂) (switch e₁⟶e₁'))
... | step-a μ-evd' e₁⟶e₁' = step-d μ-evd' (ξ (ξ-appₗ e₂) e₁⟶e₁')
... | done v with progress-normal-store e₂ ν μ-evd
...   | step-d μ-evd' e₂⟶e₂' = step-d μ-evd' (ξ (ξ-appᵣ e₁) (switch e₂⟶e₂'))
...   | step-a μ-evd' e₂⟶e₂' = step-d μ-evd' (ξ (ξ-appᵣ e₁) e₂⟶e₂')
progress-normal-store (_ · _) _ μ-evd | done (S-Val (V-ƛ _)) | done v' =
  step-d μ-evd (β-pure (β-ƛ v'))
progress-normal-store (_ · _) _ μ-evd | done (V-cast v (I-final (I-middle I-fun))) | done v' =
  step-d μ-evd (β-pure (β-ƛₚ v v')
  )
... | error E-error = step-d μ-evd (ξ-error (ξ-appᵣ e₁))
progress-normal-store (.error · e₂) ν μ-evd | error E-error =
  step-d μ-evd (ξ-error (ξ-appₗ e₂))

progress-normal-store `zero _ _ = done (S-Val V-zero)

progress-normal-store (`suc e) ν μ-evd with progress-normal-store e ν μ-evd
... | step-d μ-evd' e⟶e' = step-d μ-evd' (ξ ξ-suc (switch e⟶e'))
... | step-a μ-evd' e⟶e' = step-d μ-evd' (ξ ξ-suc e⟶e')
... | done x = done (S-Val (V-suc x))
... | error E-error = step-d μ-evd (ξ-error ξ-suc)

progress-normal-store (case p z s) ν μ-evd with progress-normal-store p ν μ-evd
... | step-d μ-evd' e⟶e' = step-d μ-evd' (ξ (ξ-caseₚ z s) (switch e⟶e'))
... | step-a μ-evd' e⟶e' = step-d μ-evd' (ξ (ξ-caseₚ z s) e⟶e')
... | error E-error = step-d μ-evd (ξ-error (ξ-caseₚ z s))
... | done (S-Val V-zero) = step-d μ-evd (β-pure β-zero)
... | done (S-Val (V-suc v)) = step-d μ-evd (β-pure (β-suc v))
... | done (V-cast _ (I-final (I-middle ())))

progress-normal-store (ref e) ν μ-evd with progress-normal-store e ν μ-evd
... | step-d μ-evd' e⟶e' = step-d μ-evd' (ξ ξ-ref (switch e⟶e'))
... | step-a μ-evd' e⟶e' = step-d μ-evd' (ξ ξ-ref e⟶e')
progress-normal-store {Σ = Σ} {A = Ref A} (ref e) ν μ-evd | done v =
  step-d μ-evd (β-mono (β-ref v))
... | error E-error = step-d μ-evd (ξ-error ξ-ref)

progress-normal-store (e₁ `× e₂) ν μ-evd with progress-normal-store e₁ ν μ-evd
... | step-d μ-evd' e⟶e' = step-d μ-evd' (ξ (ξ-×ₗ e₂) (switch e⟶e'))
... | step-a μ-evd' e⟶e' = step-d μ-evd' (ξ (ξ-×ₗ e₂) e⟶e')
... | error E-error = step-d μ-evd (ξ-error (ξ-×ₗ e₂))
... | done v₁ with progress-normal-store e₂ ν μ-evd
...   | step-d μ-evd' e⟶e'     = step-d μ-evd' (ξ (ξ-×ᵣ e₁) (switch e⟶e'))
...   | step-a μ-evd' e⟶e'     = step-d μ-evd' (ξ (ξ-×ᵣ e₁) e⟶e')
...   | done v₂ = done (S-Val (V-pair v₁ v₂))
...   | error E-error = step-d μ-evd (ξ-error (ξ-×ᵣ e₁))

progress-normal-store (π₁ e) ν μ-evd with progress-normal-store e ν μ-evd
... | step-d μ-evd' e⟶e' = step-d μ-evd' (ξ ξ-πₗ (switch e⟶e'))
... | step-a μ-evd' e⟶e' = step-d μ-evd' (ξ ξ-πₗ e⟶e')
... | done (S-Val (V-pair v₁ v₂)) = step-d μ-evd (β-pure (β-π₁ v₁ v₂))
... | done (V-cast _ (I-final (I-middle ())))
... | error E-error = step-d μ-evd (ξ-error ξ-πₗ)

progress-normal-store (π₂ e) ν μ-evd with progress-normal-store e ν μ-evd
... | step-d μ-evd' e⟶e' = step-d μ-evd' (ξ ξ-πᵣ (switch e⟶e'))
... | step-a μ-evd' e⟶e' = step-d μ-evd' (ξ ξ-πᵣ e⟶e')
... | done (S-Val (V-pair v₁ v₂)) = step-d μ-evd (β-pure (β-π₂ v₁ v₂))
... | done (V-cast _ (I-final (I-middle ())))
... | error E-error = step-d μ-evd (ξ-error ξ-πᵣ)

progress-normal-store (addr mem Σ'⊑Σ) _ _ = done (S-Val (V-addr mem Σ'⊑Σ))

progress-normal-store ((!ₛ e) A-static) ν μ-evd with progress-normal-store e ν μ-evd
... | step-d μ-evd' e⟶e' = step-d μ-evd' (ξ (ξ-!ₛ A-static) (switch e⟶e'))
... | step-a μ-evd' e⟶e' = step-d μ-evd' (ξ (ξ-!ₛ A-static) e⟶e')
... | done v = step-d μ-evd (β-mono (β-!ₛ v))
... | error E-error = step-d μ-evd (ξ-error (ξ-!ₛ A-static))

progress-normal-store ((e₁ :=ₛ e₂) A-static) ν μ-evd with progress-normal-store e₁ ν μ-evd
... | step-d μ-evd' e⟶e' = step-d μ-evd' (ξ (ξ-:=ₛₗ A-static e₂) (switch e⟶e'))
... | step-a μ-evd' e⟶e' = step-d μ-evd' (ξ (ξ-:=ₛₗ A-static e₂) e⟶e')
... | error E-error = step-d μ-evd (ξ-error (ξ-:=ₛₗ A-static e₂))
... | done v₁ with progress-normal-store e₂ ν μ-evd
...   | step-d μ-evd' e⟶e' = step-d μ-evd' (ξ (ξ-:=ₛᵣ A-static e₁) (switch e⟶e'))
...   | step-a μ-evd' e⟶e' = step-d μ-evd' (ξ (ξ-:=ₛᵣ A-static e₁) e⟶e')
...   | done v₂ = step-d μ-evd (β-mono (β-:=ₛ v₁ v₂))
...   | error E-error = step-d μ-evd (ξ-error (ξ-:=ₛᵣ A-static e₁))

progress-normal-store (! e) ν μ-evd with progress-normal-store e ν μ-evd
... | step-d μ-evd' e⟶e' = step-d μ-evd' (ξ ξ-! (switch e⟶e'))
... | step-a μ-evd' e⟶e' = step-d μ-evd' (ξ ξ-! e⟶e')
... | done v = step-d μ-evd (β-mono (β-! v))
... | error E-error = step-d μ-evd (ξ-error ξ-!)

progress-normal-store (e₁ := e₂) ν μ-evd with progress-normal-store e₁ ν μ-evd
... | step-d μ-evd' e⟶e' = step-d μ-evd' (ξ (ξ-:=ₗ e₂) (switch e⟶e'))
... | step-a μ-evd' e⟶e' = step-d μ-evd' (ξ (ξ-:=ₗ e₂) e⟶e')
... | error E-error = step-d μ-evd (ξ-error (ξ-:=ₗ e₂))
... | done v₁ with progress-normal-store e₂ ν μ-evd
...   | step-d μ-evd' e⟶e' = step-d μ-evd' (ξ (ξ-:=ᵣ e₁) (switch e⟶e'))
...   | step-a μ-evd' e⟶e' = step-d μ-evd' (ξ (ξ-:=ᵣ e₁) e⟶e')
...   | done v₂ = step-d μ-evd (β-mono (β-:= v₁ v₂))
...   | error E-error = step-d μ-evd (ξ-error (ξ-:=ᵣ e₁))

progress-normal-store unit _ _ = done (S-Val V-unit)

progress-normal-store error _ _ = error E-error

progress-normal-store (e < c >) ν μ-evd with progress-normal-store e ν μ-evd
... | step-d μ-evd' e⟶e' = step-a μ-evd' (ξ-cast e⟶e')
... | step-a μ-evd' (switch e⟶e') = step-a μ-evd' (ξ-cast e⟶e')
... | step-a μ-evd' (ξ-cast _) = step-d μ-evd' (cast-pure compose-casts)
... | step-a μ-evd' ξ-cast-error = step-d μ-evd' (cast-pure compose-casts)
... | error E-error = step-a μ-evd (ξ-cast-error)
... | done v
  with ⟶ᵤᵣprogress v c ν
...  | step-pure R = step-d μ-evd (cast-pure R)
...  | step-mono R = step-d μ-evd (cast-mono R)
...  | done x = done x
