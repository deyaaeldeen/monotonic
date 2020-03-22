module MonoRef.Dynamics.Simple.EvStore.NormalStoreProgress where

open import Data.Empty using (⊥-elim)

open import MonoRef.Dynamics.Simple.Coercions
open import MonoRef.Dynamics.Simple.Error
open import MonoRef.Dynamics.Simple.EvStore.CastProgress
open import MonoRef.Dynamics.Simple.EvStore.ProgressDef
open import MonoRef.Dynamics.Simple.EvStore.SReduction
open import MonoRef.Dynamics.Simple.EvStore.Store
open import MonoRef.Dynamics.Simple.Frames
open import MonoRef.Dynamics.Simple.Substitution
open import MonoRef.Dynamics.Simple.TargetWithoutBlame
open import MonoRef.Static.Context
open import MonoRef.Static.Types


progress-normal-store : ∀ {Σ A}
  → (e : Σ ∣ ∅ ⊢ A) → (μ : Store Σ) → NormalStore μ → Progress e μ

progress-normal-store (` ()) _ _

progress-normal-store (ƛ e) _ _ = done (V-ƛ e)

progress-normal-store (e₁ · e₂) ν μ-evd with progress-normal-store e₁ ν μ-evd
... | step (prog-reduce x e₁⟶e₁')  = step (prog-reduce x (cong (ξ-appₗ e₂) e₁⟶e₁'))
... | step (cast-reduce e₁⟶e₁')    = step (cast-reduce (cong (ξ-appₗ e₂) e₁⟶e₁'))
... | step (state-reduce ¬NS _)     = ⊥-elim (¬NS μ-evd)
... | done v with progress-normal-store e₂ ν μ-evd
...   | step (prog-reduce x e₂⟶e₂')  = step (prog-reduce x (cong (ξ-appᵣ e₁) e₂⟶e₂'))
...   | step (cast-reduce e₂⟶e₂')    = step (cast-reduce (cong (ξ-appᵣ e₁) e₂⟶e₂'))
...   | step (state-reduce ¬NS _)     = ⊥-elim (¬NS μ-evd)
progress-normal-store (_ · _) _ μ-evd | done (V-ƛ _) | done v' =
  step (prog-reduce μ-evd (β-pure (β-ƛ v')))
progress-normal-store (_ · _) _ μ-evd | done (V-cast v I-⇒) | done v' =
  step (prog-reduce μ-evd (β-pure (β-ƛₚ v v')))
... | error E-error = step (prog-reduce μ-evd (cong-error (ξ-appᵣ e₁)))
progress-normal-store (.error · e₂) ν μ-evd | error E-error =
  step (prog-reduce μ-evd (cong-error (ξ-appₗ e₂)))

progress-normal-store `zero _ _ = done V-zero

progress-normal-store (`suc e) ν μ-evd with progress-normal-store e ν μ-evd
... | step (prog-reduce x e⟶e')   = step (prog-reduce x (cong ξ-suc e⟶e'))
... | step (cast-reduce e⟶e')     = step (cast-reduce (cong ξ-suc e⟶e'))
... | step (state-reduce ¬NS _)    = ⊥-elim (¬NS μ-evd)
... | done x = done (V-suc x)
... | error E-error = step (prog-reduce μ-evd (cong-error ξ-suc))

progress-normal-store (case p z s) ν μ-evd with progress-normal-store p ν μ-evd
... | step (prog-reduce μ-evd' e⟶e') =
  step (prog-reduce μ-evd' (cong (ξ-caseₚ z s) e⟶e'))
... | step (cast-reduce e⟶e')     = step (cast-reduce (cong (ξ-caseₚ z s) e⟶e'))
... | step (state-reduce ¬NS _)    = ⊥-elim (¬NS μ-evd)
... | error E-error = step (prog-reduce μ-evd (cong-error (ξ-caseₚ z s)))
... | done V-zero = step (prog-reduce μ-evd (β-pure β-zero))
... | done (V-suc v) = step (prog-reduce μ-evd (β-pure (β-suc v)))
... | done (V-cast _ ())

progress-normal-store (ref A e) ν μ-evd with progress-normal-store e ν μ-evd
... | step (prog-reduce x e⟶e')   = step (prog-reduce x (cong (ξ-ref A) e⟶e'))
... | step (cast-reduce e⟶e')     = step (cast-reduce (cong (ξ-ref A) e⟶e'))
... | step (state-reduce ¬NS _)    = ⊥-elim (¬NS μ-evd)
progress-normal-store {Σ = Σ} {A = Ref A} (ref A e) ν μ-evd | done v =
  step (prog-reduce μ-evd (β-mono (β-ref v)))
... | error E-error = step (prog-reduce μ-evd (cong-error (ξ-ref A)))

progress-normal-store (e₁ `× e₂) ν μ-evd with progress-normal-store e₁ ν μ-evd
... | step (prog-reduce x e⟶e')   = step (prog-reduce x (cong (ξ-×ₗ e₂) e⟶e'))
... | step (cast-reduce e⟶e')     = step (cast-reduce (cong (ξ-×ₗ e₂) e⟶e'))
... | step (state-reduce ¬NS _)    = ⊥-elim (¬NS μ-evd)
... | error E-error = step (prog-reduce μ-evd (cong-error (ξ-×ₗ e₂)))
... | done v₁ with progress-normal-store e₂ ν μ-evd
...   | step (prog-reduce x e⟶e')   = step (prog-reduce x (cong (ξ-×ᵣ e₁) e⟶e'))
...   | step (cast-reduce e⟶e')     = step (cast-reduce (cong (ξ-×ᵣ e₁) e⟶e'))
...   | step (state-reduce ¬NS _)    = ⊥-elim (¬NS μ-evd)
...   | done v₂ = done (V-pair v₁ v₂)
...   | error E-error = step (prog-reduce μ-evd (cong-error (ξ-×ᵣ e₁)))

progress-normal-store (π₁ e) ν μ-evd with progress-normal-store e ν μ-evd
... | step (prog-reduce x e⟶e')   = step (prog-reduce x (cong ξ-πₗ e⟶e'))
... | step (cast-reduce e⟶e')     = step (cast-reduce (cong ξ-πₗ e⟶e'))
... | step (state-reduce ¬NS _)    = ⊥-elim (¬NS μ-evd)
... | done (V-pair v₁ v₂) = step (prog-reduce μ-evd (β-pure (β-π₁ v₁ v₂)))
... | done (V-cast _ ())
... | error E-error = step (prog-reduce μ-evd (cong-error ξ-πₗ))

progress-normal-store (π₂ e) ν μ-evd with progress-normal-store e ν μ-evd
... | step (prog-reduce x e⟶e')   = step (prog-reduce x (cong ξ-πᵣ e⟶e'))
... | step (cast-reduce e⟶e')     = step (cast-reduce (cong ξ-πᵣ e⟶e'))
... | step (state-reduce ¬NS _)    = ⊥-elim (¬NS μ-evd)
... | done (V-pair v₁ v₂) = step (prog-reduce μ-evd (β-pure (β-π₂ v₁ v₂)))
... | done (V-cast _ ())
... | error E-error = step (prog-reduce μ-evd (cong-error ξ-πᵣ))

progress-normal-store (addr mem Σ'⊑Σ) _ _ = done (V-addr mem Σ'⊑Σ)

progress-normal-store ((!ₛ e) A-static) ν μ-evd with progress-normal-store e ν μ-evd
... | step (prog-reduce x e⟶e')   = step (prog-reduce x (cong (ξ-!ₛ A-static) e⟶e'))
... | step (cast-reduce e⟶e')     = step (cast-reduce (cong (ξ-!ₛ A-static) e⟶e'))
... | step (state-reduce ¬NS _)    = ⊥-elim (¬NS μ-evd)
... | done v = step (prog-reduce μ-evd (β-mono (β-!ₛ v)))
... | error E-error = step (prog-reduce μ-evd (cong-error (ξ-!ₛ A-static)))

progress-normal-store ((e₁ :=ₛ e₂) A-static) ν μ-evd with progress-normal-store e₁ ν μ-evd
... | step (prog-reduce x e⟶e')   = step (prog-reduce x (cong (ξ-:=ₛₗ A-static e₂) e⟶e'))
... | step (cast-reduce e⟶e')     = step (cast-reduce (cong (ξ-:=ₛₗ A-static e₂) e⟶e'))
... | step (state-reduce ¬NS _)    = ⊥-elim (¬NS μ-evd)
... | error E-error = step (prog-reduce μ-evd (cong-error (ξ-:=ₛₗ A-static e₂)))
... | done v₁ with progress-normal-store e₂ ν μ-evd
...   | step (prog-reduce x e⟶e')   = step (prog-reduce x (cong (ξ-:=ₛᵣ A-static e₁) e⟶e'))
...   | step (cast-reduce e⟶e')     = step (cast-reduce (cong (ξ-:=ₛᵣ A-static e₁) e⟶e'))
...   | step (state-reduce ¬NS _)    = ⊥-elim (¬NS μ-evd)
...   | done v₂ = step (prog-reduce μ-evd (β-mono (β-:=ₛ v₁ v₂)))
...   | error E-error = step (prog-reduce μ-evd (cong-error (ξ-:=ₛᵣ A-static e₁)))

progress-normal-store (! A x e) ν μ-evd with progress-normal-store e ν μ-evd
... | step (prog-reduce w e⟶e')   = step (prog-reduce w (cong (ξ-! A x) e⟶e'))
... | step (cast-reduce e⟶e')     = step (cast-reduce (cong (ξ-! A x) e⟶e'))
... | step (state-reduce ¬NS _)    = ⊥-elim (¬NS μ-evd)
... | done v = step (prog-reduce μ-evd (β-mono (β-! x v)))
... | error E-error = step (prog-reduce μ-evd (cong-error (ξ-! A x)))

progress-normal-store (:= A x e₁ e₂) ν μ-evd with progress-normal-store e₁ ν μ-evd
... | step (prog-reduce w e⟶e')   = step (prog-reduce w (cong (ξ-:=ₗ A x e₂) e⟶e'))
... | step (cast-reduce e⟶e')     = step (cast-reduce (cong (ξ-:=ₗ A x e₂) e⟶e'))
... | step (state-reduce ¬NS _)    = ⊥-elim (¬NS μ-evd)
... | error E-error = step (prog-reduce μ-evd (cong-error (ξ-:=ₗ A x e₂)))
... | done v₁ with progress-normal-store e₂ ν μ-evd
...   | step (prog-reduce w e⟶e')   = step (prog-reduce w (cong (ξ-:=ᵣ A x e₁) e⟶e'))
...   | step (cast-reduce e⟶e')     = step (cast-reduce (cong (ξ-:=ᵣ A x e₁) e⟶e'))
...   | step (state-reduce ¬NS _)    = ⊥-elim (¬NS μ-evd)
...   | done v₂ = step (prog-reduce μ-evd (β-mono (β-:= x v₁ v₂)))
...   | error E-error = step (prog-reduce μ-evd (cong-error (ξ-:=ᵣ A x e₁)))

progress-normal-store unit _ _ = done V-unit

progress-normal-store error _ _ = error E-error

progress-normal-store (e < c >) ν μ-evd with progress-normal-store e ν μ-evd
... | step (prog-reduce x e⟶e')   = step (prog-reduce x (cong (ξ-<> c) e⟶e'))
... | step (cast-reduce e⟶e')     = step (cast-reduce (cong (ξ-<> c) e⟶e'))
... | step (state-reduce ¬NS _)    = ⊥-elim (¬NS μ-evd)
... | error E-error = step (prog-reduce μ-evd (cong-error (ξ-<> c)))
... | done v
  with ⟶ᶜprogress v c ν
...  | step s = step (cast-reduce s)
...  | done x = done x
