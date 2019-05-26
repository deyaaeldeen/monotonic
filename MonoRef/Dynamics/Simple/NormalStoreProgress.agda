module MonoRef.Dynamics.Simple.NormalStoreProgress where

open import Data.Empty using (⊥-elim)

open import MonoRef.Coercions.Reduction
open import MonoRef.Coercions.Syntax
open import MonoRef.Dynamics.Simple.Frames
  _⟹_ Inert
open import MonoRef.Dynamics.Simple.Reduction
  _⟹_ Inert make-coercion Inert⇒¬Ref
open import MonoRef.Dynamics.Store.Simple
  _⟹_ Inert Active inertP ¬Inert⇒Active make-coercion Inert⇒¬Ref
open import MonoRef.Dynamics.Substitution
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Dynamics.Simple.CastProgress
open import MonoRef.Dynamics.Simple.ProgressDef
open import MonoRef.Dynamics.Error
  _⟹_ Inert
open import MonoRef.Dynamics.Simple.Value
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types


open ParamReduction Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑
open ParamReduction/ν-cast/ν-update/ref/store/⟶ᵤ ν-cast ν-update/ref store _⟶ᵤ_

progress-normal-store : ∀ {Σ A}
  → (e : Σ ∣ ∅ ⊢ A) → (μ : Store Σ) → NormalStore μ → Progress e μ

progress-normal-store (` ()) _ _

progress-normal-store (ƛ e) _ _ = done (V-ƛ e)

progress-normal-store (e₁ · e₂) ν μ-evd with progress-normal-store e₁ ν μ-evd
... | step (prog-reduce x e₁⟶e₁')    = step (prog-reduce x (cong (ξ-appₗ e₂) e₁⟶e₁'))
... | step (cast-reduce e₁⟶e₁')      = step (cast-reduce (cong (ξ-appₗ e₂) e₁⟶e₁'))
... | step (error ¬NS _ _ _)          = ⊥-elim (¬NS μ-evd)
... | step (hcast ¬NS _ _ _ _)        = ⊥-elim (¬NS μ-evd)
... | step (hmcast ¬NS _ _ _ _ _ _ _) = ⊥-elim (¬NS μ-evd)
... | step (hdrop ¬NS _ _ _ _ _)      = ⊥-elim (¬NS μ-evd)
... | done v with progress-normal-store e₂ ν μ-evd
...   | step (prog-reduce x e₂⟶e₂')    = step (prog-reduce x (cong (ξ-appᵣ e₁) e₂⟶e₂'))
...   | step (cast-reduce e₂⟶e₂')      = step (cast-reduce (cong (ξ-appᵣ e₁) e₂⟶e₂'))
...   | step (error ¬NS _ _ _)          = ⊥-elim (¬NS μ-evd)
...   | step (hcast ¬NS _ _ _ _)        = ⊥-elim (¬NS μ-evd)
...   | step (hmcast ¬NS _ _ _ _ _ _ _) = ⊥-elim (¬NS μ-evd)
...   | step (hdrop ¬NS _ _ _ _ _)      = ⊥-elim (¬NS μ-evd)
progress-normal-store (_ · _) _ μ-evd | done (V-ƛ _) | done v' =
  step (prog-reduce μ-evd (β-pure (β-ƛ v')))
progress-normal-store (_ · _) _ μ-evd | done v@(V-cast _ I-⇒) | done v' =
  step (prog-reduce μ-evd (β-pure (β-ƛₚ v v')))
... | error E-error = step (prog-reduce μ-evd (cong-error (ξ-appᵣ e₁)))
progress-normal-store (.error · e₂) ν μ-evd | error E-error =
  step (prog-reduce μ-evd (cong-error (ξ-appₗ e₂)))

progress-normal-store `zero _ _ = done V-zero

progress-normal-store (`suc e) ν μ-evd with progress-normal-store e ν μ-evd
... | step (prog-reduce x e⟶e')     = step (prog-reduce x (cong ξ-suc e⟶e'))
... | step (cast-reduce e⟶e')       = step (cast-reduce (cong ξ-suc e⟶e'))
... | step (error ¬NS _ _ _)          = ⊥-elim (¬NS μ-evd)
... | step (hcast ¬NS _ _ _ _)        = ⊥-elim (¬NS μ-evd)
... | step (hmcast ¬NS _ _ _ _ _ _ _) = ⊥-elim (¬NS μ-evd)
... | step (hdrop ¬NS _ _ _ _ _)      = ⊥-elim (¬NS μ-evd)
... | done x = done (V-suc x)
... | error E-error = step (prog-reduce μ-evd (cong-error ξ-suc))

progress-normal-store (case p z s) ν μ-evd with progress-normal-store p ν μ-evd
... | step (prog-reduce μ-evd' e⟶e') =
  step (prog-reduce μ-evd' (cong (ξ-caseₚ z s) e⟶e'))
... | step (cast-reduce e⟶e')       = step (cast-reduce (cong (ξ-caseₚ z s) e⟶e'))
... | step (error ¬NS _ _ _)          = ⊥-elim (¬NS μ-evd)
... | step (hcast ¬NS _ _ _ _)        = ⊥-elim (¬NS μ-evd)
... | step (hmcast ¬NS _ _ _ _ _ _ _) = ⊥-elim (¬NS μ-evd)
... | step (hdrop ¬NS _ _ _ _ _)      = ⊥-elim (¬NS μ-evd)
... | error E-error = step (prog-reduce μ-evd (cong-error (ξ-caseₚ z s)))
... | done V-zero = step (prog-reduce μ-evd (β-pure β-zero))
... | done (V-suc v) = step (prog-reduce μ-evd (β-pure (β-suc v)))
... | done (V-cast _ ())

progress-normal-store (ref e) ν μ-evd with progress-normal-store e ν μ-evd
... | step (prog-reduce x e⟶e')     = step (prog-reduce x (cong ξ-ref e⟶e'))
... | step (cast-reduce e⟶e')       = step (cast-reduce (cong ξ-ref e⟶e'))
... | step (error ¬NS _ _ _)          = ⊥-elim (¬NS μ-evd)
... | step (hcast ¬NS _ _ _ _)        = ⊥-elim (¬NS μ-evd)
... | step (hmcast ¬NS _ _ _ _ _ _ _) = ⊥-elim (¬NS μ-evd)
... | step (hdrop ¬NS _ _ _ _ _)      = ⊥-elim (¬NS μ-evd)
progress-normal-store {Σ = Σ} {A = Ref A} (ref e) ν μ-evd | done v =
  step (prog-reduce μ-evd (β-mono (β-ref v)))
... | error E-error = step (prog-reduce μ-evd (cong-error ξ-ref))

progress-normal-store (e₁ `× e₂) ν μ-evd with progress-normal-store e₁ ν μ-evd
... | step (prog-reduce x e⟶e')     = step (prog-reduce x (cong (ξ-×ₗ e₂) e⟶e'))
... | step (cast-reduce e⟶e')       = step (cast-reduce (cong (ξ-×ₗ e₂) e⟶e'))
... | step (error ¬NS _ _ _)          = ⊥-elim (¬NS μ-evd)
... | step (hcast ¬NS _ _ _ _)        = ⊥-elim (¬NS μ-evd)
... | step (hmcast ¬NS _ _ _ _ _ _ _) = ⊥-elim (¬NS μ-evd)
... | step (hdrop ¬NS _ _ _ _ _)      = ⊥-elim (¬NS μ-evd)
... | error E-error = step (prog-reduce μ-evd (cong-error (ξ-×ₗ e₂)))
... | done v₁ with progress-normal-store e₂ ν μ-evd
...   | step (prog-reduce x e⟶e')     = step (prog-reduce x (cong (ξ-×ᵣ e₁) e⟶e'))
...   | step (cast-reduce e⟶e')       = step (cast-reduce (cong (ξ-×ᵣ e₁) e⟶e'))
...   | step (error ¬NS _ _ _)          = ⊥-elim (¬NS μ-evd)
...   | step (hcast ¬NS _ _ _ _)        = ⊥-elim (¬NS μ-evd)
...   | step (hmcast ¬NS _ _ _ _ _ _ _) = ⊥-elim (¬NS μ-evd)
...   | step (hdrop ¬NS _ _ _ _ _)      = ⊥-elim (¬NS μ-evd)
...   | done v₂ = done (V-pair v₁ v₂)
...   | error E-error = step (prog-reduce μ-evd (cong-error (ξ-×ᵣ e₁)))

progress-normal-store (π₁ e) ν μ-evd with progress-normal-store e ν μ-evd
... | step (prog-reduce x e⟶e')     = step (prog-reduce x (cong ξ-πₗ e⟶e'))
... | step (cast-reduce e⟶e')       = step (cast-reduce (cong ξ-πₗ e⟶e'))
... | step (error ¬NS _ _ _)          = ⊥-elim (¬NS μ-evd)
... | step (hcast ¬NS _ _ _ _)        = ⊥-elim (¬NS μ-evd)
... | step (hmcast ¬NS _ _ _ _ _ _ _) = ⊥-elim (¬NS μ-evd)
... | step (hdrop ¬NS _ _ _ _ _)      = ⊥-elim (¬NS μ-evd)
... | done (V-pair v₁ v₂) = step (prog-reduce μ-evd (β-pure (β-π₁ v₁ v₂)))
... | done (V-cast _ ())
... | error E-error = step (prog-reduce μ-evd (cong-error ξ-πₗ))

progress-normal-store (π₂ e) ν μ-evd with progress-normal-store e ν μ-evd
... | step (prog-reduce x e⟶e')     = step (prog-reduce x (cong ξ-πᵣ e⟶e'))
... | step (cast-reduce e⟶e')       = step (cast-reduce (cong ξ-πᵣ e⟶e'))
... | step (error ¬NS _ _ _)          = ⊥-elim (¬NS μ-evd)
... | step (hcast ¬NS _ _ _ _)        = ⊥-elim (¬NS μ-evd)
... | step (hmcast ¬NS _ _ _ _ _ _ _) = ⊥-elim (¬NS μ-evd)
... | step (hdrop ¬NS _ _ _ _ _)      = ⊥-elim (¬NS μ-evd)
... | done (V-pair v₁ v₂) = step (prog-reduce μ-evd (β-pure (β-π₂ v₁ v₂)))
... | done (V-cast _ ())
... | error E-error = step (prog-reduce μ-evd (cong-error ξ-πᵣ))

progress-normal-store (addr mem Σ'⊑Σ) _ _ = done (V-addr mem Σ'⊑Σ)

progress-normal-store ((!ₛ e) A-static) ν μ-evd with progress-normal-store e ν μ-evd
... | step (prog-reduce x e⟶e')     = step (prog-reduce x (cong (ξ-!ₛ A-static) e⟶e'))
... | step (cast-reduce e⟶e')       = step (cast-reduce (cong (ξ-!ₛ A-static) e⟶e'))
... | step (error ¬NS _ _ _)          = ⊥-elim (¬NS μ-evd)
... | step (hcast ¬NS _ _ _ _)        = ⊥-elim (¬NS μ-evd)
... | step (hmcast ¬NS _ _ _ _ _ _ _) = ⊥-elim (¬NS μ-evd)
... | step (hdrop ¬NS _ _ _ _ _)      = ⊥-elim (¬NS μ-evd)
... | done v = step (prog-reduce μ-evd (β-mono (β-!ₛ v)))
... | error E-error = step (prog-reduce μ-evd (cong-error (ξ-!ₛ A-static)))

progress-normal-store ((e₁ :=ₛ e₂) A-static) ν μ-evd with progress-normal-store e₁ ν μ-evd
... | step (prog-reduce x e⟶e')     = step (prog-reduce x (cong (ξ-:=ₛₗ A-static e₂) e⟶e'))
... | step (cast-reduce e⟶e')       = step (cast-reduce (cong (ξ-:=ₛₗ A-static e₂) e⟶e'))
... | step (error ¬NS _ _ _)          = ⊥-elim (¬NS μ-evd)
... | step (hcast ¬NS _ _ _ _)        = ⊥-elim (¬NS μ-evd)
... | step (hmcast ¬NS _ _ _ _ _ _ _) = ⊥-elim (¬NS μ-evd)
... | step (hdrop ¬NS _ _ _ _ _)      = ⊥-elim (¬NS μ-evd)
... | error E-error = step (prog-reduce μ-evd (cong-error (ξ-:=ₛₗ A-static e₂)))
... | done v₁ with progress-normal-store e₂ ν μ-evd
...   | step (prog-reduce x e⟶e')     = step (prog-reduce x (cong (ξ-:=ₛᵣ A-static e₁) e⟶e'))
...   | step (cast-reduce e⟶e')       = step (cast-reduce (cong (ξ-:=ₛᵣ A-static e₁) e⟶e'))
...   | step (error ¬NS _ _ _)          = ⊥-elim (¬NS μ-evd)
...   | step (hcast ¬NS _ _ _ _)        = ⊥-elim (¬NS μ-evd)
...   | step (hmcast ¬NS _ _ _ _ _ _ _) = ⊥-elim (¬NS μ-evd)
...   | step (hdrop ¬NS _ _ _ _ _)      = ⊥-elim (¬NS μ-evd)
...   | done v₂ = step (prog-reduce μ-evd (β-mono (β-:=ₛ v₁ v₂)))
...   | error E-error = step (prog-reduce μ-evd (cong-error (ξ-:=ₛᵣ A-static e₁)))

progress-normal-store (! e) ν μ-evd with progress-normal-store e ν μ-evd
... | step (prog-reduce x e⟶e')     = step (prog-reduce x (cong ξ-! e⟶e'))
... | step (cast-reduce e⟶e')       = step (cast-reduce (cong ξ-! e⟶e'))
... | step (error ¬NS _ _ _)          = ⊥-elim (¬NS μ-evd)
... | step (hcast ¬NS _ _ _ _)        = ⊥-elim (¬NS μ-evd)
... | step (hmcast ¬NS _ _ _ _ _ _ _) = ⊥-elim (¬NS μ-evd)
... | step (hdrop ¬NS _ _ _ _ _)      = ⊥-elim (¬NS μ-evd)
... | done v = step (prog-reduce μ-evd (β-mono (β-! v)))
... | error E-error = step (prog-reduce μ-evd (cong-error ξ-!))

progress-normal-store (e₁ := e₂) ν μ-evd with progress-normal-store e₁ ν μ-evd
... | step (prog-reduce x e⟶e')     = step (prog-reduce x (cong (ξ-:=ₗ e₂) e⟶e'))
... | step (cast-reduce e⟶e')       = step (cast-reduce (cong (ξ-:=ₗ e₂) e⟶e'))
... | step (error ¬NS _ _ _)          = ⊥-elim (¬NS μ-evd)
... | step (hcast ¬NS _ _ _ _)        = ⊥-elim (¬NS μ-evd)
... | step (hmcast ¬NS _ _ _ _ _ _ _) = ⊥-elim (¬NS μ-evd)
... | step (hdrop ¬NS _ _ _ _ _)      = ⊥-elim (¬NS μ-evd)
... | error E-error = step (prog-reduce μ-evd (cong-error (ξ-:=ₗ e₂)))
... | done v₁ with progress-normal-store e₂ ν μ-evd
...   | step (prog-reduce x e⟶e')     = step (prog-reduce x (cong (ξ-:=ᵣ e₁) e⟶e'))
...   | step (cast-reduce e⟶e')       = step (cast-reduce (cong (ξ-:=ᵣ e₁) e⟶e'))
...   | step (error ¬NS _ _ _)          = ⊥-elim (¬NS μ-evd)
...   | step (hcast ¬NS _ _ _ _)        = ⊥-elim (¬NS μ-evd)
...   | step (hmcast ¬NS _ _ _ _ _ _ _) = ⊥-elim (¬NS μ-evd)
...   | step (hdrop ¬NS _ _ _ _ _)      = ⊥-elim (¬NS μ-evd)
...   | done v₂ = step (prog-reduce μ-evd (β-mono (β-:= v₁ v₂)))
...   | error E-error = step (prog-reduce μ-evd (cong-error (ξ-:=ᵣ e₁)))

progress-normal-store unit _ _ = done V-unit

progress-normal-store error _ _ = error E-error

progress-normal-store (e < c >) ν μ-evd with progress-normal-store e ν μ-evd
... | step (prog-reduce x e⟶e')     = step (prog-reduce x (cong (ξ-<> c) e⟶e'))
... | step (cast-reduce e⟶e')       = step (cast-reduce (cong (ξ-<> c) e⟶e'))
... | step (error ¬NS _ _ _)          = ⊥-elim (¬NS μ-evd)
... | step (hcast ¬NS _ _ _ _)        = ⊥-elim (¬NS μ-evd)
... | step (hmcast ¬NS _ _ _ _ _ _ _) = ⊥-elim (¬NS μ-evd)
... | step (hdrop ¬NS _ _ _ _ _)      = ⊥-elim (¬NS μ-evd)
... | error E-error = step (prog-reduce μ-evd (cong-error (ξ-<> c)))
... | done v
  with ⟶ᵤᵣprogress v c ν
...  | step s = step (cast-reduce s)
...  | done x = done x
...  | error x = error x
