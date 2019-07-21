module MonoRef.Dynamics.Simple.ReducibleDelayedCastProgress where

open import Data.Empty using (⊥-elim)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Nullary using (¬_)

open import MonoRef.Dynamics.Simple.ActiveCastProgress
open import MonoRef.Dynamics.Simple.Coercions
open import MonoRef.Dynamics.Simple.Frames
open import MonoRef.Dynamics.Simple.SReduction
open import MonoRef.Dynamics.Simple.Store
open import MonoRef.Dynamics.Simple.TargetWithoutBlame


⟶ᵤᵣprogress-scv : ∀ {Γ Σ A} {e : Σ ∣ Γ ⊢ A} {cv : DelayedCast e}
  → ReducibleDelayedCast cv → (ν : Store Σ) → ActiveCastProgress e ν
⟶ᵤᵣprogress-scv (SCV-cast v ac) ν = ⟶ᵤᵣprogress-active v ac ν
⟶ᵤᵣprogress-scv (SCV-ccast cv scv c) ν
  with ⟶ᵤᵣprogress-scv scv ν
... | step red = step (cong (ξ-<> c) red)
⟶ᵤᵣprogress-scv (SCV-pair _ _ p) ν with p
⟶ᵤᵣprogress-scv (SCV-pair _ _ _) ν | inj₂ (inj₁ ⟨ _ , scv₂ ⟩)
  with ⟶ᵤᵣprogress-scv scv₂ ν
⟶ᵤᵣprogress-scv (SCV-pair {e₁ = e₁} _ _ _) _ | _ | step scv₂⟶scv₂' =
  step (cong (ξ-×ᵣ e₁) scv₂⟶scv₂')
⟶ᵤᵣprogress-scv (SCV-pair _ _ _) ν | inj₂ (inj₂ ⟨ scv₁ , _ ⟩)
  with ⟶ᵤᵣprogress-scv scv₁ ν
⟶ᵤᵣprogress-scv (SCV-pair {e₂ = e₂} _ _ _) _ | _ | step scv₁⟶scv₁' =
  step (cong (ξ-×ₗ e₂) scv₁⟶scv₁')
⟶ᵤᵣprogress-scv (SCV-pair _ _ _) ν | inj₁ ⟨ scv₁ , _ ⟩
  with ⟶ᵤᵣprogress-scv scv₁ ν
⟶ᵤᵣprogress-scv (SCV-pair {e₂ = e₂} _ _ _) _ | _ | step scv₁⟶scv₁' =
  step (cong (ξ-×ₗ e₂) scv₁⟶scv₁')
