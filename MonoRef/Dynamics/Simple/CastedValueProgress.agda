module MonoRef.Dynamics.Simple.CastedValueProgress where

open import Data.Empty using (⊥-elim)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Nullary using (¬_)

open import MonoRef.Coercions.Reduction
open import MonoRef.Coercions.Syntax
open import MonoRef.Dynamics.Simple.Reduction
  _⟹_ Inert make-coercion
open import MonoRef.Dynamics.Simple.Frames
  _⟹_ Inert
open import MonoRef.Dynamics.Simple.Value
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Simple
  _⟹_ Inert Active inertP ¬Inert⇒Active make-coercion Inert⇒¬Ref
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Dynamics.Simple.ActiveCastProgress


open ParamReduction Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑
open ParamReduction/ν-cast/ν-update/ref/store/⟶ᵤ ν-cast ν-update/ref store _⟶ᵤ_


⟶ᵤᵣprogress-scv : ∀ {Γ Σ A} {e : Σ ∣ Γ ⊢ A} {cv : CastedValue e}
  → StrongCastedValue cv → (ν : Store Σ) → ActiveCastProgress e ν
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
