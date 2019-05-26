module MonoRef.Dynamics.Simple.CastedValueProgress where

open import Data.Empty using (⊥-elim)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Nullary using (¬_)

open import MonoRef.Coercions.Reduction
open import MonoRef.Coercions.Syntax
open import MonoRef.Dynamics.Simple.Reduction
  _⟹_ Inert make-coercion Inert⇒¬Ref 
open import MonoRef.Dynamics.Simple.Frames
  _⟹_ Inert
open import MonoRef.Dynamics.Simple.Value
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Simple
  _⟹_ Inert Active inertP ¬Inert⇒Active make-coercion Inert⇒¬Ref
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Dynamics.Simple.ActiveCastProgress
open import MonoRef.Dynamics.Simple.ProgressDef
open import MonoRef.Dynamics.Error
  _⟹_ Inert
open import MonoRef.Static.Context


open ParamReduction Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑
open ParamReduction/ν-cast/ν-update/ref/store/⟶ᵤ ν-cast ν-update/ref store _⟶ᵤ_


⟶ᵤᵣprogress-scv : ∀ {Γ Σ A} {e : Σ ∣ Γ ⊢ A} {cv : CastedValue e}
  → StrongCastedValue cv → (ν : Store Σ) → ¬ NormalStore ν → ActiveCastProgress e ν
⟶ᵤᵣprogress-scv (SCV-cast v ac) ν _ = ⟶ᵤᵣprogress-active v ac ν
⟶ᵤᵣprogress-scv (SCV-ccast cv scv c) ν ¬ν-NS
  with ⟶ᵤᵣprogress-scv scv ν ¬ν-NS
... | step red = step (cong (ξ-<> c) red)
⟶ᵤᵣprogress-scv (SCV-pair _ _ p) ν ¬ν-NS with p
⟶ᵤᵣprogress-scv (SCV-pair _ _ _) ν ¬ν-NS | inj₂ (inj₁ ⟨ v₁ , scv₂ ⟩)
  with ⟶ᵤᵣprogress-scv scv₂ ν ¬ν-NS
⟶ᵤᵣprogress-scv (SCV-pair {e₁ = e₁} _ _ _) ν ¬ν-NS | inj₂ (inj₁ _)  | step scv₂⟶scv₂' =
  step (cong (ξ-×ᵣ e₁) scv₂⟶scv₂')
⟶ᵤᵣprogress-scv (SCV-pair {e₂ = e₂} _ _ _) ν ¬ν-NS | inj₂ (inj₂ ⟨ scv₁ , _ ⟩)
  with ⟶ᵤᵣprogress-scv scv₁ ν ¬ν-NS
⟶ᵤᵣprogress-scv (SCV-pair {e₂ = e₂} _ _ _) ν ¬ν-NS | inj₂ (inj₂ _) | step scv₁⟶scv₁' =
  step (cong (ξ-×ₗ e₂) scv₁⟶scv₁')
⟶ᵤᵣprogress-scv (SCV-pair {e₂ = e₂} _ _ _) ν ¬ν-NS | inj₁ ⟨ scv₁ , _ ⟩
  with ⟶ᵤᵣprogress-scv scv₁ ν ¬ν-NS
⟶ᵤᵣprogress-scv (SCV-pair {e₂ = e₂} _ _ _) ν ¬ν-NS | inj₁ _ | step scv₁⟶scv₁' =
  step (cong (ξ-×ₗ e₂) scv₁⟶scv₁')

⟶ᵤᵣprogress-cv : ∀ {Σ A} {e : Σ ∣ ∅ ⊢ A}
  → CastedValue e → (ν : Store Σ) → ¬ NormalStore ν → Progress e ν
⟶ᵤᵣprogress-cv (v⇑ v) _ _ = done v
⟶ᵤᵣprogress-cv (cast-val v ac) ν ¬ν-NS
  with ⟶ᵤᵣprogress-active v ac ν
... | step s = step (cast-reduce s)
⟶ᵤᵣprogress-cv (cast-cval cv scv c) ν ¬ν-NS
  with ⟶ᵤᵣprogress-scv scv ν ¬ν-NS
... | step red = step (cast-reduce (cong (ξ-<> c) red))
⟶ᵤᵣprogress-cv (cv-pair cv₁ cv₂ p) ν ¬ν-NS with ⟶ᵤᵣprogress-cv cv₁ ν ¬ν-NS
... | step (prog-reduce μ-evd _) = ⊥-elim (¬ν-NS μ-evd)
⟶ᵤᵣprogress-cv (cv-pair {e₂ = e₂} _ _ _) _ _ | step (cast-reduce e⟶e') =
  step (cast-reduce (cong (ξ-×ₗ e₂) e⟶e'))
... | step (error ¬NS mem red err) = step (error ¬NS mem red err)
... | step (hcast ¬NS mem red x y) = step (hcast ¬NS mem red x y)
... | step (hmcast ¬NS a b c d e f g) = step (hmcast ¬NS a b c d e f g)
... | step (hdrop ¬NS mem scv red a b) = step (hdrop ¬NS mem scv red a b)
⟶ᵤᵣprogress-cv (cv-pair {e₂ = e₂} _ _ _) _ _ | error E-error =
  step (cast-reduce (cong-error (ξ-×ₗ e₂)))
... | done v₁ with ⟶ᵤᵣprogress-cv cv₂ ν ¬ν-NS
...   | step (prog-reduce μ-evd _) = ⊥-elim (¬ν-NS μ-evd)
⟶ᵤᵣprogress-cv (cv-pair {e₁ = e₁} _ _ _) _ _ | done _ | step (cast-reduce e⟶e') =
  step (cast-reduce (cong (ξ-×ᵣ e₁) e⟶e'))
...   | step (error ¬NS mem red err) = step (error ¬NS mem red err)
...   | step (hcast ¬NS mem red x y) = step (hcast ¬NS mem red x y)
... | step (hmcast ¬NS a b c d e f g) = step (hmcast ¬NS a b c d e f g)
...   | step (hdrop ¬NS mem scv red a b) = step (hdrop ¬NS mem scv red a b)
⟶ᵤᵣprogress-cv (cv-pair {e₁ = e₁} _ _ _) _ _ | done _ | error E-error =
  step (cast-reduce (cong-error (ξ-×ᵣ e₁)))
...   | done v₂ = done (V-pair v₁ v₂)
