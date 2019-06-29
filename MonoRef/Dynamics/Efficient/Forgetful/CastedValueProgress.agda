module MonoRef.Dynamics.Efficient.Forgetful.CastedValueProgress where

open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁ ; inj₂)

open import MonoRef.Coercions.NormalForm.Forgetful.CastedValueReduction
open import MonoRef.Coercions.NormalForm.Forgetful.Compose
open import MonoRef.Coercions.NormalForm.Forgetful.Reduction
open import MonoRef.Coercions.NormalForm.Forgetful.Syntax
  renaming (NormalFormCoercion to _⟹_ ; InertNormalForm to Inert
           ; ActiveNormalForm to Active ; inert-normalform-decidable to inertP
           ; ¬Inert⇒Active-normform to ¬Inert⇒Active)
open import MonoRef.Coercions.NormalForm.Forgetful.Make renaming (make-normal-form-coercion to make-coercion)
open import MonoRef.Dynamics.Efficient.Forgetful.Reduction
  _⟹_ Inert Active make-coercion
open import MonoRef.Dynamics.Efficient.Value
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Efficient
  _⟹_ Inert Active inertP ¬Inert⇒Active make-coercion compose
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Dynamics.Efficient.Forgetful.ActiveCastProgress


open ParamReduction SimpleValue Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑
open ParamReduction/ν-cast/ν-update/ref/store/⟶ᵤ/⟶ᵤᶜᵛ ν-cast ν-update/ref store _⟶ᵤ_ _⟶ᵤᶜᵛ_


data StrongCastedValueProgress {Γ Σ A} (M : Σ ∣ Γ ⊢ A) (ν : Store Σ) : Set where

  step : ∀ {Σ'} {ν' : Store Σ'} {N : Σ' ∣ Γ ⊢ A}
    → M , ν ⟶ᵤᵣ N , ν'
      -----------------------------
    → StrongCastedValueProgress M ν

⟶ᵤᵣprogress-scv : ∀ {Γ Σ A} {e : Σ ∣ Γ ⊢ A} {cv : CastedValue e}
  → StrongCastedValue cv → (ν : Store Σ) → StrongCastedValueProgress e ν
⟶ᵤᵣprogress-scv (SCV-cast v ac) ν
  with ⟶ᵤᵣprogress-active/sv v ac ν
... | step-pure R = step (pure R)
... | step-mono R = step (mono R)
⟶ᵤᵣprogress-scv (SCV-pair _ _ p) ν
  with p
... | inj₂ (inj₁ ⟨ v₁ , scv₂ ⟩)
   with ⟶ᵤᵣprogress-scv scv₂ ν
...  | step scv₂⟶scv₂' = step (ξ-×ᵣ scv₂⟶scv₂')
⟶ᵤᵣprogress-scv (SCV-pair {e₂ = e₂} _ _ _) ν | inj₂ (inj₂ ⟨ scv₁ , _ ⟩)
   with ⟶ᵤᵣprogress-scv scv₁ ν
...  | step scv₁⟶scv₁' = step (ξ-×ₗ scv₁⟶scv₁')
⟶ᵤᵣprogress-scv (SCV-pair {e₂ = e₂} _ _ _) ν | inj₁ ⟨ scv₁ , _ ⟩
   with ⟶ᵤᵣprogress-scv scv₁ ν
...  | step scv₁⟶scv₁' = step (ξ-×ₗ scv₁⟶scv₁')
