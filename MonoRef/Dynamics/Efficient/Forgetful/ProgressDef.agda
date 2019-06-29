module MonoRef.Dynamics.Efficient.Forgetful.ProgressDef where

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
open import MonoRef.Dynamics.Error
  _⟹_ Inert
open import MonoRef.Static.Context


open ParamReduction SimpleValue Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑
open ParamReduction/ν-cast/ν-update/ref/store/⟶ᵤ/⟶ᵤᶜᵛ ν-cast ν-update/ref store _⟶ᵤ_ _⟶ᵤᶜᵛ_

data Progress {Σ A} (M : Σ ∣ ∅ ⊢ A) (ν : Store Σ) : Set where

  step : ∀ {Σ'} {ν' : Store Σ'} {N : Σ' ∣ ∅ ⊢ A}
    → M , ν ⟶ₛ N , ν'
      ----------------
    → Progress M ν

  done :
      Value M
      ------------
    → Progress M ν

  error :
      Error M
      ------------
    → Progress M ν
