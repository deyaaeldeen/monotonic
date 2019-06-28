module MonoRef.Dynamics.Efficient.Faithful.ProgProgressDef where

open import MonoRef.Coercions.NormalForm.Faithful.Compose
open import MonoRef.Coercions.NormalForm.Faithful.Reduction
open import MonoRef.Coercions.NormalForm.Faithful.Syntax
  renaming (NormalFormCoercion to _⟹_ ; InertNormalForm to Inert
           ; ActiveNormalForm to Active ; inert-normalform-decidable to inertP
           ; ¬Inert⇒Active-normform to ¬Inert⇒Active)
open import MonoRef.Coercions.NormalForm.Faithful.Make renaming (make-normal-form-coercion to make-coercion)
open import MonoRef.Dynamics.Efficient.Faithful.Reduction
open import MonoRef.Dynamics.Efficient.Value
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Efficient
  _⟹_ Inert Active inertP ¬Inert⇒Active make-coercion compose
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Dynamics.Error
  _⟹_ Inert
open import MonoRef.Static.Context


data ProgProgress {Σ A} (M : Σ ∣ ∅ ⊢ A) (ν : Store Σ) : Set where

  step-d : ∀ {Σ'} {ν' : Store Σ'} {N : Σ' ∣ ∅ ⊢ A}
    → (μ-evd : NormalStore ν)
    → disallow / M , ν , μ-evd ⟶ₑ N , ν'
      -----------------------------------
    → ProgProgress M ν

  step-a : ∀ {Σ'} {ν' : Store Σ'} {N : Σ' ∣ ∅ ⊢ A}
    → (μ-evd : NormalStore ν)
    → allow / M , ν , μ-evd ⟶ₑ N , ν'
      --------------------------------
    → ProgProgress M ν

  done :
      Value M
      ----------------
    → ProgProgress M ν

  error :
      Error M
      ----------------
    → ProgProgress M ν
