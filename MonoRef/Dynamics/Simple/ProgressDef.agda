module MonoRef.Dynamics.Simple.ProgressDef where

open import MonoRef.Coercions.Reduction
open import MonoRef.Coercions.Syntax
open import MonoRef.Dynamics.Simple.Reduction
  _⟹_ Inert make-coercion
open import MonoRef.Dynamics.Simple.Value
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Simple
  _⟹_ Inert Active inertP ¬Inert⇒Active make-coercion Inert⇒¬Ref
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Dynamics.Error
  _⟹_ Inert
open import MonoRef.Static.Context


open ParamReduction Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑
open ParamReduction/ν-cast/ν-update/ref/store/⟶ᵤ ν-cast ν-update/ref store _⟶ᵤ_

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
