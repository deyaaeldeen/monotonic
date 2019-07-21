module MonoRef.Dynamics.Simple.ProgressDef where

open import MonoRef.Dynamics.Simple.Error
open import MonoRef.Dynamics.Simple.SReduction
open import MonoRef.Dynamics.Simple.Store
open import MonoRef.Dynamics.Simple.TargetWithoutBlame
open import MonoRef.Static.Context


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
