module MonoRef.Dynamics.Simple.EvStore.ProgressDef where

open import MonoRef.Dynamics.Simple.Error
open import MonoRef.Dynamics.Simple.EvStore.SReduction
open import MonoRef.Dynamics.Simple.EvStore.Store
open import MonoRef.Dynamics.Simple.TargetWithoutBlame
open import MonoRef.Static.Context


data Progress {Σ A} (M : Σ ∣ ∅ ⊢ A) (ν : Store Σ) : Set where

  step : ∀ {Σ'} {ν' : Store Σ'} {N : Σ' ∣ ∅ ⊢ A}
    → M , ν ⟶ N , ν'
      ---------------
    → Progress M ν

  done :
      Value M
      ------------
    → Progress M ν

  error :
      Error M
      ------------
    → Progress M ν
