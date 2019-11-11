module MonoRef.Dynamics.Efficient.EvStore.ProgressDef where

open import MonoRef.Dynamics.Efficient.Error
open import MonoRef.Dynamics.Efficient.EvStore.Reduction
open import MonoRef.Dynamics.Efficient.EvStore.Store
open import MonoRef.Dynamics.Efficient.TargetWithoutBlame
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
