module MonoRef.Dynamics.Efficient.StdStore.ProgressDef where

open import Data.List using (List)

open import MonoRef.Dynamics.Efficient.Error
open import MonoRef.Dynamics.Efficient.StdStore.SuspendedCast
open import MonoRef.Dynamics.Efficient.StdStore.Reduction
open import MonoRef.Dynamics.Efficient.StdStore.Store
open import MonoRef.Dynamics.Efficient.TargetWithoutBlame
open import MonoRef.Static.Context


data Progress {Σ Σ₂ Σ₃ A} (Q : List (SuspendedCast Σ)) (M : Σ₃ ∣ ∅ ⊢ A) (μ : Store Σ₃ Σ₂) : Set where

  step : ∀ {Σ₄ Σ₅} {μ' : Store Σ₅ Σ₄} {N : Σ₅ ∣ ∅ ⊢ A} {Q' : List (SuspendedCast Σ)}
    → Q , M , μ ⟶ Q' , N , μ'
      ------------------------
    → Progress Q M μ

  done :
      Value M
      --------------
    → Progress Q M μ

  error :
      Error M
      --------------
    → Progress Q M μ
