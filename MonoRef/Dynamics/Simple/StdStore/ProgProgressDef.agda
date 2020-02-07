module MonoRef.Dynamics.Simple.StdStore.ProgProgressDef where

open import Data.List using (List)

open import MonoRef.Dynamics.Simple.Error
open import MonoRef.Dynamics.Simple.StdStore.SuspendedCast
open import MonoRef.Dynamics.Simple.StdStore.Reduction
open import MonoRef.Dynamics.Simple.StdStore.Store
open import MonoRef.Dynamics.Simple.TargetWithoutBlame
open import MonoRef.Dynamics.Simple.Value
open import MonoRef.Static.Context


data ProgProgress {Σ A} (M : Σ ∣ ∅ ⊢ A) (μ : Store Σ Σ) : Set where

  step : ∀ {Σ' Σ''} {μ' : Store Σ'' Σ'} {N : Σ'' ∣ ∅ ⊢ A} {Q : List (SuspendedCast Σ)}
    → M , μ ⟶ₑ Q , N , μ'
      --------------------
    → ProgProgress M μ

  done :
      Value M
      ----------------
    → ProgProgress M μ

  error :
      Error M
      ----------------
    → ProgProgress M μ
