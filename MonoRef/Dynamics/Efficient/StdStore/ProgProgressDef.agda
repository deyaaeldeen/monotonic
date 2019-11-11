module MonoRef.Dynamics.Efficient.StdStore.ProgProgressDef where

open import Data.List using (List)

open import MonoRef.Dynamics.Efficient.StdStore.SuspendedCast
open import MonoRef.Dynamics.Efficient.StdStore.Reduction
open import MonoRef.Dynamics.Efficient.StdStore.Store
open import MonoRef.Dynamics.Efficient.Error
open import MonoRef.Dynamics.Efficient.TargetWithoutBlame
open import MonoRef.Static.Context


data ProgProgress {Σ A} (M : Σ ∣ ∅ ⊢ A) (μ : Store Σ Σ) : Set where

  step-d : ∀ {Σ' Σ''} {μ' : Store Σ'' Σ'} {N : Σ'' ∣ ∅ ⊢ A} {Q : List (SuspendedCast Σ)}
    → disallow / M , μ ⟶ₑ Q , N , μ'
      -------------------------------
    → ProgProgress M μ

  step-a : ∀ {Σ' Σ''} {μ' : Store Σ'' Σ'} {N : Σ'' ∣ ∅ ⊢ A} {Q : List (SuspendedCast Σ)}
    → allow / M , μ ⟶ₑ Q , N , μ'
      ----------------------------
    → ProgProgress M μ

  done :
      Value M
      ----------------
    → ProgProgress M μ

  error :
      Error M
      ----------------
    → ProgProgress M μ
