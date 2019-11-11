module MonoRef.Dynamics.Efficient.EvStore.ProgProgressDef where

open import MonoRef.Dynamics.Efficient.Error
open import MonoRef.Dynamics.Efficient.EvStore.Reduction
open import MonoRef.Dynamics.Efficient.EvStore.Store
open import MonoRef.Dynamics.Efficient.TargetWithoutBlame
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
