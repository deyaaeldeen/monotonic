module MonoRef.Dynamics.Efficient.StdStore.ProgProgressDef where

open import Data.List using (List)
open import Data.Product using (proj₁)

open import MonoRef.Dynamics.Efficient.StdStore.SuspendedCast
open import MonoRef.Dynamics.Efficient.StdStore.Reduction
open import MonoRef.Dynamics.Efficient.StdStore.Store
open import MonoRef.Dynamics.Efficient.Error
open import MonoRef.Dynamics.Efficient.TargetWithoutBlame
open import MonoRef.Static.Context


data ProgProgress {Σ A} (M : Σ ∣ ∅ ⊢ A) (μ : Store Σ Σ) : Set where

  step-d : ∀ {Σ'} {Q : List (SuspendedCast Σ')} {μ' : Store (proj₁ (merge Q)) Σ'}
             {N : proj₁ (merge Q) ∣ ∅ ⊢ A}
    → disallow / M , μ ⟶ₑ Q , N , μ'
      -------------------------------
    → ProgProgress M μ

  step-a : ∀ {Σ'} {Q : List (SuspendedCast Σ')} {μ' : Store (proj₁ (merge Q)) Σ'}
             {N : proj₁ (merge Q) ∣ ∅ ⊢ A}
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
