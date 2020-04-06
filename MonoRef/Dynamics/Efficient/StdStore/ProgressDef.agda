module MonoRef.Dynamics.Efficient.StdStore.ProgressDef where

open import Data.List using (List)
open import Data.Product using (proj₁)

open import MonoRef.Dynamics.Efficient.Error
open import MonoRef.Dynamics.Efficient.StdStore.SuspendedCast
open import MonoRef.Dynamics.Efficient.StdStore.Reduction
open import MonoRef.Dynamics.Efficient.StdStore.Store
open import MonoRef.Dynamics.Efficient.TargetWithoutBlame
open import MonoRef.Static.Context


data Progress {Σ Σ₁ A} {Σ₁⊑ₕΣ : Σ₁ ⊑ₕ Σ}
  (Q : List (SuspendedCast Σ))
  (M : proj₁ (merge' Σ₁⊑ₕΣ Q) ∣ ∅ ⊢ A)
  (μ : Store (proj₁ (merge' Σ₁⊑ₕΣ Q)) Σ₁) : Set where

  step : ∀ {Σ₂ Σ₃} {Σ₃⊑ₕΣ₂ : Σ₃ ⊑ₕ Σ₂} {Q' : List (SuspendedCast Σ₂)}
           {μ' : Store (proj₁ (merge' Σ₃⊑ₕΣ₂ Q')) Σ₃}
           {N : proj₁ (merge' Σ₃⊑ₕΣ₂ Q') ∣ ∅ ⊢ A}
    → Q , M , μ ⟶ Q' , N , μ'
      -------------------------
    → Progress Q M μ

  done :
      Value M
      --------------
    → Progress Q M μ

  error :
      Error M
      --------------
    → Progress Q M μ
