{-

  MonoRef.Dynamics.Efficient.StdStore.TypeSafety assembles a proof of progress
  and provides the full type safety proof.

-}

module MonoRef.Dynamics.Efficient.StdStore.TypeSafety where

open import Data.List using (List ; _∷_ ; [])
open import Data.Nat using (ℕ ; suc)
open import Data.Product using (proj₁)
open import Relation.Nullary using (yes ; no)

open import MonoRef.Dynamics.Efficient.Error
open import MonoRef.Dynamics.Efficient.StdStore.SuspendedCast
open import MonoRef.Dynamics.Efficient.StdStore.ReflTransClosure
open import MonoRef.Dynamics.Efficient.StdStore.Reduction
open import MonoRef.Dynamics.Efficient.StdStore.Store
open import MonoRef.Dynamics.Efficient.StdStore.NormalStoreProgress
open import MonoRef.Dynamics.Efficient.StdStore.ProgressDef
open import MonoRef.Dynamics.Efficient.StdStore.ProgProgressDef
open import MonoRef.Dynamics.Efficient.StdStore.SuspendedCastProgress hiding (Progress)
open import MonoRef.Dynamics.Efficient.TargetWithoutBlame
open import MonoRef.Static.Context


progress : ∀ {Σ Σ₁ A} {Σ₁⊑ₕΣ : Σ₁ ⊑ₕ Σ}
  → (Q : List (SuspendedCast Σ))
  → QueueStoreTyping Σ₁⊑ₕΣ Q
  → (M : proj₁ (merge' Σ₁⊑ₕΣ Q) ∣ ∅ ⊢ A)
  → (μ : Store (proj₁ (merge' Σ₁⊑ₕΣ Q)) Σ₁)
  → Progress Q M μ
progress .[] normal e μ
  with progress-normal-store e μ
... | step-d R = step (prog-reduce R)
... | step-a R = step (prog-reduce R)
... | done v = done v
... | error x = error x
progress {Σ₁⊑ₕΣ = Σ₁⊑ₕΣ} (cast A∈Σ B ∷ Q) (evolving Q A∈Σ) e μ
  with suspended-cast-progress Σ₁⊑ₕΣ A∈Σ B Q μ
... | step R = step (state-reduce R)

data Gas : Set where
  gas : ℕ → Gas

data Finished {Σ A} (N : Σ ∣ ∅ ⊢ A) : Set where

  done :
      Value N
      ----------
    → Finished N

  error :
      Error N
      ----------
    → Finished N

  diverge :
      ----------
      Finished N

data TypeSafety {Σ Σ₁ A} {Σ₁⊑ₕΣ : Σ₁ ⊑ₕ Σ}
  (Q : List (SuspendedCast Σ))
  (L : proj₁ (merge' Σ₁⊑ₕΣ Q) ∣ ∅ ⊢ A)
  (μ : Store (proj₁ (merge' Σ₁⊑ₕΣ Q)) Σ₁) : Set where

  intro : ∀ {Σ₂ Σ₃} {Σ₃⊑ₕΣ₂ : Σ₃ ⊑ₕ Σ₂} {Q' : List (SuspendedCast Σ₂)}
            {μ' : Store (proj₁ (merge' Σ₃⊑ₕΣ₂ Q')) Σ₃}
            {N : proj₁ (merge' Σ₃⊑ₕΣ₂ Q') ∣ ∅ ⊢ A}
    → Q , L , μ ↠ Q' , N , μ'
    → Finished N
      ----------------
    → TypeSafety Q L μ

type-safety : ∀ {Σ Σ₁ A} {Σ₁⊑ₕΣ : Σ₁ ⊑ₕ Σ}
  → Gas
  → (Q : List (SuspendedCast Σ))
  → QueueStoreTyping Σ₁⊑ₕΣ Q
  → (L : proj₁ (merge' Σ₁⊑ₕΣ Q) ∣ ∅ ⊢ A)
  → (μ : Store (proj₁ (merge' Σ₁⊑ₕΣ Q)) Σ₁)
  → TypeSafety Q L μ
type-safety (gas 0) Q qst L μ = intro ↠-refl diverge
type-safety (gas (suc x)) Q qst L μ
  with progress Q qst L μ
... | done v = intro ↠-refl (done v)
... | error err = intro ↠-refl (error err)
... | step {Q' = Q'} {μ' = μ'} {N = N} red
   with type-safety (gas x) Q' {!(⟶⟹qst red)!} N μ'
...  | intro steps fin = intro (↠-trans red steps) fin
