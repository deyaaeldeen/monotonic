{-

  MonoRef.Dynamics.Efficient.Faithful.TypeSafety assembles a proof of progress
  and provides the full type safety proof.

-}

module MonoRef.Dynamics.Efficient.Faithful.TypeSafety where

open import Data.Nat using (ℕ ; suc)
open import Relation.Nullary using (yes ; no)

open import MonoRef.Dynamics.Efficient.Faithful.Error
open import MonoRef.Dynamics.Efficient.Faithful.ReflTransClosure
open import MonoRef.Dynamics.Efficient.Faithful.Reduction
open import MonoRef.Dynamics.Efficient.Faithful.Store
open import MonoRef.Dynamics.Efficient.Faithful.TargetWithoutBlame
open import MonoRef.Dynamics.Efficient.Faithful.EvolvingStoreProgress
open import MonoRef.Dynamics.Efficient.Faithful.NormalStoreProgress
open import MonoRef.Dynamics.Efficient.Faithful.ProgressDef
open import MonoRef.Dynamics.Efficient.Faithful.ProgProgressDef
open import MonoRef.Static.Context


progress : ∀ {Σ A} → (M : Σ ∣ ∅ ⊢ A) → (ν : Store Σ) → Progress M ν
progress e ν
  with normalStoreP ν
... | no ν-¬NS = progress-evolving-store ν ν-¬NS
... | yes ν-NS
  with progress-normal-store e ν ν-NS
... | step-d μ-evd R = step (prog-reduce μ-evd R)
... | step-a μ-evd R = step (prog-reduce μ-evd R)
... | done v = done v
... | error x = error x

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

data TypeSafety {Σ A} (L : Σ ∣ ∅ ⊢ A) (ν : Store Σ) : Set where

  intro : ∀ {Σ'} {N : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
    → L , ν ↠ N , ν'
    → Finished N
      --------------
    → TypeSafety L ν

type-safety : ∀ {Σ A} → Gas → (L : Σ ∣ ∅ ⊢ A) → (ν : Store Σ) → TypeSafety L ν
type-safety (gas 0) e ν = intro ↠-refl diverge
type-safety (gas (suc x)) e ν
  with progress e ν
... | done v = intro ↠-refl (done v)
... | error err = intro ↠-refl (error err)
... | step {ν' = ν'} {N = N} red
   with type-safety (gas x) N ν'
...  | intro steps fin = intro (↠-trans red steps) fin
