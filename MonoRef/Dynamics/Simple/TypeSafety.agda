{-

  MonoRef.Dynamics.Simple.TypeSafety assembles a proof of progress and provides
  the full type safety proof.

-}

module MonoRef.Dynamics.Simple.TypeSafety where

open import Data.Nat using (ℕ ; suc)
open import Relation.Nullary using (yes ; no)

open import MonoRef.Dynamics.Simple.Error
open import MonoRef.Dynamics.Simple.EvolvingStoreProgress
open import MonoRef.Dynamics.Simple.NormalStoreProgress
open import MonoRef.Dynamics.Simple.ProgressDef
open import MonoRef.Dynamics.Simple.ReflTransClosure
open import MonoRef.Dynamics.Simple.SValue
open import MonoRef.Dynamics.Simple.Store
open import MonoRef.Dynamics.Simple.TargetWithoutBlame
open import MonoRef.Static.Context


progress : ∀ {Σ A} → (M : Σ ∣ ∅ ⊢ A) → (ν : Store Σ) → Progress M ν
progress e ν
  with normalStoreP ν
... | yes ν-NS = progress-normal-store e ν ν-NS
... | no ν-¬NS = progress-evolving-store ν ν-¬NS

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
