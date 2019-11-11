module MonoRef.Dynamics.Simple.EvStore.CastProgress where

open import Relation.Nullary using (yes ; no)

open import MonoRef.Dynamics.Simple.EvStore.ActiveCastProgress
open import MonoRef.Dynamics.Simple.Coercions
open import MonoRef.Dynamics.Simple.EvStore.SReduction
open import MonoRef.Dynamics.Simple.EvStore.Store
open import MonoRef.Dynamics.Simple.TargetWithoutBlame


data CastProgress {Γ Σ A} (M : Σ ∣ Γ ⊢ A) (ν : Store Σ) : Set where

  step : ∀ {Σ'} {ν' : Store Σ'} {N : Σ' ∣ Γ ⊢ A}
    → M , ν ⟶ᶜ N , ν'
      ----------------
    → CastProgress M ν

  done :
      Value M
      ----------------
    → CastProgress M ν


⟶ᶜprogress : ∀ {Γ Σ A B} {e : Σ ∣ Γ ⊢ A}
  → Value e → (c : A ⟹ B) → (ν : Store Σ) → CastProgress (e < c >) ν
⟶ᶜprogress v c ν
  with inertP c
... | yes c-Inert = done (V-cast v c-Inert)
... | no c-¬Inert with ⟶ᶜprogress-active v (¬Inert⇒Active c-¬Inert) ν
...  | step a = step a
