module MonoRef.Dynamics.Efficient.Faithful.CastProgress where

open import Relation.Nullary using (yes ; no)

open import MonoRef.Dynamics.Efficient.Faithful.ActiveCastProgProgress
open import MonoRef.Dynamics.Efficient.Faithful.Coercions
open import MonoRef.Dynamics.Efficient.Faithful.Reduction
open import MonoRef.Dynamics.Efficient.Faithful.Store
open import MonoRef.Dynamics.Efficient.Faithful.TargetWithoutBlame


data CastProgress {Γ Σ A} (M : Σ ∣ Γ ⊢ A) (ν : Store Σ) : Set where

  step-pure : ∀ {N : Σ ∣ Γ ⊢ A}
    → M ⟶ᵤ N
      ----------------
    → CastProgress M ν

  step-mono : ∀ {Σ'} {ν' : Store Σ'} {N : Σ' ∣ Γ ⊢ A}
    → M , ν ⟶ₘ N , ν'
      ----------------
    → CastProgress M ν

  done :
      Value M
      ----------------
    → CastProgress M ν


⟶ᵤᵣprogress : ∀ {Γ Σ A B} {e : Σ ∣ Γ ⊢ A}
  → Value e → (c : A ⟹ B) → (ν : Store Σ) → CastProgress (e < c >) ν
⟶ᵤᵣprogress (S-Val sv) c ν
  with inertP c
... | yes c-inert = done (V-cast sv c-inert)
... | no c-¬inert with ⟶ᵤᵣprogress-active/sv sv (¬Inert⇒Active c-¬inert) ν
...  | step-pure R = step-pure R
...  | step-mono R = step-mono R
⟶ᵤᵣprogress (V-cast _ _) _ _ = step-pure compose-casts
