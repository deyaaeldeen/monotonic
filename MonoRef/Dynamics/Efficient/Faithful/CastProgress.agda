module MonoRef.Dynamics.Efficient.Faithful.CastProgress where

open import Relation.Nullary using (yes ; no)

open import MonoRef.Coercions.NormalForm.Faithful.Compose
open import MonoRef.Coercions.NormalForm.Faithful.Reduction
open import MonoRef.Coercions.NormalForm.Faithful.Syntax
  renaming (NormalFormCoercion to _⟹_ ; InertNormalForm to Inert
           ; ActiveNormalForm to Active ; inert-normalform-decidable to inertP
           ; ¬Inert⇒Active-normform to ¬Inert⇒Active)
open import MonoRef.Coercions.NormalForm.Faithful.Make renaming (make-normal-form-coercion to make-coercion)
open import MonoRef.Dynamics.Efficient.Faithful.Reduction
open import MonoRef.Dynamics.Efficient.Value
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Efficient
  _⟹_ Inert Active inertP ¬Inert⇒Active make-coercion compose
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Dynamics.Efficient.Faithful.ActiveCastProgress


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
