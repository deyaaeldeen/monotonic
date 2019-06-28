module MonoRef.Dynamics.Simple.CastProgress where

open import Relation.Nullary using (yes ; no)

open import MonoRef.Coercions.Reduction
open import MonoRef.Coercions.Syntax
open import MonoRef.Dynamics.Simple.Reduction
  _⟹_ Inert make-coercion
open import MonoRef.Dynamics.Simple.Value
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Simple
  _⟹_ Inert Active inertP ¬Inert⇒Active make-coercion Inert⇒¬Ref
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Dynamics.Simple.ActiveCastProgress
open import MonoRef.Dynamics.Error
  _⟹_ Inert
open import MonoRef.Static.Types
open import MonoRef.Static.Context


open ParamReduction Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑
open ParamReduction/ν-cast/ν-update/ref/store/⟶ᵤ ν-cast ν-update/ref store _⟶ᵤ_

data CastProgress {Γ Σ A} (M : Σ ∣ Γ ⊢ A) (ν : Store Σ) : Set where

  step : ∀ {Σ'} {ν' : Store Σ'} {N : Σ' ∣ Γ ⊢ A}
    → M , ν ⟶ᵤᵣ N , ν'
      ----------------
    → CastProgress M ν

  done :
      Value M
      ----------------
    → CastProgress M ν


⟶ᵤᵣprogress : ∀ {Γ Σ A B} {e : Σ ∣ Γ ⊢ A}
  → Value e → (c : A ⟹ B) → (ν : Store Σ) → CastProgress (e < c >) ν
⟶ᵤᵣprogress v c ν
  with inertP c
... | yes c-Inert = done (V-cast v c-Inert)
... | no c-¬Inert with ⟶ᵤᵣprogress-active v (¬Inert⇒Active c-¬Inert) ν
...  | step a = step a
