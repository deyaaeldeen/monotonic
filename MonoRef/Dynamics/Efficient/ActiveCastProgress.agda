module MonoRef.Dynamics.Efficient.ActiveCastProgress where

open import Relation.Nullary using (yes ; no)

open import MonoRef.Coercions.NormalForm.Compose
open import MonoRef.Coercions.NormalForm.Reduction
open import MonoRef.Coercions.NormalForm.Syntax
  renaming (NormalFormCoercion to _⟹_ ; InertNormalForm to Inert
           ; ActiveNormalForm to Active ; inert-normalform-decidable to inertP
           ; ¬Inert⇒Active-normform to ¬Inert⇒Active)
open import MonoRef.Coercions.NormalForm.Make renaming (make-normal-form-coercion to make-coercion)
open import MonoRef.Dynamics.Efficient.Reduction
  _⟹_ Inert Active make-coercion Inert⇒¬Ref
open import MonoRef.Dynamics.Efficient.Value
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Efficient
  _⟹_ Inert Active inertP ¬Inert⇒Active make-coercion Inert⇒¬Ref compose
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Types.Relations


open ParamReduction SimpleValue Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑
open ParamReduction/ν-cast/ν-update/ref/store/⟶ᵤ ν-cast ν-update/ref store _⟶ᵤ_


data ActiveCastProgress {Γ Σ A} (M : Σ ∣ Γ ⊢ A) (ν : Store Σ) : Set where

  step-pure : ∀ {N : Σ ∣ Γ ⊢ A}
    → M ⟶ᵤ N
      ----------------------
    → ActiveCastProgress M ν

  step-mono : ∀ {Σ'} {ν' : Store Σ'} {N : Σ' ∣ Γ ⊢ A}
    → M , ν ⟶ₘ N , ν'
      ----------------------
    → ActiveCastProgress M ν


⟶ᵤᵣprogress-active/middle/sv : ∀ {Γ Σ A B} {e : Σ ∣ Γ ⊢ A} {c : MiddleCoercion A B}
  → SimpleValue e → ActiveMiddle c → (ν : Store Σ) → ActiveCastProgress (e < final (middle c) >) ν
⟶ᵤᵣprogress-active/middle/sv sv A-id ν = step-pure (ι sv)
⟶ᵤᵣprogress-active/middle/sv (V-pair x y) (A-prod c d) ν = step-pure (`× x y)
⟶ᵤᵣprogress-active/middle/sv R@(V-addr A∈Σ _) (A-Ref B) ν
  with ∼-decidable (store-lookup-rtti A∈Σ ν) B
...  | no rtti≁B =
  step-mono (castref3 (S-Val R) rtti≁B)
...  | yes rtti∼B with ≡Type-decidable (⊓ rtti∼B) (store-lookup-rtti A∈Σ ν)
...      | yes rtti≡B rewrite rtti≡B =
  step-mono (castref2 (S-Val R) rtti∼B rtti≡B)
...      | no rtti≢B =
  step-mono (castref1 (S-Val R) rtti∼B rtti≢B)

⟶ᵤᵣprogress-active/final/sv : ∀ {Γ Σ A B} {e : Σ ∣ Γ ⊢ A} {c : FinalCoercion A B}
  → SimpleValue e → ActiveFinal c → (ν : Store Σ) → ActiveCastProgress (e < final c >) ν
⟶ᵤᵣprogress-active/final/sv sv A-fail _ = step-pure (`⊥ sv)
⟶ᵤᵣprogress-active/final/sv sv (A-middle c) ν = ⟶ᵤᵣprogress-active/middle/sv sv c ν

⟶ᵤᵣprogress-active/sv : ∀ {Γ Σ A B} {e : Σ ∣ Γ ⊢ A} {c : A ⟹ B}
  → SimpleValue e → Active c → (ν : Store Σ) → ActiveCastProgress (e < c >) ν
⟶ᵤᵣprogress-active/sv () (A-prjSeq _ _) _
⟶ᵤᵣprogress-active/sv sv (A-final c) ν = ⟶ᵤᵣprogress-active/final/sv sv c ν

⟶ᵤᵣprogress-active : ∀ {Γ Σ A B} {e : Σ ∣ Γ ⊢ A} {c : A ⟹ B}
  → Value e → Active c → (ν : Store Σ) → ActiveCastProgress (e < c >) ν
⟶ᵤᵣprogress-active (S-Val sv) c ν = ⟶ᵤᵣprogress-active/sv sv c ν
⟶ᵤᵣprogress-active (V-cast _ _) _ _ =
  step-pure compose-casts
