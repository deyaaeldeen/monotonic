module MonoRef.Dynamics.Efficient.Faithful.ActiveCastProgress where

open import Relation.Nullary using (yes ; no)

open import MonoRef.Dynamics.Efficient.Faithful.Coercions
open import MonoRef.Dynamics.Efficient.Faithful.Reduction
open import MonoRef.Dynamics.Efficient.Faithful.Store
open import MonoRef.Dynamics.Efficient.Faithful.TargetWithoutBlame
open import MonoRef.Static.Types.Relations


data ActiveCastProgress {Γ Σ A} (M : Σ ∣ Γ ⊢ A) (ν : Store Σ) : Set where

  step-pure : ∀ {N : Σ ∣ Γ ⊢ A}
    → M ⟶ᵤᶜᵛ N
      ----------------------
    → ActiveCastProgress M ν

  step-mono : ∀ {Σ'} {ν' : Store Σ'} {N : Σ' ∣ Γ ⊢ A}
    → M , ν ⟶ₘ N , ν'
      ----------------------
    → ActiveCastProgress M ν


⟶ᵤᵣprogress-active/middle/sv : ∀ {Γ Σ A B} {e : Σ ∣ Γ ⊢ A} {c : MiddleCoercion A B}
  → SimpleValue e → ActiveMiddle c → (ν : Store Σ) → ActiveCastProgress (e < final (middle c) >) ν
⟶ᵤᵣprogress-active/middle/sv sv A-fail ν = step-pure (⊥ₘ sv)
⟶ᵤᵣprogress-active/middle/sv sv A-id ν = step-pure (ι sv)
⟶ᵤᵣprogress-active/middle/sv (V-pair x y) (A-prod c d) ν
  with x | y
... | S-Val sv₁ | S-Val sv₂ = step-pure (pair-simple sv₁ sv₂)
... | S-Val sv₁ | V-cast sv₂ _ = step-pure (pair-cast-right sv₁ sv₂)
... | V-cast sv₁ _ | S-Val sv₂ = step-pure (pair-cast-left sv₁ sv₂)
... | V-cast sv₁ _ | V-cast sv₂ _ = step-pure (pair-cast-both sv₁ sv₂)
⟶ᵤᵣprogress-active/middle/sv R@(V-addr A∈Σ _) (A-Ref B _) ν
  with ∼-decidable (store-lookup-rtti A∈Σ ν) B
...  | no rtti≁B = step-mono (castref3 R rtti≁B)
...  | yes rtti∼B with ≡Type-decidable (⊓ rtti∼B) (store-lookup-rtti A∈Σ ν)
...      | yes rtti≡B rewrite rtti≡B = step-mono (castref2 R rtti∼B rtti≡B)
...      | no rtti≢B = step-mono (castref1 R rtti∼B rtti≢B)

⟶ᵤᵣprogress-active/final/sv : ∀ {Γ Σ A B} {e : Σ ∣ Γ ⊢ A} {c : FinalCoercion A B}
  → SimpleValue e → ActiveFinal c → (ν : Store Σ) → ActiveCastProgress (e < final c >) ν
⟶ᵤᵣprogress-active/final/sv sv A-fail _ = step-pure (`⊥ sv)
⟶ᵤᵣprogress-active/final/sv sv (A-middle c) ν = ⟶ᵤᵣprogress-active/middle/sv sv c ν

⟶ᵤᵣprogress-active/sv : ∀ {Γ Σ A B} {e : Σ ∣ Γ ⊢ A} {c : A ⟹ B}
  → SimpleValue e → Active c → (ν : Store Σ) → ActiveCastProgress (e < c >) ν
⟶ᵤᵣprogress-active/sv () (A-prjSeq _ _) _
⟶ᵤᵣprogress-active/sv sv (A-final c) ν = ⟶ᵤᵣprogress-active/final/sv sv c ν
