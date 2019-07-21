module MonoRef.Dynamics.Simple.ActiveCastProgress where

open import Relation.Nullary using (yes ; no)

open import MonoRef.Dynamics.Simple.Coercions
open import MonoRef.Dynamics.Simple.SReduction
open import MonoRef.Dynamics.Simple.Store
open import MonoRef.Dynamics.Simple.TargetWithoutBlame
open import MonoRef.Static.Types.Relations


data ActiveCastProgress {Γ Σ A} (M : Σ ∣ Γ ⊢ A) (ν : Store Σ) : Set where

  step : ∀ {Σ'} {ν' : Store Σ'} {N : Σ' ∣ Γ ⊢ A}
    → M , ν ⟶ᵤᵣ N , ν'
      ----------------------
    → ActiveCastProgress M ν

⟶ᵤᵣprogress-active : ∀ {Γ Σ A B} {e : Σ ∣ Γ ⊢ A} {c : A ⟹ B}
  → Value e → Active c → (ν : Store Σ) → ActiveCastProgress (e < c >) ν
⟶ᵤᵣprogress-active v A-ι _ = step (pure (ι v))
⟶ᵤᵣprogress-active (V-cast v (I-inj {A} _)) (A-prj {B} _) _ =
  step (pure (!? v))
⟶ᵤᵣprogress-active (V-pair v₁ v₂) A-× _ =
  step (pure (`× v₁ v₂))
⟶ᵤᵣprogress-active (V-cast _ ()) A-× _
⟶ᵤᵣprogress-active {Σ = Σ} R@(V-addr A∈Σ _) (A-Ref {B = B}) ν
  with ∼-decidable (store-lookup-rtti A∈Σ ν) B
...  | no rtti≁B =
  step (mono (castref3 R rtti≁B))
...  | yes rtti∼B with ≡Type-decidable (⊓ rtti∼B) (store-lookup-rtti A∈Σ ν)
...      | yes rtti≡B rewrite rtti≡B =
  step (mono (castref2 R rtti∼B rtti≡B))
...      | no rtti≢B =
  step (mono (castref1 R rtti∼B rtti≢B))
⟶ᵤᵣprogress-active (V-cast _ ()) A-Ref _
⟶ᵤᵣprogress-active v (A-⊥ {A≁B = A≁B}) _ = step (pure (`⊥ v A≁B))
