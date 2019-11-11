module MonoRef.Dynamics.Simple.EvStore.ActiveCastProgress where

open import Relation.Nullary using (yes ; no)

open import MonoRef.Dynamics.Simple.Coercions
open import MonoRef.Dynamics.Simple.EvStore.SReduction
open import MonoRef.Dynamics.Simple.EvStore.Store
open import MonoRef.Dynamics.Simple.TargetWithoutBlame
open import MonoRef.Static.Types.Relations


data ActiveCastProgress {Γ Σ A} (M : Σ ∣ Γ ⊢ A) (ν : Store Σ) : Set where

  step : ∀ {Σ'} {ν' : Store Σ'} {N : Σ' ∣ Γ ⊢ A}
    → M , ν ⟶ᶜ N , ν'
      ----------------------
    → ActiveCastProgress M ν

⟶ᶜprogress-active : ∀ {Γ Σ A B} {e : Σ ∣ Γ ⊢ A} {c : A ⟹ B}
  → Value e → Active c → (ν : Store Σ) → ActiveCastProgress (e < c >) ν
⟶ᶜprogress-active v A-ι _ = step (pure (ι v))
⟶ᶜprogress-active (V-cast v (I-inj _)) (A-prj _) _ =
  step (pure (!? v))
⟶ᶜprogress-active (V-pair v₁ v₂) A-× _ =
  step (pure (`× v₁ v₂))
⟶ᶜprogress-active (V-cast _ ()) A-× _
⟶ᶜprogress-active {Σ = Σ} R@(V-addr A∈Σ _) (A-Ref {B = B}) ν
  with ∼-decidable (store-lookup-rtti A∈Σ ν) B
...  | no rtti≁B =
  step (mono (castref3 {C⊑B = ⊑-reflexive} R rtti≁B))
...  | yes rtti∼B with ≡Type-decidable (⊓ rtti∼B) (store-lookup-rtti A∈Σ ν)
...      | yes rtti≡B rewrite rtti≡B =
  step (mono (castref2 {C⊑B = ⊑-reflexive} R rtti∼B rtti≡B))
...      | no rtti≢B =
  step (mono (castref1 {C⊑B = ⊑-reflexive} R rtti∼B rtti≢B))
⟶ᶜprogress-active (V-cast _ ()) A-Ref _
⟶ᶜprogress-active v (A-⊥ {A≁B = A≁B}) _ = step (pure (`⊥ v A≁B))
