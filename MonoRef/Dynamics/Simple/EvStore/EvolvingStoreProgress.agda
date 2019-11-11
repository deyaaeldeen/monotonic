module MonoRef.Dynamics.Simple.EvStore.EvolvingStoreProgress where

open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Product using (∃ ; ∃-syntax ; -,_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Nullary using (¬_ ; yes ; no)

open import MonoRef.Dynamics.Simple.Coercions
open import MonoRef.Dynamics.Simple.EvStore.ActiveCastProgress
open import MonoRef.Dynamics.Simple.EvStore.Properties
open import MonoRef.Dynamics.Simple.EvStore.SReduction
open import MonoRef.Dynamics.Simple.EvStore.Store
open import MonoRef.Dynamics.Simple.Frames
open import MonoRef.Dynamics.Simple.TargetWithoutBlame
open import MonoRef.Dynamics.Progress.EvolvingStore
  _⟹_ Inert public
open import MonoRef.Static.Context


open ParamEvolvingStoreProgress Value Value valueP DelayedCast v⇑_ ref⟹T ref⟹∈ ref⟹⊑
open ParamEvolvingStoreProgress/ν-cast/RefCoercion/⟶ᶜ/⟶ᶜ⟹⊑ₕ/Frame/plug
  ν-cast (λ {A}{B} _ _ → Ref A B) _,_⟶ᶜ_,_ ⟶ᶜ⟹⊑ₕ Frame plug public


⟶ᶜprogress-scv : ∀ {Σ A} {e : Σ ∣ ∅ ⊢ A}
  → DelayedCast e → ¬ Value e → (ν : Store Σ) → ReducibleDelayedCastProgress e ν
⟶ᶜprogress-scv (v⇑ x) ¬v ν = ⊥-elim (¬v x)
⟶ᶜprogress-scv (cast-val {e = e} cv c) ¬v ν
  with valueP e
... | no ¬v'
    with ⟶ᶜprogress-scv cv ¬v' ν
... | step red = step (cong (ξ-<> c) red)
⟶ᶜprogress-scv (cast-val {e = e} cv c) ¬v ν | yes v
    with inertP c
...   | yes c-inert = ⊥-elim (¬v (V-cast v c-inert))
...   | no ¬c-inert
      with ⟶ᶜprogress-active v (¬Inert⇒Active ¬c-inert) ν
...     | step R = step R
⟶ᶜprogress-scv (cv-pair {e₁ = e₁} {e₂ = e₂} cv₁ cv₂) v ν
  with valueP e₁
... | no ¬v₁
    with ⟶ᶜprogress-scv cv₁ ¬v₁ ν
...   | step red = step (cong (ξ-×ₗ e₂) red)
⟶ᶜprogress-scv (cv-pair {e₁ = e₁} {e₂ = e₂} cv₁ cv₂) v ν | yes v₁
  with valueP e₂
... | no ¬v₂
    with ⟶ᶜprogress-scv cv₂ ¬v₂ ν
...   | step red = step (cong (ξ-×ᵣ e₁) red)
⟶ᶜprogress-scv (cv-pair {e₂ = e₂} cv₁ cv₂) ¬v ν | yes v₁ | yes v₂ =
  ⊥-elim (¬v (V-pair v₁ v₂))

get-ptr : ∀ {Σ Σ' A} {e : Σ ∣ ∅ ⊢ A} {e' : Σ' ∣ ∅ ⊢ A} {ν : Store Σ} {ν' : Store Σ'}
  → (red : e , ν ⟶ᶜ e' , ν') → Maybe (∃[ B ] (B ∈ Σ))
get-ptr (pure _)       = nothing
get-ptr (mono red)     = get-ptr/mono red
get-ptr (cong _ red)   = get-ptr red
get-ptr (cong-error _) = nothing

progress-store : ∀ {Σ Σ' A T} {e : Σ ∣ ∅ ⊢ A} {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → (ν : Store Σ)
  → (T∈Σ : T ∈ Σ)
  → (red : e , ν ⟶ᶜ e' , ν')
  → StoreProgress ν T∈Σ (get-ptr red) ν'
progress-store ν T∈Σ (cong ξ red) = progress-store ν T∈Σ red
progress-store _ _ (cong-error _) = S-no-change
progress-store ν A∈Σ (mono red) = progress-store/mono ν A∈Σ red
progress-store _ _ (pure _) = S-no-change

open ParamEvolvingStoreProgress/Proof
  ⟶ᶜprogress-scv scv⟶ᶜ⟹cv' get-ptr progress-store public
