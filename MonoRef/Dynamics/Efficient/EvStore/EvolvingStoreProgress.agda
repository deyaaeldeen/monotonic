module MonoRef.Dynamics.Efficient.EvStore.EvolvingStoreProgress where

open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Product using (∃ ; ∃-syntax ; -,_)
open import Relation.Nullary using (yes ; no ; ¬_)

open import MonoRef.Dynamics.Efficient.Coercions
open import MonoRef.Dynamics.Efficient.EvStore.ActiveCastProgress
open import MonoRef.Dynamics.Efficient.EvStore.Properties
open import MonoRef.Dynamics.Efficient.EvStore.CastReduction
  renaming (_,_⟶_,_ to _,_⟶ᶜ_,_ ; ⟶⟹⊑ₕ to ⟶ᶜ⟹⊑ₕ)
open import MonoRef.Dynamics.Efficient.EvStore.Store
open import MonoRef.Dynamics.Efficient.Frames
open import MonoRef.Dynamics.Efficient.Value
open import MonoRef.Dynamics.Efficient.TargetWithoutBlame
open import MonoRef.Dynamics.Progress.EvolvingStore
  _⟹_ Inert public
open import MonoRef.Static.Context


open ParamEvolvingStoreProgress
  SimpleValue Value valueP DelayedCast v⇑_ ref⟹T ref⟹∈ ref⟹⊑ public
open ParamEvolvingStoreProgress/ν-cast/RefCoercion/⟶ᶜ/⟶ᶜ⟹⊑ₕ/Frame/plug
  ν-cast ((λ {A}{B} C x → final (middle (Ref C x)))) _,_⟶ᶜ_,_ ⟶ᶜ⟹⊑ₕ Frame plug public


⟶ᶜprogress-scv : ∀ {Σ A} {e : Σ ∣ ∅ ⊢ A}
  → DelayedCast e → ¬ Value e → (ν : Store Σ) → ReducibleDelayedCastProgress e ν
⟶ᶜprogress-scv (v⇑ v) ¬v _ = ⊥-elim (¬v v)
⟶ᶜprogress-scv (cast-val v c) ¬v ν
  with inertP c
... | yes c-inert = ⊥-elim (¬v (V-cast v c-inert))
... | no ¬c-inert
    with ⟶ᶜprogress-active/sv v (¬Inert⇒Active ¬c-inert) ν
...   | step-pure R = step (pure R)
...   | step-mono R = step (mono R)
⟶ᶜprogress-scv (cv-pair {e₁ = e₁} {e₂ = e₂} cv₁ cv₂) v ν
  with valueP e₁
... | no ¬v₁
    with ⟶ᶜprogress-scv cv₁ ¬v₁ ν
...   | step red = step (ξ-×ₗ red)
⟶ᶜprogress-scv (cv-pair {e₁ = e₁} {e₂ = e₂} cv₁ cv₂) v ν | yes v₁
  with valueP e₂
... | no ¬v₂
    with ⟶ᶜprogress-scv cv₂ ¬v₂ ν
...   | step red = step (ξ-×ᵣ red)
⟶ᶜprogress-scv (cv-pair {e₂ = e₂} cv₁ cv₂) ¬v ν | yes v₁ | yes v₂ =
  ⊥-elim (¬v (S-Val (V-pair v₁ v₂)))

get-ptr : ∀ {Σ Σ' A} {e : Σ ∣ ∅ ⊢ A} {e' : Σ' ∣ ∅ ⊢ A} {ν : Store Σ} {ν' : Store Σ'}
  → (red : e , ν ⟶ᶜ e' , ν') → Maybe (∃[ B ] (B ∈ Σ))
get-ptr (pure _) = nothing
get-ptr (mono red) = get-ptr/mono red
get-ptr (ξ-×ₗ red) = get-ptr red
get-ptr (ξ-×ᵣ red) = get-ptr red

progress-store : ∀ {Σ Σ' A T} {e : Σ ∣ ∅ ⊢ A} {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → (ν : Store Σ)
  → (T∈Σ : T ∈ Σ)
  → (red : e , ν ⟶ᶜ e' , ν')
  → StoreProgress ν T∈Σ (get-ptr red) ν'
progress-store ν T∈Σ (ξ-×ₗ red) = progress-store ν T∈Σ red
progress-store ν T∈Σ (ξ-×ᵣ red) = progress-store ν T∈Σ red
progress-store ν A∈Σ (mono red) = progress-store/mono ν A∈Σ red
progress-store _ _ (pure _) = S-no-change

open ParamEvolvingStoreProgress/Proof
  ⟶ᶜprogress-scv scv⟶ᶜ⟹cv' get-ptr progress-store public
