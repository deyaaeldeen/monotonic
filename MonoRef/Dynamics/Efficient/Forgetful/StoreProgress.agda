module MonoRef.Dynamics.Efficient.Forgetful.StoreProgress where

open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Product using (∃ ; ∃-syntax ; -,_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≢_ ; refl)
open import Relation.Nullary using (yes ; no)

open import MonoRef.Coercions.NormalForm.Forgetful.CastedValueReduction
open import MonoRef.Coercions.NormalForm.Forgetful.Compose
open import MonoRef.Coercions.NormalForm.Forgetful.Reduction
open import MonoRef.Coercions.NormalForm.Forgetful.Syntax
  renaming (NormalFormCoercion to _⟹_ ; InertNormalForm to Inert
           ; ActiveNormalForm to Active ; inert-normalform-decidable to inertP
           ; ¬Inert⇒Active-normform to ¬Inert⇒Active)
open import MonoRef.Coercions.NormalForm.Forgetful.Make renaming (make-normal-form-coercion to make-coercion)
open import MonoRef.Dynamics.MonoStoreProgress
  _⟹_ Inert
open import MonoRef.Dynamics.Efficient.Forgetful.Reduction
  _⟹_ Inert Active make-coercion
open import MonoRef.Dynamics.Efficient.Value
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Efficient
  _⟹_ Inert Active inertP ¬Inert⇒Active make-coercion compose
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


open ParamReduction SimpleValue Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑
open ParamReduction/ν-cast/ν-update/ref/store/⟶ᵤ/⟶ᵤᶜᵛ ν-cast ν-update/ref store _⟶ᵤ_ _⟶ᵤᶜᵛ_
open ParamMonoStoreProgress SimpleValue Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑
open ParamMonoStoreProgress/ν-cast ν-cast public

get-ptr : ∀ {Σ Σ' A} {e : Σ ∣ ∅ ⊢ A} {e' : Σ' ∣ ∅ ⊢ A} {ν : Store Σ} {ν' : Store Σ'}
  → (red : e , ν ⟶ᵤᵣ e' , ν') → Maybe (∃[ B ] (B ∈ Σ))
get-ptr (pure _) = nothing
get-ptr (mono red) = get-ptr/mono red
get-ptr (ξ-×ₗ red) = get-ptr red
get-ptr (ξ-×ᵣ red) = get-ptr red

progress-store/mono : ∀ {Σ Σ' A T} {e : Σ ∣ ∅ ⊢ A} {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → (ν : Store Σ)
  → (T∈Σ : T ∈ Σ)
  → (red : e , ν ⟶ₘ e' , ν')
  → StoreProgress ν T∈Σ (get-ptr/mono red) ν'
progress-store/mono {T = T} ν B∈Σ (castref1 (V-addr {A = A} A∈Σ _) rtti∼T₂ ⊓rtti∼T₂≢rtti)
  with ≡Type-decidable T A
... | no T≢A = S-acyclic A∈Σ (PIE-ptr T≢A A∈Σ) (⊓⟹⊑ₗ rtti∼T₂)
... | yes refl
   with ≡Ptr-decidable A∈Σ B∈Σ
...  | yes refl = S-cyclic (⊓⟹⊑ₗ rtti∼T₂) ⊓rtti∼T₂≢rtti
...  | no A∈Σ≢B∈Σ = S-acyclic A∈Σ (PIE-ty A∈Σ A∈Σ≢B∈Σ) (⊓⟹⊑ₗ rtti∼T₂)
progress-store/mono _ _ (castref2 _ _ _) = S-no-change
progress-store/mono _ _ (castref3 _ _) = S-no-change

progress-store : ∀ {Σ Σ' A T} {e : Σ ∣ ∅ ⊢ A} {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → (ν : Store Σ)
  → (T∈Σ : T ∈ Σ)
  → (red : e , ν ⟶ᵤᵣ e' , ν')
  → StoreProgress ν T∈Σ (get-ptr red) ν'
progress-store ν T∈Σ (ξ-×ₗ red) = progress-store ν T∈Σ red
progress-store ν T∈Σ (ξ-×ᵣ red) = progress-store ν T∈Σ red
progress-store ν A∈Σ (mono red) = progress-store/mono ν A∈Σ red
progress-store _ _ (pure _) = S-no-change
