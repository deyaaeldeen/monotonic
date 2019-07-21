module MonoRef.Dynamics.Simple.StoreProgress where

open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Product using (∃ ; ∃-syntax ; -,_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≢_ ; refl)
open import Relation.Nullary using (yes ; no)


open import MonoRef.Dynamics.Simple.Coercions
open import MonoRef.Dynamics.Simple.SReduction
open import MonoRef.Dynamics.Simple.Store
open import MonoRef.Dynamics.Simple.TargetWithoutBlame
open import MonoRef.Dynamics.Simple.MonoStoreProgress
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


get-ptr : ∀ {Σ Σ' A} {e : Σ ∣ ∅ ⊢ A} {e' : Σ' ∣ ∅ ⊢ A} {ν : Store Σ} {ν' : Store Σ'}
  → (red : e , ν ⟶ᵤᵣ e' , ν') → Maybe (∃[ B ] (B ∈ Σ))
get-ptr (pure _)       = nothing
get-ptr (mono red)     = get-ptr/mono red
get-ptr (cong _ red)   = get-ptr red
get-ptr (cong-error _) = nothing

progress-store/mono : ∀ {Σ Σ' A T} {e : Σ ∣ ∅ ⊢ A} {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → (ν : Store Σ)
  → (T∈Σ : T ∈ Σ)
  → (red : e , ν ⟶ₘ e' , ν')
  → StoreProgress ν T∈Σ (get-ptr/mono red) ν'
progress-store/mono _ _ (castref1 (V-cast _ c) _ _) = ⊥-elim (Inert⇒¬Ref c)
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
progress-store ν T∈Σ (cong ξ red) = progress-store ν T∈Σ red
progress-store _ _ (cong-error _) = S-no-change
progress-store ν A∈Σ (mono red) = progress-store/mono ν A∈Σ red
progress-store _ _ (pure _) = S-no-change
