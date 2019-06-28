open import Data.Empty using (⊥)

open import MonoRef.Static.Types

module MonoRef.Dynamics.MonoStoreProgress
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Product using (∃ ; ∃-syntax ; -,_)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import MonoRef.Dynamics.Reduction.MonoCastReduction
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Ptr
open import MonoRef.Dynamics.Store.Store
  _⟹_ Inert
open import MonoRef.Dynamics.Store.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


module ParamMonoStoreProgress
  (SimpleValue       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (Value             : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (CastedValue       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (StrongCastedValue : ∀ {Σ Γ A} {e : Σ ∣ Γ ⊢ A} → CastedValue e → Set)
  (ref⟹T : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → Type)
  (ref⟹∈ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ∈ Σ)
  (ref⟹⊑ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ⊑ A)
  where

  open ParamStoreValue Value CastedValue StrongCastedValue
  open ParamStoreDef StoreValue
  open ParamStore SimpleValue Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑
  open ParamMonoCastReduction SimpleValue Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑

  module ParamMonoStoreProgress/ν-cast
    (ν-cast : ∀ {Σ T t'}
      → (T∈Σ : T ∈ Σ)
      → (ν : Store Σ)
      → t' ⊑ (store-lookup-rtti T∈Σ ν)
      → Store (Σ-cast T∈Σ t'))
      where

    open ParamMonoCastReduction/ν-cast ν-cast

    data StoreProgress {Σ A} (ν : Store Σ) (A∈Σ : A ∈ Σ) :
      ∀ {Σ'} → Maybe (∃[ B ] (B ∈ Σ)) → (ν : Store Σ') → Set where

      S-no-change : StoreProgress ν A∈Σ nothing ν

      S-cyclic : ∀ {B}
        → (B⊑A : B ⊑ store-lookup-rtti A∈Σ ν)
        → B ≢ store-lookup-rtti A∈Σ ν
        → StoreProgress ν A∈Σ (just (-, A∈Σ)) (ν-cast A∈Σ ν B⊑A)

      S-acyclic : ∀ {B C}
        → (B∈Σ : B ∈ Σ)
        → PtrInEquality A∈Σ B∈Σ
        → (C⊑B : C ⊑ store-lookup-rtti B∈Σ ν)
        → StoreProgress ν A∈Σ (just (-, B∈Σ)) (ν-cast B∈Σ ν C⊑B)

    get-ptr/mono : ∀ {Σ Σ' A} {e : Σ ∣ ∅ ⊢ A} {e' : Σ' ∣ ∅ ⊢ A} {ν : Store Σ} {ν' : Store Σ'}
      → (red : e , ν ⟶ₘ e' , ν') → (Maybe (∃[ B ] (B ∈ Σ)))
    get-ptr/mono (castref1 R _ _) = just (-, ref⟹∈ R)
    get-ptr/mono (castref2 _ _ _) = nothing
    get-ptr/mono (castref3 _ _)   = nothing
