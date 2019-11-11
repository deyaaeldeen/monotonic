{-

  MonoRef.Dynamics.Reduction.MonoReduction provides a reduction relation for
  casts on monotonic references. It is parameterized over the representation of
  values and casted values.

-}

open import MonoRef.Static.Types

module MonoRef.Dynamics.Reduction.EvolvingStore.MonoCastReduction
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
open import Relation.Nullary using (¬_)

open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.Store
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Types.Relations


module ParamMonoCastReduction
  (SimpleValue       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (Value             : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (DelayedCast       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (v⇑_ : ∀ {Σ Γ A} {t : Σ ∣ Γ ⊢ A} → Value t → DelayedCast t)
  (ref⟹T : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → Type)
  (ref⟹∈ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ∈ Σ)
  (ref⟹⊑ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ⊑ A)
  where

  open ParamStoreValue DelayedCast
  open ParamStoreDef StoreValue
  open ParamStore SimpleValue Value DelayedCast v⇑_ ref⟹T ref⟹∈ ref⟹⊑

  module ParamMonoCastReduction/ν-cast
    (ν-cast : ∀ {Σ T t'}
      → (T∈Σ : T ∈ Σ)
      → (ν : Store Σ)
      → t' ⊑ (store-lookup-rtti T∈Σ ν)
      → Store (Σ-cast T∈Σ t'))
    (RefCoercion : ∀ {A B} → (C : Type) → C ⊑ B → Ref A ⟹ Ref B)
     where

    infix 3  _,_⟶ₘ_,_

    data _,_⟶ₘ_,_ {Γ Σ} : ∀ {Σ' A}
      → Σ  ∣ Γ ⊢ A → (ν  : Store Σ )
      → Σ' ∣ Γ ⊢ A → (ν' : Store Σ')
      → Set where

      castref1 : ∀ {ν A B C} {v : Σ ∣ Γ ⊢ Ref A} {C⊑B : C ⊑ B}
        → (R : SimpleValue v)
        → (rtti∼C : store-lookup-rtti (ref⟹∈ R) ν ∼ C)
        → ⊓ rtti∼C ≢ store-lookup-rtti (ref⟹∈ R) ν
          ------------------------------------------------------------------------------------------------------------
        → v < RefCoercion C C⊑B >                                           , ν
        ⟶ₘ addr (Σ-cast⟹∈ (ref⟹∈ R) (⊓ rtti∼C)) (⊑-trans (⊓⟹⊑ᵣ rtti∼C) C⊑B) , ν-cast (ref⟹∈ R) ν (⊓⟹⊑ₗ rtti∼C)

      castref2 : ∀ {ν A B C} {v : Σ ∣ Γ ⊢ Ref A} {C⊑B : C ⊑ B}
        → (R : SimpleValue v)
        → (rtti∼C : store-lookup-rtti/ref R ν ∼ C)
        → (eq : ⊓ rtti∼C ≡ store-lookup-rtti/ref R ν)
          -----------------------------------------------------------------------------------------------
        → v < RefCoercion C C⊑B > , ν ⟶ₘ addr (ref-ν⟹∈ R ν) (⊑-trans (⊓⟹⊑ᵣ-with-≡ rtti∼C eq) C⊑B) , ν

      castref3 : ∀ {ν A B C} {v : Σ ∣ Γ ⊢ Ref A} {C⊑B : C ⊑ B}
        → (R : SimpleValue v)
        → ¬ store-lookup-rtti/ref R ν ∼ C
          ------------------------------------------
        → v < RefCoercion C C⊑B > , ν ⟶ₘ error , ν

    ⟶ₘ⟹⊑ₕ : ∀ {Γ Σ Σ' A}
                  {M : Σ ∣ Γ ⊢ A} {ν : Store Σ}
                  {M' : Σ' ∣ Γ ⊢ A} {ν' : Store Σ'}
      → M , ν ⟶ₘ M' , ν'
      → Σ' ⊑ₕ Σ
    ⟶ₘ⟹⊑ₕ {ν = ν} (castref1 R rtti∼T₂ x)
      rewrite (mem-rtti-preserves-Σ (ref⟹∈ R) ν) =
        build-prec (ref⟹∈ R) (⊓⟹⊑ₗ rtti∼T₂)
    ⟶ₘ⟹⊑ₕ (castref2 _ _ _) = ⊑ₕ-refl
    ⟶ₘ⟹⊑ₕ (castref3 _ _) = ⊑ₕ-refl
