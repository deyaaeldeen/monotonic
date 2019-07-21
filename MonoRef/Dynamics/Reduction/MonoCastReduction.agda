{-

  MonoRef.Dynamics.Reduction.MonoReduction provides a reduction relation for
  casts on monotonic references. It is parameterized over the representation of
  values and casted values.

-}

open import Data.Empty using (⊥)

open import MonoRef.Static.Types

module MonoRef.Dynamics.Reduction.MonoCastReduction
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary using (¬_)

open import MonoRef.Dynamics.EvolvingStore.Precision
  _⟹_ Inert
open import MonoRef.Dynamics.EvolvingStore.Store
  _⟹_ Inert
open import MonoRef.Dynamics.EvolvingStore.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.EvolvingStore.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Types.Relations


module ParamMonoCastReduction
  (SimpleValue       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (Value             : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (DelayedCast       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (ReducibleDelayedCast : ∀ {Σ Γ A} {e : Σ ∣ Γ ⊢ A} → DelayedCast e → Set)
  (ref⟹T : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → Type)
  (ref⟹∈ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ∈ Σ)
  (ref⟹⊑ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ⊑ A)
  where

  open ParamStoreValue Value DelayedCast ReducibleDelayedCast
  open ParamStoreDef StoreValue
  open ParamStore SimpleValue Value DelayedCast ReducibleDelayedCast ref⟹T ref⟹∈ ref⟹⊑

  module ParamMonoCastReduction/ν-cast
    (ν-cast : ∀ {Σ T t'}
      → (T∈Σ : T ∈ Σ)
      → (ν : Store Σ)
      → t' ⊑ (store-lookup-rtti T∈Σ ν)
      → Store (Σ-cast T∈Σ t'))
     where

    infix 3  _,_⟶ₘ_,_

    data _,_⟶ₘ_,_ {Γ Σ} : ∀ {Σ' A}
      → Σ  ∣ Γ ⊢ A → (ν  : Store Σ )
      → Σ' ∣ Γ ⊢ A → (ν' : Store Σ')
      → Set where

      castref1 : ∀ {ν T T₂} {v : Σ ∣ Γ ⊢ Ref T} {c : Ref T ⟹ Ref T₂}
        → (R : SimpleValue v)
        → (rtti∼T₂ : store-lookup-rtti (ref⟹∈ R) ν ∼ T₂)
        → ⊓ rtti∼T₂ ≢ store-lookup-rtti (ref⟹∈ R) ν
          ------------------------------------------------------------------------------------------------
        →   v < c >                             , ν
        ⟶ₘ addr (Σ-cast⟹∈ (ref⟹∈ R) (⊓ rtti∼T₂)) (⊓⟹⊑ᵣ rtti∼T₂) , ν-cast (ref⟹∈ R) ν (⊓⟹⊑ₗ rtti∼T₂)

      castref2 : ∀ {ν T T₂} {v : Σ ∣ Γ ⊢ Ref T} {c : Ref T ⟹ Ref T₂}
        → (R : SimpleValue v)
        → (rtti∼T₂ : store-lookup-rtti/ref R ν ∼ T₂)
        → (eq : ⊓ rtti∼T₂ ≡ store-lookup-rtti/ref R ν)
          ----------------------------------------------------
        →   v < c >                                        , ν
        ⟶ₘ addr (ref-ν⟹∈ R ν) (⊓⟹⊑ᵣ-with-≡ rtti∼T₂ eq) , ν

      castref3 : ∀ {ν T T₂} {v : Σ ∣ Γ ⊢ Ref T} {c : Ref T ⟹ Ref T₂}
        → (R : SimpleValue v)
        → ¬ store-lookup-rtti/ref R ν ∼ T₂
          --------------------------------
        → v < c > , ν ⟶ₘ error , ν

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
