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
  (Inert⇒¬Ref : ∀ {A B} {c : A ⟹ Ref B} → Inert c → ⊥)
  where

open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary using (¬_)

open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Store
  _⟹_ Inert Inert⇒¬Ref
open import MonoRef.Dynamics.Store.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Types.Relations


module ParamMonoCastReduction
  (Value             : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (CastedValue       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (StrongCastedValue : ∀ {Σ Γ A} {e : Σ ∣ Γ ⊢ A} → CastedValue e → Set)
  (ref⟹T : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : Value v) → Type)
  (ref⟹∈ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : Value v) → ref⟹T V ∈ Σ)
  (ref⟹⊑ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : Value v) → ref⟹T V ⊑ A)
  where

  open ParamStoreValue Value CastedValue StrongCastedValue
  open ParamStoreDef StoreValue
  open ParamStore Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑

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
        → (R : Value v)
        → (rtti∼T₂ : store-lookup-rtti (ref⟹∈ R) ν ∼ T₂)
        → ⊓ rtti∼T₂ ≢ store-lookup-rtti (ref⟹∈ R) ν
          ------------------------------------------------------------------------------------------------
        →   v < c >                             , ν
        ⟶ₘ addr (Σ-cast⟹∈ (ref⟹∈ R) (⊓ rtti∼T₂)) (⊓⟹⊑ᵣ rtti∼T₂) , ν-cast (ref⟹∈ R) ν (⊓⟹⊑ₗ rtti∼T₂)

      castref2 : ∀ {ν T T₂} {v : Σ ∣ Γ ⊢ Ref T} {c : Ref T ⟹ Ref T₂}
        → (R : Value v)
        → (rtti∼T₂ : store-lookup-rtti/ref R ν ∼ T₂)
        → (eq : ⊓ rtti∼T₂ ≡ store-lookup-rtti/ref R ν)
          ----------------------------------------------------
        →   v < c >                                        , ν
        ⟶ₘ addr (ref-ν⟹∈ R ν) (⊓⟹⊑ᵣ-with-≡ rtti∼T₂ eq) , ν

      castref3 : ∀ {ν T T₂} {v : Σ ∣ Γ ⊢ Ref T} {c : Ref T ⟹ Ref T₂}
        → (R : Value v)
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
