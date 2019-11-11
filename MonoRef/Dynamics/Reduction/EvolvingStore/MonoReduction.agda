open import Data.Empty using (⊥ ; ⊥-elim)

open import MonoRef.Static.Types

module MonoRef.Dynamics.Reduction.EvolvingStore.MonoReduction
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.List using (_∷ʳ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Nullary using (Dec)

-- standard library++
open import Data.List.Prefix renaming (_⊑_ to _⊑ₗ_ ; ⊑-refl to ⊑ₗ-refl)
open import Data.List.Properties.Extra using (∈-∷ʳ)

open import MonoRef.Dynamics.Store.Evolving.Normal
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.Store
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


module ParamMonoReduction
  (SimpleValue       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (Value             : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (valueP : ∀ {Σ A} → (e : Σ ∣ ∅ ⊢ A) → Dec (Value e))
  (DelayedCast       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (v⇑_ : ∀ {Σ Γ A} {t : Σ ∣ Γ ⊢ A} → Value t → DelayedCast t)
  (ref⟹T : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → Type)
  (ref⟹∈ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ∈ Σ)
  (ref⟹⊑ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ⊑ A)
  (make-coercion : ∀ A B → A ⟹ B)
  where

  open ParamStoreValue DelayedCast
  open ParamStoreDef StoreValue
  open ParamStore SimpleValue Value DelayedCast v⇑_ ref⟹T ref⟹∈ ref⟹⊑
  open ParamNormal Value valueP DelayedCast

  module ParamMonoReduction/ν-update/ref/store
    (ν-update/ref : ∀ {Σ Γ}
      → (A : Type)
      → {r : Σ ∣ Γ ⊢ Ref A}
      → (R : SimpleValue r)
      → Store Σ
      → ∀ {v : Σ ∣ ∅ ⊢ A}
      → Value v
      → Store Σ)
    (store : ∀ {Σ A} {v : Σ ∣ ∅ ⊢ A} → Value v → Store Σ → Store (Σ ∷ʳ A))
    where

    infix 3  _,_,_⟶ᵢₘ_,_

    data _,_,_⟶ᵢₘ_,_ {Σ} : ∀ {Σ' A}
      → Σ  ∣ ∅ ⊢ A → (μ : Store Σ ) → NormalStore μ
      → Σ' ∣ ∅ ⊢ A → (ν : Store Σ')
      → Set

    ⟶ᵢₘ⟹⊑ₗ : ∀ {Σ Σ' A} {μ : Store Σ} {ν' : Store Σ'} {μ-evd : NormalStore μ}
                 {M : Σ ∣ ∅ ⊢ A} {M' : Σ' ∣ ∅ ⊢ A}
      → M , μ , μ-evd ⟶ᵢₘ M' , ν'
      → Σ ⊑ₗ Σ'

    {- Impure Program Reduction Rules -}

    data _,_,_⟶ᵢₘ_,_ {Σ} where

      β-ref : ∀ {A μ μ-evd} {v : Σ ∣ ∅ ⊢ A}
        → (V : Value v)
          -------------------------------------------------------------
        → ref v , μ , μ-evd ⟶ᵢₘ addr (∈-∷ʳ Σ A) ⊑-reflexive , store V μ

      β-!ₛ : ∀ {A x μ μ-evd} {r : Σ ∣ ∅ ⊢ Ref A}
        → (R : SimpleValue r)
          ---------------------------------------------------
        → (!ₛ r) x , μ , μ-evd ⟶ᵢₘ μ-static-lookup R x μ , μ

      β-! : ∀ {B μ μ-evd} {r : Σ ∣ ∅ ⊢ Ref B}
        → (R : SimpleValue r)
          --------------------------------------------------------------------------------------
        → ! B r , μ , μ-evd ⟶ᵢₘ store-lookup-v (ref⟹∈ R) μ < make-coercion (ref⟹T R) B > , μ

      β-:=ₛ : ∀ {A x μ μ-evd} {r : Σ ∣ ∅ ⊢ Ref A} {v : Σ ∣ ∅ ⊢ A}
        → (R : SimpleValue r) → (V : Value v)
          -----------------------------------------------------------
        → (r :=ₛ v) x , μ , μ-evd ⟶ᵢₘ unit , μ-static-update R x μ V

      β-:= : ∀ {B μ μ-evd} {r : Σ ∣ ∅ ⊢ Ref B} {v : Σ ∣ ∅ ⊢ B}
        → (R : SimpleValue r) → (V : Value v)
          -----------------------------------------------------
        → := B r v , μ , μ-evd ⟶ᵢₘ unit , ν-update/ref B R μ V

    ⟶ᵢₘ⟹⊑ₗ (β-!ₛ R) = ⊑ₗ-refl
    ⟶ᵢₘ⟹⊑ₗ (β-! R) = ⊑ₗ-refl
    ⟶ᵢₘ⟹⊑ₗ (β-:=ₛ R V) = ⊑ₗ-refl
    ⟶ᵢₘ⟹⊑ₗ (β-:= R V) = ⊑ₗ-refl
    ⟶ᵢₘ⟹⊑ₗ {Σ} {A = Ref A} (β-ref V) = ∷ʳ-⊒ A Σ
