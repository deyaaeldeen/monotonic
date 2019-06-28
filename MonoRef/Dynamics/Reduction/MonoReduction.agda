open import Data.Empty using (⊥ ; ⊥-elim)

open import MonoRef.Static.Types

module MonoRef.Dynamics.Reduction.MonoReduction
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  (make-coercion : ∀ A B → A ⟹ B)
  where

open import Data.List using (_∷ʳ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Nullary using (¬_)

-- standard library++
open import Data.List.Prefix renaming (_⊑_ to _⊑ₗ_ ; ⊑-refl to ⊑ₗ-refl)
open import Data.List.Properties.Extra using (∈-∷ʳ)

open import MonoRef.Dynamics.Store.Normal
  _⟹_ Inert
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


module ParamMonoReduction
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
  open ParamNormal Value CastedValue StrongCastedValue

  module ParamMonoReduction/ν-update/ref/store
    (ν-update/ref : ∀ {A Σ Γ} {r : Σ ∣ Γ ⊢ Ref A}
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
          -----------------------------------
        →   ref v                  , μ , μ-evd
        ⟶ᵢₘ addr (∈-∷ʳ Σ A) ⊑-refl , store V μ

      β-!ₛ : ∀ {A x μ μ-evd} {r : Σ ∣ ∅ ⊢ Ref A}
        → (R : SimpleValue r)
          -----------------------------------
        →   (!ₛ r) x              , μ , μ-evd
        ⟶ᵢₘ μ-static-lookup R x μ , μ

      β-! : ∀ {B μ μ-evd} {r : Σ ∣ ∅ ⊢ Ref B}
        → (R : SimpleValue r)
          -------------------------------------------------------------
        →   ! r                                             , μ , μ-evd
        ⟶ᵢₘ store-lookup-v (ref⟹∈ R) μ < make-coercion (ref⟹T R) B > , μ

      β-:=ₛ : ∀ {A x μ μ-evd} {r : Σ ∣ ∅ ⊢ Ref A} {v : Σ ∣ ∅ ⊢ A}
        → (R : SimpleValue r) → (V : Value v)
          ---------------------------------------
        →   (r :=ₛ v) x , μ , μ-evd
        ⟶ᵢₘ unit        , μ-static-update R x μ V

      β-:= : ∀ {B μ μ-evd} {r : Σ ∣ ∅ ⊢ Ref B} {v : Σ ∣ ∅ ⊢ B}
        → (R : SimpleValue r) → (V : Value v)
          -----------------------------
        →   r := v , μ , μ-evd
        ⟶ᵢₘ unit   , ν-update/ref R μ V

    ⟶ᵢₘ⟹⊑ₗ (β-!ₛ R) = ⊑ₗ-refl
    ⟶ᵢₘ⟹⊑ₗ (β-! R) = ⊑ₗ-refl
    ⟶ᵢₘ⟹⊑ₗ (β-:=ₛ R V) = ⊑ₗ-refl
    ⟶ᵢₘ⟹⊑ₗ (β-:= R V) = ⊑ₗ-refl
    ⟶ᵢₘ⟹⊑ₗ {Σ} {A = Ref A} (β-ref V) = ∷ʳ-⊒ A Σ
