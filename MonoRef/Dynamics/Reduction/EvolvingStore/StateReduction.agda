open import MonoRef.Static.Types

module MonoRef.Dynamics.Reduction.EvolvingStore.StateReduction
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; ¬_)

open import MonoRef.Dynamics.Store.Evolving.Normal
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Ptr
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
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


module ParamStateReduction
  (SimpleValue : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (Value       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (valueP : ∀ {Σ A} → (e : Σ ∣ ∅ ⊢ A) → Dec (Value e))
  (DelayedCast : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (v⇑_ : ∀ {Σ Γ A} {t : Σ ∣ Γ ⊢ A} → Value t → DelayedCast t)
  (ref⟹T : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → Type)
  (ref⟹∈ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ∈ Σ)
  (ref⟹⊑ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ⊑ A)
  where

  open ParamStoreValue DelayedCast
  open ParamStoreDef StoreValue
  open ParamStore SimpleValue Value DelayedCast v⇑_ ref⟹T ref⟹∈ ref⟹⊑
  open ParamNormal Value valueP DelayedCast

  module ParamStateReduction/ν-cast/⟶ᶜ/⟶ᶜ⟹⊑ₕ
    (ν-cast : ∀ {Σ T t'}
      → (T∈Σ : T ∈ Σ)
      → (ν : Store Σ)
      → t' ⊑ (store-lookup-rtti T∈Σ ν)
      → Store (Σ-cast T∈Σ t'))
    (_,_⟶ᶜ_,_ : ∀ {Γ Σ Σ' A}
      → Σ  ∣ Γ ⊢ A → (ν  : Store Σ )
      → Σ' ∣ Γ ⊢ A → (ν' : Store Σ')
      → Set)
    (⟶ᶜ⟹⊑ₕ : ∀ {Γ Σ Σ' A} {M : Σ ∣ Γ ⊢ A} {ν : Store Σ} {M' : Σ' ∣ Γ ⊢ A} {ν' : Store Σ'}
      → M , ν ⟶ᶜ M' , ν'
      → Σ' ⊑ₕ Σ)
    (Frame : ∀ {Γ Σ} → (A B : Type) → Set)
    (plug : ∀{Σ Γ A B} → Σ ∣ Γ ⊢ A → Frame {Γ} {Σ} A B → Σ ∣ Γ ⊢ B)
    where

    data Erroneous : ∀ {Γ Σ A} → (M : Σ ∣ Γ ⊢ A) → Set where
    
      Err-intro : ∀ {Γ Σ A}
        → Erroneous (error {Σ = Σ} {Γ = Γ} {A = A})
    
      Err-plugged : ∀ {Γ Σ A B} {M : Σ ∣ Γ ⊢ A}
        → Erroneous M
        → (ξ : Frame A B)
        → Erroneous (plug M ξ)
    
    infix 3  _,_,_⟶ₛ_,_

    {- State Reduction Rules -}

    data _,_,_⟶ₛ_,_ {Σ A}
        (M  : Σ  ∣ ∅ ⊢ A)   (ν  : Store Σ ) (¬μ : ¬ NormalStore ν) : ∀ {Σ'}
      → (M' : Σ' ∣ ∅ ⊢ A) → (ν' : Store Σ')
      → Set where

      error :  ∀ {Σ' T} {e : Σ ∣ ∅ ⊢ T} {e' : Σ' ∣ ∅ ⊢ T} {ν' : Store Σ'}
        → (mem : T ∈ Σ)
        → e , ν ⟶ᶜ e' , ν'
        → Erroneous e'
          -------------------------
        → M , ν , ¬μ ⟶ₛ error , ν'

      hcast : ∀ {T} {e e' : Σ ∣ ∅ ⊢ T}
        → (T∈Σ : T ∈ Σ)
        → (red : e , ν ⟶ᶜ e' , ν)
        → (cv' : DelayedCast e')
          ------------------------------------
        → M , ν , ¬μ ⟶ₛ M , ν-update T∈Σ ν cv'

      hmcast : ∀ {T A B} {e : Σ ∣ ∅ ⊢ T}
        → (T∈Σ : T ∈ Σ)
        → (A∈Σ : A ∈ Σ)
        → (T∈Σ≢A∈Σ : PtrInEquality T∈Σ A∈Σ)
        → (B⊑A : B ⊑ store-lookup-rtti A∈Σ ν)
        → {e' : Σ-cast A∈Σ B ∣ ∅ ⊢ T}
        → (red : e , ν ⟶ᶜ e' , ν-cast A∈Σ ν B⊑A)
        → (cv' : DelayedCast e')
          --------------------------------------------------------------------------------------------------------------
        →    M                                           , ν , ¬μ
        ⟶ₛ typeprecise-strenthen-expr (⟶ᶜ⟹⊑ₕ red) M , ν-update (weaken-ptr T∈Σ B A∈Σ T∈Σ≢A∈Σ) (ν-cast A∈Σ ν B⊑A) cv'

      hdrop : ∀ {T T'} {e : Σ ∣ ∅ ⊢ T}
        → (T∈Σ : T ∈ Σ)
        → {e' : Σ-cast T∈Σ T' ∣ ∅ ⊢ T}
        → (T'⊑T : T' ⊑ store-lookup-rtti T∈Σ ν)
        → T' ≢ store-lookup-rtti T∈Σ ν
        → (red : e , ν ⟶ᶜ e' , ν-cast T∈Σ ν T'⊑T)
          -----------------------------------------------------------------
        →    M                                           , ν , ¬μ
        ⟶ₛ typeprecise-strenthen-expr (⟶ᶜ⟹⊑ₕ red) M , ν-cast T∈Σ ν T'⊑T

    ⟶ₛ⟹⊑ : ∀ {Σ Σ' A} {M : Σ ∣ ∅ ⊢ A} {ν : Store Σ} {¬μ : ¬ NormalStore ν} {M' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
      → M , ν , ¬μ ⟶ₛ M' , ν'
      → Σ' ⊑ₕ Σ
    ⟶ₛ⟹⊑ (error _ red _) = ⟶ᶜ⟹⊑ₕ red
    ⟶ₛ⟹⊑ (hcast _ _ _) = ⊑ₕ-refl
    ⟶ₛ⟹⊑ (hmcast _ _ _ _ red _) = ⟶ᶜ⟹⊑ₕ red
    ⟶ₛ⟹⊑ (hdrop _ _ _ red) = ⟶ᶜ⟹⊑ₕ red
