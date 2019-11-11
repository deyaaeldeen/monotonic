open import MonoRef.Static.Types

module MonoRef.Dynamics.Progress.EvolvingStore
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Product using (∃ ; ∃-syntax ; -,_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality using (_≢_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)

open import MonoRef.Dynamics.Reduction.EvolvingStore.MonoCastReduction
  _⟹_ Inert
open import MonoRef.Dynamics.Reduction.EvolvingStore.StateReduction
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Ptr
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


module ParamEvolvingStoreProgress
  (SimpleValue       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (Value             : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (valueP : ∀ {Σ A} → (e : Σ ∣ ∅ ⊢ A) → Dec (Value e))
  (DelayedCast       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (v⇑_ : ∀ {Σ Γ A} {t : Σ ∣ Γ ⊢ A} → Value t → DelayedCast t)
  (ref⟹T : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → Type)
  (ref⟹∈ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ∈ Σ)
  (ref⟹⊑ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ⊑ A)
  where

  open ParamStoreValue DelayedCast
  open ParamStoreDef StoreValue
  open ParamStore SimpleValue Value DelayedCast v⇑_ ref⟹T ref⟹∈ ref⟹⊑
  open ParamMonoCastReduction
    SimpleValue Value DelayedCast v⇑_ ref⟹T ref⟹∈ ref⟹⊑
  open ParamNormal Value valueP DelayedCast
  open ParamStateReduction
    SimpleValue Value valueP DelayedCast v⇑_ ref⟹T ref⟹∈ ref⟹⊑

  module ParamEvolvingStoreProgress/ν-cast/RefCoercion/⟶ᶜ/⟶ᶜ⟹⊑ₕ/Frame/plug
    (ν-cast : ∀ {Σ T t'}
      → (T∈Σ : T ∈ Σ)
      → (ν : Store Σ)
      → t' ⊑ (store-lookup-rtti T∈Σ ν)
      → Store (Σ-cast T∈Σ t'))
    (RefCoercion : ∀ {A B} → (C : Type) → C ⊑ B → Ref A ⟹ Ref B)
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

    open ParamMonoCastReduction/ν-cast ν-cast RefCoercion
    open ParamStateReduction/ν-cast/⟶ᶜ/⟶ᶜ⟹⊑ₕ ν-cast _,_⟶ᶜ_,_ ⟶ᶜ⟹⊑ₕ Frame plug

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

    progress-store/mono : ∀ {Σ Σ' A T} {e : Σ ∣ ∅ ⊢ A} {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
      → (ν : Store Σ)
      → (T∈Σ : T ∈ Σ)
      → (red : e , ν ⟶ₘ e' , ν')
      → StoreProgress ν T∈Σ (get-ptr/mono red) ν'
    progress-store/mono {T = T} ν B∈Σ (castref1 R rtti∼T₂ ⊓rtti∼T₂≢rtti)
      with ref⟹T R | ref⟹∈ R
    ... | A | A∈Σ
        with ≡Type-decidable T A
    ... | no T≢A = S-acyclic A∈Σ (PIE-ptr T≢A A∈Σ) (⊓⟹⊑ₗ rtti∼T₂)
    ... | yes refl
          with ≡Ptr-decidable A∈Σ B∈Σ
    ...  | yes refl = S-cyclic (⊓⟹⊑ₗ rtti∼T₂) ⊓rtti∼T₂≢rtti
    ...  | no A∈Σ≢B∈Σ = S-acyclic A∈Σ (PIE-ty A∈Σ A∈Σ≢B∈Σ) (⊓⟹⊑ₗ rtti∼T₂)
    progress-store/mono _ _ (castref2 _ _ _) = S-no-change
    progress-store/mono _ _ (castref3 _ _) = S-no-change

    data StateProgress {Σ A} (M : Σ ∣ ∅ ⊢ A) (ν : Store Σ) : Set where

      step : ∀ {Σ'} {ν' : Store Σ'} {N : Σ' ∣ ∅ ⊢ A}
        → (¬μ : ¬ NormalStore ν)
        → M , ν , ¬μ ⟶ₛ N , ν'
          ----------------------
        → StateProgress M ν

    data ReducibleDelayedCastProgress {Γ Σ A} (M : Σ ∣ Γ ⊢ A) (ν : Store Σ) : Set where

      step : ∀ {Σ'} {ν' : Store Σ'} {N : Σ' ∣ Γ ⊢ A}
        → M , ν ⟶ᶜ N , ν'
          --------------------------------
        → ReducibleDelayedCastProgress M ν

    module ParamEvolvingStoreProgress/Proof
      (⟶ᶜprogress-scv : ∀ {Σ A} {e : Σ ∣ ∅ ⊢ A}
        → DelayedCast e
        → ¬ Value e
        → (ν : Store Σ)
        → ReducibleDelayedCastProgress e ν)
      (scv⟶ᶜ⟹cv' : ∀ {Σ Σ' A} {e : Σ ∣ ∅ ⊢ A} {ν : Store Σ}
        {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
        → DelayedCast e
        → ¬ Value e
        → e , ν ⟶ᶜ e' , ν'
        → DelayedCast e' ⊎ Erroneous e')
      (get-ptr : ∀ {Σ Σ' A} {e : Σ ∣ ∅ ⊢ A} {e' : Σ' ∣ ∅ ⊢ A} {ν : Store Σ} {ν' : Store Σ'}
        → (red : e , ν ⟶ᶜ e' , ν') → Maybe (∃[ B ] (B ∈ Σ)))
      (progress-store : ∀ {Σ Σ' A T} {e : Σ ∣ ∅ ⊢ A} {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
        → (ν : Store Σ)
        → (T∈Σ : T ∈ Σ)
        → (red : e , ν ⟶ᶜ e' , ν')
        → StoreProgress ν T∈Σ (get-ptr red) ν') where

      progress-evolving-store : ∀ {Σ A} {M : Σ ∣ ∅ ⊢ A}
        → (ν : Store Σ) → ¬ NormalStore ν → StateProgress M ν
      progress-evolving-store ν ν-¬NS
        with ¬NormalStore⇒∃¬v ν-¬NS
      ... | ⟨ A , ⟨ A∈Σ , ⟨ _ , ⟨ scv , dc ⟩ ⟩ ⟩ ⟩
         with ⟶ᶜprogress-scv dc scv ν
      ...  | step R
          with scv⟶ᶜ⟹cv' dc scv R
      ...   | inj₂ err = step ν-¬NS (error A∈Σ R err)
      ...   | inj₁ cv' with get-ptr R | progress-store ν A∈Σ R
      ...   | _ | S-no-change = step ν-¬NS (hcast A∈Σ R cv')
      ...   | _ | S-cyclic T'⊑T T'≢T = step ν-¬NS (hdrop A∈Σ T'⊑T T'≢T R)
      ...   | _ | S-acyclic B∈Σ A≢B C⊑B = step ν-¬NS (hmcast A∈Σ B∈Σ A≢B C⊑B R cv')
