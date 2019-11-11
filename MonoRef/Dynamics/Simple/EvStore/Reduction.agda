open import MonoRef.Static.Types

module MonoRef.Dynamics.Simple.EvStore.Reduction
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  (make-coercion : ∀ A B → A ⟹ B)
  where

open import Data.List using (_∷ʳ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary using (Dec ; ¬_)

-- standard library++
open import Data.List.Prefix renaming (_⊑_ to _⊑ₗ_ ; ⊑-refl to ⊑ₗ-refl)
open import Data.List.Properties.Extra using (∈-∷ʳ)

open import MonoRef.Dynamics.Reduction.EvolvingStore.MonoReduction
  _⟹_ Inert
open import MonoRef.Dynamics.Reduction.EvolvingStore.MonoCastReduction
  _⟹_ Inert
open import MonoRef.Dynamics.Reduction.EvolvingStore.StateReduction
  _⟹_ Inert public
open import MonoRef.Dynamics.Reduction.PureReduction
  _⟹_ Inert make-coercion
open import MonoRef.Dynamics.Simple.Common.Frames
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.Normal
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Ptr
open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.Store
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.Store.TypingProgress
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


module ParamReduction
  (Value             : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (valueP : ∀ {Σ A} → (e : Σ ∣ ∅ ⊢ A) → Dec (Value e))
  (DelayedCast       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (v⇑_ : ∀ {Σ Γ A} {t : Σ ∣ Γ ⊢ A} → Value t → DelayedCast t)
  (ref⟹T : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : Value v) → Type)
  (ref⟹∈ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : Value v) → ref⟹T V ∈ Σ)
  (ref⟹⊑ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : Value v) → ref⟹T V ⊑ A)
  where

  open ParamStoreValue DelayedCast
  open ParamStoreDef StoreValue
  open ParamStore Value Value DelayedCast v⇑_ ref⟹T ref⟹∈ ref⟹⊑
  open ParamPureReduction Value Value renaming (_⟶_ to _⟶ₚ_) public
  open ParamMonoCastReduction
    Value Value DelayedCast v⇑_ ref⟹T ref⟹∈ ref⟹⊑
  open ParamMonoReduction
    Value Value valueP DelayedCast v⇑_ ref⟹T ref⟹∈ ref⟹⊑ make-coercion public
  open ParamNormal Value valueP DelayedCast
  open ParamStateReduction
    Value Value valueP DelayedCast v⇑_ ref⟹T ref⟹∈ ref⟹⊑

  module ParamReduction/ν-cast/ν-update/ref/store/⟶ᵤ
    (ν-cast : ∀ {Σ T t'}
      → (T∈Σ : T ∈ Σ)
      → (ν : Store Σ)
      → t' ⊑ (store-lookup-rtti T∈Σ ν)
      → Store (Σ-cast T∈Σ t'))
    (RefCoercion : ∀ {A B} → (C : Type) → C ⊑ B → Ref A ⟹ Ref B)
    (ν-update/ref : ∀ {Σ Γ}
      → (A : Type)
      → {r : Σ ∣ Γ ⊢ Ref A}
      → (R : Value r)
      → Store Σ
      → ∀ {v : Σ ∣ ∅ ⊢ A}
      → Value v
      → Store Σ)
    (store : ∀ {Σ A} {v : Σ ∣ ∅ ⊢ A} → Value v → Store Σ → Store (Σ ∷ʳ A))
    (_⟶ᵤ_ : ∀ {Γ Σ A} → Σ ∣ Γ ⊢ A → Σ ∣ Γ ⊢ A → Set)
    where

    open ParamMonoCastReduction/ν-cast ν-cast RefCoercion public
    open ParamMonoReduction/ν-update/ref/store ν-update/ref store public

    infix 3  _,_,_⟶ₑ_,_
    infix 3  _,_⟶ᶜ_,_
    infix 3  _,_⟶_,_

    {- Cast Reduction Rules -}


    data _,_⟶ᶜ_,_ {Γ Σ} : ∀ {Σ' A}
      → Σ  ∣ Γ ⊢ A → (ν  : Store Σ )
      → Σ' ∣ Γ ⊢ A → (ν' : Store Σ')
      → Set

    ⟶ᶜ⟹⊑ₕ : ∀ {Γ Σ Σ' A} {M : Σ ∣ Γ ⊢ A} {ν : Store Σ} {M' : Σ' ∣ Γ ⊢ A} {ν' : Store Σ'}
      → M , ν ⟶ᶜ M' , ν'
      → Σ' ⊑ₕ Σ

    data _,_⟶ᶜ_,_ {Γ Σ} where

      pure : ∀ {A} {ν : Store Σ} {M' M : Σ ∣ Γ ⊢ A}
        → M ⟶ᵤ M'
          -----------------
        → M , ν ⟶ᶜ M' , ν

      mono : ∀ {Σ' A} {ν : Store Σ} {ν' : Store Σ'}
               {M : Σ ∣ Γ ⊢ A} {M' : Σ' ∣ Γ ⊢ A}
        → M , ν ⟶ₘ M' , ν'
          -----------------
        → M , ν ⟶ᶜ M' , ν'

      cong : ∀ {Σ' A B} {μ : Store Σ} {ν : Store Σ'} {M : Σ ∣ Γ ⊢ A} {M' : Σ' ∣ Γ ⊢ A}
        → (ξ : Frame A B)
        → (red : M , μ ⟶ᶜ M' , ν)
          ---------------------------------------------------------------------------
        → plug M ξ , μ ⟶ᶜ plug M' (typeprecise-strenthen-frame (⟶ᶜ⟹⊑ₕ red) ξ) , ν

      cong-error : ∀ {A B} {ν : Store Σ}
        → (ξ : Frame A B)
          -------------------------------
        → plug error ξ , ν ⟶ᶜ error , ν

    ⟶ᶜ⟹⊑ₕ (pure _) = ⊑ₕ-refl
    ⟶ᶜ⟹⊑ₕ (mono red) = ⟶ₘ⟹⊑ₕ red
    ⟶ᶜ⟹⊑ₕ (cong _ red) = ⟶ᶜ⟹⊑ₕ red
    ⟶ᶜ⟹⊑ₕ (cong-error _) = ⊑ₕ-refl

    data _,_,_⟶ₑ_,_ {Σ} : ∀ {Σ' A}
      → Σ  ∣ ∅ ⊢ A → (μ : Store Σ ) → NormalStore μ
      → Σ' ∣ ∅ ⊢ A → (ν : Store Σ')
      → Set

    ⟶ₑ⟹⊑ₗ : ∀ {Σ Σ' A} {μ : Store Σ} {ν' : Store Σ'} {μ-evd : NormalStore μ}
                 {M : Σ ∣ ∅ ⊢ A} {M' : Σ' ∣ ∅ ⊢ A}
      → M , μ , μ-evd ⟶ₑ M' , ν'
      → Σ ⊑ₗ Σ'

    {- Program Reduction Rules -}

    data _,_,_⟶ₑ_,_ {Σ} where

      β-pure : ∀ {A μ μ-evd} {M' M : Σ ∣ ∅ ⊢ A}
        → M ⟶ₚ M'
          ------------------------
        → M , μ , μ-evd ⟶ₑ M' , μ

      β-mono : ∀ {Σ' A} {μ : Store Σ} {ν : Store Σ'} {μ-evd : NormalStore μ}
                   {M : Σ ∣ ∅ ⊢ A} {M' : Σ' ∣ ∅ ⊢ A}
        → M , μ , μ-evd ⟶ᵢₘ M' , ν
          -------------------------
        → M , μ , μ-evd ⟶ₑ M' , ν

      cong : ∀ {Σ' A B} {μ : Store Σ} {ν : Store Σ'} {μ-evd : NormalStore μ}
               {M : Σ ∣ ∅ ⊢ A} {M' : Σ' ∣ ∅ ⊢ A}
        → (ξ : Frame A B)
        → (red : M , μ , μ-evd ⟶ₑ M' , ν)
          --------------------------------------------------------------------------
        → plug M ξ , μ , μ-evd ⟶ₑ plug M' (prefix-weaken-frame (⟶ₑ⟹⊑ₗ red) ξ) , ν

      cong-error : ∀ {A B} {μ : Store Σ} {μ-evd : NormalStore μ}
        → (ξ : Frame A B)
          --------------------------------------
        → plug error ξ , μ , μ-evd ⟶ₑ error , μ

    ⟶ₑ⟹⊑ₗ (β-pure _) = ⊑ₗ-refl
    ⟶ₑ⟹⊑ₗ (β-mono red) = ⟶ᵢₘ⟹⊑ₗ red
    ⟶ₑ⟹⊑ₗ (cong ξ red) = ⟶ₑ⟹⊑ₗ red
    ⟶ₑ⟹⊑ₗ (cong-error _) = ⊑ₗ-refl
  
    open ParamStateReduction/ν-cast/⟶ᶜ/⟶ᶜ⟹⊑ₕ ν-cast _,_⟶ᶜ_,_ ⟶ᶜ⟹⊑ₕ Frame plug public

    {- State Reduction Rules -}

    data _,_⟶_,_ {Σ A}
        (M  : Σ  ∣ ∅ ⊢ A)   (ν  : Store Σ ) : ∀ {Σ'}
      → (M' : Σ' ∣ ∅ ⊢ A) → (ν' : Store Σ')
      → Set where

      prog-reduce : ∀ {Σ'} {ν' : Store Σ'} {M' : Σ' ∣ ∅ ⊢ A}
        → (μ-evd : NormalStore ν)
        → M , ν , μ-evd ⟶ₑ M' , ν'
          ------------------------
        → M , ν ⟶ M' , ν'

      cast-reduce :  ∀ {Σ'} {ν' : Store Σ'} {M' : Σ' ∣ ∅ ⊢ A}
        → M , ν ⟶ᶜ M' , ν'
          ----------------
        → M , ν ⟶ M' , ν'

      state-reduce :  ∀ {Σ'} {ν' : Store Σ'} {M' : Σ' ∣ ∅ ⊢ A}
        → (¬μ : ¬ NormalStore ν)
        → M , ν , ¬μ ⟶ₛ M' , ν'
          ---------------------
        → M , ν ⟶ M' , ν'

    ⟶⟹⊑ : ∀ {Σ Σ' A} {M : Σ ∣ ∅ ⊢ A} {ν : Store Σ} {M' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
      → M , ν ⟶ M' , ν'
      → StoreTypingProgress Σ Σ'
    ⟶⟹⊑ (prog-reduce _ red) = from⊑ₗ (⟶ₑ⟹⊑ₗ red)
    ⟶⟹⊑ (cast-reduce red) = from⊑ₕ (⟶ᶜ⟹⊑ₕ red)
    ⟶⟹⊑ (state-reduce _ red) = from⊑ₕ (⟶ₛ⟹⊑ red)
