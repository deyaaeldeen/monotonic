open import Data.Empty using (⊥ ; ⊥-elim)

open import MonoRef.Static.Types

module MonoRef.Dynamics.Simple.Reduction
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  (make-coercion : ∀ A B → A ⟹ B)
  (Inert⇒¬Ref : ∀ {A B} {c : A ⟹ Ref B} → Inert c → ⊥)
  where

open import Data.List using (_∷ʳ_)
open import Data.List.Any using (here ; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary using (¬_)

-- standard library++
open import Data.List.Prefix renaming (_⊑_ to _⊑ₗ_ ; ⊑-refl to ⊑ₗ-refl)
open import Data.List.Properties.Extra using (∈-∷ʳ)

open import MonoRef.Dynamics.Reduction.MonoReduction
  _⟹_ Inert make-coercion Inert⇒¬Ref
open import MonoRef.Dynamics.Reduction.MonoCastReduction
  _⟹_ Inert Inert⇒¬Ref
open import MonoRef.Dynamics.Reduction.PureReduction
  _⟹_ Inert make-coercion
open import MonoRef.Dynamics.Simple.Frames
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Normal
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Ptr
open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Store
  _⟹_ Inert Inert⇒¬Ref
open import MonoRef.Dynamics.Store.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.Store.TypingProgress
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


module ParamReduction
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
  open ParamPureReduction Value public
  open ParamMonoCastReduction
    Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑
  open ParamMonoReduction
    Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑ public
  open ParamNormal Value CastedValue StrongCastedValue

  module ParamReduction/ν-cast/ν-update/ref/store/⟶ᵤ
    (ν-cast : ∀ {Σ T t'}
      → (T∈Σ : T ∈ Σ)
      → (ν : Store Σ)
      → t' ⊑ (store-lookup-rtti T∈Σ ν)
      → Store (Σ-cast T∈Σ t'))
    (ν-update/ref : ∀ {A Σ Γ} {r : Σ ∣ Γ ⊢ Ref A}
      → (R : Value r)
      → Store Σ
      → ∀ {v : Σ ∣ ∅ ⊢ A}
      → Value v
      → Store Σ)
    (store : ∀ {Σ A} {v : Σ ∣ ∅ ⊢ A} → Value v → Store Σ → Store (Σ ∷ʳ A))
    (_⟶ᵤ_ : ∀ {Γ Σ A} → Σ ∣ Γ ⊢ A → Σ ∣ Γ ⊢ A → Set)
    where

    open ParamMonoCastReduction/ν-cast ν-cast public
    open ParamMonoReduction/ν-update/ref/store ν-update/ref store public

    infix 3  _,_,_⟶ₑ_,_
    infix 3  _,_⟶ᵤᵣ_,_
    infix 3  _,_⟶ₛ_,_

    {- Cast Reduction Rules -}


    data _,_⟶ᵤᵣ_,_ {Γ Σ} : ∀ {Σ' A}
      → Σ  ∣ Γ ⊢ A → (ν  : Store Σ )
      → Σ' ∣ Γ ⊢ A → (ν' : Store Σ')
      → Set

    ⟶ᵤᵣ⟹⊑ₕ : ∀ {Γ Σ Σ' A} {M : Σ ∣ Γ ⊢ A} {ν : Store Σ} {M' : Σ' ∣ Γ ⊢ A} {ν' : Store Σ'}
      → M , ν ⟶ᵤᵣ M' , ν'
      → Σ' ⊑ₕ Σ

    data _,_⟶ᵤᵣ_,_ {Γ Σ} where

      pure : ∀ {A} {ν : Store Σ} {M' M : Σ ∣ Γ ⊢ A}
        → M ⟶ᵤ M'
          -----------------
        → M , ν ⟶ᵤᵣ M' , ν

      mono : ∀ {Σ' A} {ν : Store Σ} {ν' : Store Σ'}
               {M : Σ ∣ Γ ⊢ A} {M' : Σ' ∣ Γ ⊢ A}
        → M , ν ⟶ₘ M' , ν'
          -----------------
        → M , ν ⟶ᵤᵣ M' , ν'

      cong : ∀ {Σ' A B} {μ : Store Σ} {ν : Store Σ'} {M : Σ ∣ Γ ⊢ A} {M' : Σ' ∣ Γ ⊢ A}
        → (ξ : Frame A B)
        → (red : M , μ ⟶ᵤᵣ M' , ν)
          ---------------------------------------------------------------------------
        → plug M ξ , μ ⟶ᵤᵣ plug M' (typeprecise-strenthen-frame (⟶ᵤᵣ⟹⊑ₕ red) ξ) , ν

      cong-error : ∀ {A B} {ν : Store Σ}
        → (ξ : Frame A B)
          -------------------------------
        → plug error ξ , ν ⟶ᵤᵣ error , ν

    ⟶ᵤᵣ⟹⊑ₕ (pure _) = ⊑ₕ-refl
    ⟶ᵤᵣ⟹⊑ₕ (mono red) = ⟶ₘ⟹⊑ₕ red
    ⟶ᵤᵣ⟹⊑ₕ (cong _ red) = ⟶ᵤᵣ⟹⊑ₕ red
    ⟶ᵤᵣ⟹⊑ₕ (cong-error _) = ⊑ₕ-refl

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
        → M ⟶ M'
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

    data Erroneous : ∀ {Γ Σ A} → (M : Σ ∣ Γ ⊢ A) → Set where

      Err-intro : ∀ {Γ Σ A}
        → Erroneous (error {Σ = Σ} {Γ = Γ} {A = A})

      Err-plugged : ∀ {Γ Σ A B} {M : Σ ∣ Γ ⊢ A}
        → Erroneous M
        → (ξ : Frame A B)
        → Erroneous (plug M ξ)

    weaken-ptr : ∀ {T A Σ}
      → (T∈Σ : T ∈ Σ) → (B : Type) → (A∈Σ : A ∈ Σ)
      → PtrInEquality T∈Σ A∈Σ → T ∈ Σ-cast A∈Σ B
    weaken-ptr (here refl) B (here refl) (PIE-ty _ ¬f) = ⊥-elim (¬f refl)
    weaken-ptr (here refl) B (here refl) (PIE-ptr ¬f _) = ⊥-elim (¬f refl)
    weaken-ptr (there T∈Σ) B (here refl) _ = there T∈Σ
    weaken-ptr (here refl) B (there A∈Σ) _ = here refl
    weaken-ptr (there T∈Σ) B (there A∈Σ) (PIE-ty .(there A∈Σ) ¬f) =
      there (weaken-ptr T∈Σ B A∈Σ (PIE-ty A∈Σ λ { refl → ¬f refl}))
    weaken-ptr (there T∈Σ) B (there A∈Σ) (PIE-ptr ¬f _) =
      there (weaken-ptr T∈Σ B A∈Σ (PIE-ptr ¬f A∈Σ))

    {- State Reduction Rules -}

    data _,_⟶ₛ_,_ {Σ A}
        (M  : Σ  ∣ ∅ ⊢ A)   (ν  : Store Σ ) : ∀ {Σ'}
      → (M' : Σ' ∣ ∅ ⊢ A) → (ν' : Store Σ')
      → Set where

      prog-reduce : ∀ {Σ'} {ν' : Store Σ'} {M' : Σ' ∣ ∅ ⊢ A}
        → (μ-evd : NormalStore ν)
        → M , ν , μ-evd ⟶ₑ M' , ν'
          ------------------------
        → M , ν ⟶ₛ M' , ν'

    -- Is there a bug in the paper related to this rule where it assumes the ⟶ᵤᵣ
    -- takes a μ as input?
      cast-reduce :  ∀ {Σ'} {ν' : Store Σ'} {M' : Σ' ∣ ∅ ⊢ A}
        → M , ν ⟶ᵤᵣ M' , ν'
          -----------------
        → M , ν ⟶ₛ M' , ν'

      error :  ∀ {Σ' T} {e : Σ ∣ ∅ ⊢ T} {e' : Σ' ∣ ∅ ⊢ T} {ν' : Store Σ'}
        → ¬ NormalStore ν
        → (mem : T ∈ Σ)
        → e , ν ⟶ᵤᵣ e' , ν'
        → Erroneous e'
          --------------------
        → M , ν ⟶ₛ error , ν'

      hcast : ∀ {T} {e e' : Σ ∣ ∅ ⊢ T} {cv : CastedValue e} {ν' : Store Σ}
        → ¬ NormalStore ν
        → (T∈Σ : T ∈ Σ)
        → (scv : StrongCastedValue cv)
        → (red : e , ν ⟶ᵤᵣ e' , ν')
        → (cv' : CastedValue e')
          ---------------------------------
        → M , ν ⟶ₛ M , ν-update T∈Σ ν' cv'

      hmcast : ∀ {T A B} {e : Σ ∣ ∅ ⊢ T} {cv : CastedValue e}
        → ¬ NormalStore ν
        → (T∈Σ : T ∈ Σ)
        → (scv : StrongCastedValue cv)
        → (A∈Σ : A ∈ Σ)
        → (T∈Σ≢A∈Σ : PtrInEquality T∈Σ A∈Σ)
        → (B⊑A : B ⊑ store-lookup-rtti A∈Σ ν)
        → {e' : Σ-cast A∈Σ B ∣ ∅ ⊢ T}
        → (red : e , ν ⟶ᵤᵣ e' , ν-cast A∈Σ ν B⊑A)
        → (cv' : CastedValue e')
          --------------------------------------------------------------------------------------------------------------
        →    M                                           , ν
        ⟶ₛ typeprecise-strenthen-expr (⟶ᵤᵣ⟹⊑ₕ red) M , ν-update (weaken-ptr T∈Σ B A∈Σ T∈Σ≢A∈Σ) (ν-cast A∈Σ ν B⊑A) cv'

      hdrop : ∀ {T T'} {e : Σ ∣ ∅ ⊢ T} {cv : CastedValue e}
        → ¬ NormalStore ν
        → (T∈Σ : T ∈ Σ)
        → (scv : StrongCastedValue cv)
        → {e' : Σ-cast T∈Σ T' ∣ ∅ ⊢ T}
        → (T'⊑T : T' ⊑ store-lookup-rtti T∈Σ ν)
        → T' ≢ store-lookup-rtti T∈Σ ν
        → (red : e , ν ⟶ᵤᵣ e' , ν-cast T∈Σ ν T'⊑T)
          -----------------------------------------------------------------
        →    M                                           , ν
        ⟶ₛ typeprecise-strenthen-expr (⟶ᵤᵣ⟹⊑ₕ red) M , ν-cast T∈Σ ν T'⊑T

    ⟶ₛ⟹⊑ : ∀ {Σ Σ' A} {M : Σ ∣ ∅ ⊢ A} {ν : Store Σ} {M' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
      → M , ν ⟶ₛ M' , ν'
      → StoreTypingProgress Σ Σ'
    ⟶ₛ⟹⊑ (prog-reduce _ red) = from⊑ₗ (⟶ₑ⟹⊑ₗ red)
    ⟶ₛ⟹⊑ (cast-reduce red) = from⊑ₕ (⟶ᵤᵣ⟹⊑ₕ red)
    ⟶ₛ⟹⊑ (error _ _ red _) = from⊑ₕ (⟶ᵤᵣ⟹⊑ₕ red)
    ⟶ₛ⟹⊑ (hcast _ _ _ _ _) = StoreTypingProgress-refl
    ⟶ₛ⟹⊑ (hmcast _ _ _ _ _ _ red _) = from⊑ₕ (⟶ᵤᵣ⟹⊑ₕ red)
    ⟶ₛ⟹⊑ (hdrop _ _ _ _ _ red) = from⊑ₕ (⟶ᵤᵣ⟹⊑ₕ red)
