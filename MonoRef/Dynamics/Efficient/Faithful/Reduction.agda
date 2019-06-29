module MonoRef.Dynamics.Efficient.Faithful.Reduction where

open import Data.Empty using (⊥-elim)
open import Data.List using (_∷ʳ_)
open import Data.List.Any using (here ; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary using (¬_)

-- standard library++
open import Data.List.Prefix renaming (_⊑_ to _⊑ₗ_ ; ⊑-refl to ⊑ₗ-refl)
open import Data.List.Properties.Extra using (∈-∷ʳ)

open import MonoRef.Coercions.NormalForm.Faithful.CastedValueReduction public
open import MonoRef.Coercions.NormalForm.Faithful.Compose
open import MonoRef.Coercions.NormalForm.Faithful.Reduction
open import MonoRef.Coercions.NormalForm.Faithful.Syntax
  renaming (NormalFormCoercion to _⟹_ ; InertNormalForm to Inert
           ; ActiveNormalForm to Active ; inert-normalform-decidable to inertP
           ; ¬Inert⇒Active-normform to ¬Inert⇒Active)
open import MonoRef.Coercions.NormalForm.Faithful.Make renaming (make-normal-form-coercion to make-coercion)
open import MonoRef.Dynamics.Store.Efficient
  _⟹_ Inert Active inertP ¬Inert⇒Active make-coercion compose
open import MonoRef.Dynamics.Efficient.Value
  _⟹_ Inert
open import MonoRef.Dynamics.BypassCast public
open import MonoRef.Dynamics.Reduction.MonoReduction
  _⟹_ Inert make-coercion
open import MonoRef.Dynamics.Efficient.Faithful.MonoCastReduction public
open import MonoRef.Dynamics.Reduction.PureReduction
  _⟹_ Inert make-coercion
open import MonoRef.Dynamics.Efficient.Frames
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


open ParamPureReduction SimpleValue Value public
open ParamMonoReduction
  SimpleValue Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑ public
open ParamMonoReduction/ν-update/ref/store ν-update/ref store public

infix 3  _/_,_,_⟶ₑ_,_
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
    → M ⟶ᵤᶜᵛ M'
      -----------------
    → M , ν ⟶ᵤᵣ M' , ν

  mono : ∀ {Σ' A} {ν : Store Σ} {ν' : Store Σ'} {M : Σ ∣ Γ ⊢ A} {M' : Σ' ∣ Γ ⊢ A}
    → M , ν ⟶ₘ M' , ν'
      ------------------
    → M , ν ⟶ᵤᵣ M' , ν'

  ξ-×ₗ : ∀ {Σ' A B} {ν : Store Σ} {ν' : Store Σ'} {e₁ : Σ ∣ Γ ⊢ A} {e₁' : Σ' ∣ Γ ⊢ A} {e₂ : Σ ∣ Γ ⊢ B}
    → (red : e₁ , ν ⟶ᵤᵣ e₁' , ν')
      -----------------------------------------------------------------------------------------
    → _`×_ e₁ e₂ , ν ⟶ᵤᵣ _`×_ e₁' (typeprecise-strenthen-expr (⟶ᵤᵣ⟹⊑ₕ red) e₂) , ν'

  ξ-×ᵣ : ∀ {Σ' A B} {ν : Store Σ} {ν' : Store Σ'} {e₁ : Σ ∣ Γ ⊢ A} {e₂ : Σ ∣ Γ ⊢ B} {e₂' : Σ' ∣ Γ ⊢ B}
    → (red : e₂ , ν ⟶ᵤᵣ e₂' , ν')
      -----------------------------------------------------------------------------------------
    → _`×_ e₁ e₂ , ν ⟶ᵤᵣ _`×_ (typeprecise-strenthen-expr (⟶ᵤᵣ⟹⊑ₕ red) e₁) e₂' , ν'

  ξ-×ₗ-error : ∀ {A B} {ν : Store Σ} {M : Σ ∣ Γ ⊢ B}
      ------------------------------------------
    → _`×_ (error {A = A})  M , ν ⟶ᵤᵣ error , ν

  ξ-×ᵣ-error : ∀ {A B} {ν : Store Σ} {M : Σ ∣ Γ ⊢ A}
      -----------------------------------------
    → _`×_ M (error {A = B}) , ν ⟶ᵤᵣ error , ν

⟶ᵤᵣ⟹⊑ₕ (pure _) = ⊑ₕ-refl
⟶ᵤᵣ⟹⊑ₕ (mono red) = ⟶ₘ⟹⊑ₕ red
⟶ᵤᵣ⟹⊑ₕ (ξ-×ₗ red) = ⟶ᵤᵣ⟹⊑ₕ red
⟶ᵤᵣ⟹⊑ₕ (ξ-×ᵣ red) = ⟶ᵤᵣ⟹⊑ₕ red
⟶ᵤᵣ⟹⊑ₕ ξ-×ₗ-error = ⊑ₕ-refl
⟶ᵤᵣ⟹⊑ₕ ξ-×ᵣ-error = ⊑ₕ-refl

data _/_,_,_⟶ₑ_,_ {Σ} : ∀ {Σ' A}
  → BypassCast
  → Σ  ∣ ∅ ⊢ A → (μ : Store Σ ) → NormalStore μ
  → Σ' ∣ ∅ ⊢ A → (ν : Store Σ')
  → Set

⟶ₑ⟹⊑ : ∀ {Σ Σ' A} {μ : Store Σ} {ν' : Store Σ'} {μ-evd : NormalStore μ} {bc : BypassCast}
             {M : Σ ∣ ∅ ⊢ A} {M' : Σ' ∣ ∅ ⊢ A}
  → bc / M , μ , μ-evd ⟶ₑ M' , ν'
  → StoreTypingProgress Σ Σ'

{- Program Reduction Rules -}

data _/_,_,_⟶ₑ_,_ {Σ} where

  switch : ∀ {Σ' A} {μ : Store Σ} {ν : Store Σ'} {μ-evd : NormalStore μ} {M : Σ ∣ ∅ ⊢ A} {M' : Σ' ∣ ∅ ⊢ A}
    → disallow / M , μ , μ-evd ⟶ₑ M' , ν
      ------------------------------------
    → allow / M , μ , μ-evd ⟶ₑ M' , ν

  β-pure : ∀ {A μ μ-evd} {M' M : Σ ∣ ∅ ⊢ A}
    → M ⟶ M'
      ------------------------------------
    → disallow / M , μ , μ-evd ⟶ₑ M' , μ

  β-mono : ∀ {Σ' A} {μ : Store Σ} {ν : Store Σ'} {μ-evd : NormalStore μ} {M : Σ ∣ ∅ ⊢ A} {M' : Σ' ∣ ∅ ⊢ A}
    → M , μ , μ-evd ⟶ᵢₘ M' , ν
      ------------------------------------
    → disallow / M , μ , μ-evd ⟶ₑ M' , ν

  cast-pure : ∀ {A B} {μ : Store Σ} {M : Σ ∣ ∅ ⊢ A} {M' : Σ ∣ ∅ ⊢ B} {μ-evd : NormalStore μ} {c : A ⟹ B}
    → (M < c >) ⟶ᵤ M'
      ------------------------------------------
    → disallow / M < c > , μ , μ-evd ⟶ₑ M' , μ

  cast-mono : ∀ {Σ' A B} {μ : Store Σ} {ν : Store Σ'} {M : Σ ∣ ∅ ⊢ A} {M' : Σ' ∣ ∅ ⊢ B} {μ-evd : NormalStore μ} {c : A ⟹ B}
    → M < c > , μ ⟶ₘ M' , ν
      ------------------------------------------
    → disallow / M < c > , μ , μ-evd ⟶ₑ M' , ν

  ξ : ∀ {Σ' A B} {μ : Store Σ} {ν : Store Σ'} {μ-evd : NormalStore μ} {M : Σ ∣ ∅ ⊢ A} {M' : Σ' ∣ ∅ ⊢ A}
    → (F : Frame A B)
    → (red : allow / M , μ , μ-evd ⟶ₑ M' , ν)
      -------------------------------------------------------------------------------
    → disallow / plug M F , μ , μ-evd ⟶ₑ plug M' (weaken-frame (⟶ₑ⟹⊑ red) F) , ν

  ξ-cast : ∀ {Σ' A B} {μ : Store Σ} {ν : Store Σ'} {μ-evd : NormalStore μ}
                {M : Σ ∣ ∅ ⊢ A} {M' : Σ' ∣ ∅ ⊢ A} {c : A ⟹ B}
    → (red : disallow / M , μ , μ-evd ⟶ₑ M' , ν)
      ---------------------------------------------
    → allow / M < c > , μ , μ-evd ⟶ₑ M' < c > , ν

  ξ-error : ∀ {A B} {μ : Store Σ} {μ-evd : NormalStore μ}
    → (ξ : Frame A B)
      --------------------------------------------------
    → disallow / plug error ξ , μ , μ-evd ⟶ₑ error , μ

  ξ-cast-error : ∀ {A B} {μ : Store Σ} {μ-evd : NormalStore μ} {c : A ⟹ B}
      ----------------------------------------------
    → allow / error < c > , μ , μ-evd ⟶ₑ error , μ

⟶ₑ⟹⊑ (switch red) = ⟶ₑ⟹⊑ red
⟶ₑ⟹⊑ (β-pure _) = StoreTypingProgress-refl
⟶ₑ⟹⊑ (β-mono red) = from⊑ₗ (⟶ᵢₘ⟹⊑ₗ red)
⟶ₑ⟹⊑ (cast-pure red) = StoreTypingProgress-refl
⟶ₑ⟹⊑ (cast-mono red) = from⊑ₕ (⟶ₘ⟹⊑ₕ red)
⟶ₑ⟹⊑ (ξ _ red) = ⟶ₑ⟹⊑ red
⟶ₑ⟹⊑ (ξ-cast red) = ⟶ₑ⟹⊑ red
⟶ₑ⟹⊑ (ξ-error _) = StoreTypingProgress-refl
⟶ₑ⟹⊑ ξ-cast-error = StoreTypingProgress-refl

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
weaken-ptr (here refl) _ (here refl) (PIE-ty _ ¬f) = ⊥-elim (¬f refl)
weaken-ptr (here refl) _ (here refl) (PIE-ptr ¬f _) = ⊥-elim (¬f refl)
weaken-ptr (there T∈Σ) _ (here refl) _ = there T∈Σ
weaken-ptr (here refl) _ (there A∈Σ) _ = here refl
weaken-ptr (there T∈Σ) B (there A∈Σ) (PIE-ty .(there A∈Σ) ¬f) =
  there (weaken-ptr T∈Σ B A∈Σ (PIE-ty A∈Σ λ { refl → ¬f refl}))
weaken-ptr (there T∈Σ) B (there A∈Σ) (PIE-ptr ¬f _) =
  there (weaken-ptr T∈Σ B A∈Σ (PIE-ptr ¬f A∈Σ))

{- State Reduction Rules -}

data _,_⟶ₛ_,_ {Σ A} :
    (M  : Σ  ∣ ∅ ⊢ A) → (ν  : Store Σ ) → ∀ {Σ'}
  → (M' : Σ' ∣ ∅ ⊢ A) → (ν' : Store Σ')
  → Set where

  prog-reduce : ∀ {Σ' bc} {ν : Store Σ} {ν' : Store Σ'} {M : Σ ∣ ∅ ⊢ A} {M' : Σ' ∣ ∅ ⊢ A}
    → (μ-evd : NormalStore ν)
    → bc / M , ν , μ-evd ⟶ₑ M' , ν'
      ------------------------------
    → M , ν ⟶ₛ M' , ν'

  error :  ∀ {M : Σ ∣ ∅ ⊢ A} {Σ' T} {e : Σ ∣ ∅ ⊢ T} {e' : Σ' ∣ ∅ ⊢ T} {ν : Store Σ} {ν' : Store Σ'}
    → ¬ NormalStore ν
    → (mem : T ∈ Σ)
    → e , ν ⟶ᵤᵣ e' , ν'
    → Erroneous e'
      ----------------------
    → M , ν ⟶ₛ error , ν'

  hcast : ∀ {M : Σ ∣ ∅ ⊢ A} {T} {e e' : Σ ∣ ∅ ⊢ T} {cv : CastedValue e} {ν : Store Σ}
    → ¬ NormalStore ν
    → (T∈Σ : T ∈ Σ)
    → (scv : StrongCastedValue cv)
    → (red : e , ν ⟶ᵤᵣ e' , ν)
    → (cv' : CastedValue e')
      ---------------------------------
    → M , ν ⟶ₛ M , ν-update T∈Σ ν cv'

  hmcast : ∀ {M : Σ ∣ ∅ ⊢ A} {T A B} {e : Σ ∣ ∅ ⊢ T} {cv : CastedValue e} {ν : Store Σ}
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
    →    M                                   , ν
    ⟶ₛ typeprecise-strenthen-expr (⟶ᵤᵣ⟹⊑ₕ red) M , ν-update (weaken-ptr T∈Σ B A∈Σ T∈Σ≢A∈Σ) (ν-cast A∈Σ ν B⊑A) cv'

  hdrop : ∀ {M : Σ ∣ ∅ ⊢ A} {T T'} {e : Σ ∣ ∅ ⊢ T} {cv : CastedValue e} {ν : Store Σ}
    → ¬ NormalStore ν
    → (T∈Σ : T ∈ Σ)
    → (scv : StrongCastedValue cv)
    → {e' : Σ-cast T∈Σ T' ∣ ∅ ⊢ T}
    → (T'⊑T : T' ⊑ store-lookup-rtti T∈Σ ν)
    → T' ≢ store-lookup-rtti T∈Σ ν
    → (red : e , ν ⟶ᵤᵣ e' , ν-cast T∈Σ ν T'⊑T)
      -----------------------------------------------------------------
    →    M                                   , ν
    ⟶ₛ typeprecise-strenthen-expr (⟶ᵤᵣ⟹⊑ₕ red) M , ν-cast T∈Σ ν T'⊑T

⟶ₛ⟹⊑ : ∀ {Σ Σ' A} {M : Σ ∣ ∅ ⊢ A} {ν : Store Σ} {M' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → M , ν ⟶ₛ M' , ν'
  → StoreTypingProgress Σ Σ'
⟶ₛ⟹⊑ (prog-reduce _ red) = ⟶ₑ⟹⊑ red
⟶ₛ⟹⊑ (error _ _ red _) = from⊑ₕ (⟶ᵤᵣ⟹⊑ₕ red)
⟶ₛ⟹⊑ (hcast _ _ _ _ _) = StoreTypingProgress-refl
⟶ₛ⟹⊑ (hmcast _ _ _ _ _ _ red _) = from⊑ₕ (⟶ᵤᵣ⟹⊑ₕ red)
⟶ₛ⟹⊑ (hdrop _ _ _ _ _ red) = from⊑ₕ (⟶ᵤᵣ⟹⊑ₕ red)
