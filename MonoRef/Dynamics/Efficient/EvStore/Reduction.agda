module MonoRef.Dynamics.Efficient.EvStore.Reduction where

open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (¬_)

open import MonoRef.Dynamics.BypassCast public
open import MonoRef.Dynamics.Efficient.Coercions
open import MonoRef.Dynamics.Efficient.EvStore.CastReduction
  renaming (_,_⟶_,_ to _,_⟶ᶜ_,_) public
open import MonoRef.Dynamics.Efficient.EvStore.MonoCastReduction public
open import MonoRef.Dynamics.Efficient.EvStore.MonoReduction public
open import MonoRef.Dynamics.Efficient.EvStore.Store
open import MonoRef.Dynamics.Efficient.EvStore.StateReduction public
open import MonoRef.Dynamics.Efficient.Frames
open import MonoRef.Dynamics.Efficient.PureReduction
  renaming (_⟶_ to _⟶ₚ_) public
open import MonoRef.Dynamics.Efficient.TargetWithoutBlame
open import MonoRef.Dynamics.Efficient.Value public
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


infix 3  _/_,_,_⟶ₑ_,_
infix 3  _,_⟶_,_

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
    → M ⟶ₚ M'
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

{- State Reduction Rules -}

data _,_⟶_,_ {Σ A} :
    (M  : Σ  ∣ ∅ ⊢ A) → (ν  : Store Σ ) → ∀ {Σ'}
  → (M' : Σ' ∣ ∅ ⊢ A) → (ν' : Store Σ')
  → Set where

  prog-reduce : ∀ {Σ' bc} {ν : Store Σ} {ν' : Store Σ'} {M : Σ ∣ ∅ ⊢ A} {M' : Σ' ∣ ∅ ⊢ A}
    → (μ-evd : NormalStore ν)
    → bc / M , ν , μ-evd ⟶ₑ M' , ν'
      ------------------------------
    → M , ν ⟶ M' , ν'

  state-reduce : ∀ {Σ'} {ν : Store Σ} {ν' : Store Σ'} {M : Σ ∣ ∅ ⊢ A} {M' : Σ' ∣ ∅ ⊢ A}
    → (¬μ : ¬ NormalStore ν)
    → M , ν , ¬μ ⟶ₛ M' , ν'
      ----------------------
    → M , ν ⟶ M' , ν'

⟶⟹⊑ : ∀ {Σ Σ' A} {M : Σ ∣ ∅ ⊢ A} {ν : Store Σ} {M' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → M , ν ⟶ M' , ν' → StoreTypingProgress Σ Σ'
⟶⟹⊑ (prog-reduce _ red) = ⟶ₑ⟹⊑ red
⟶⟹⊑ (state-reduce _ red) = from⊑ₕ (⟶ₛ⟹⊑ red)
