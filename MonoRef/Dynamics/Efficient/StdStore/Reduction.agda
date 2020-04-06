module MonoRef.Dynamics.Efficient.StdStore.Reduction where

open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.List.All using () renaming (map to all-map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (proj₁ ; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)

open import MonoRef.Dynamics.BypassCast public
open import MonoRef.Dynamics.Efficient.StdStore.ApplyCast
open import MonoRef.Dynamics.Efficient.StdStore.MonoReduction public
open import MonoRef.Dynamics.Efficient.StdStore.StateReduction
  renaming (_,_,_⟶_,_,_ to _,_,_⟶ₛ_,_,_ ; ⟶⟹rtti⊑Σ to ⟶ₛ⟹rtti⊑Σ) public
open import MonoRef.Dynamics.Efficient.StdStore.SuspendedCast
open import MonoRef.Dynamics.Efficient.StdStore.Store
open import MonoRef.Dynamics.Efficient.Coercions
open import MonoRef.Dynamics.Efficient.Frames
open import MonoRef.Dynamics.Efficient.PureReduction
  renaming (_⟶_ to _⟶ₚ_) public
open import MonoRef.Dynamics.Efficient.TargetWithoutBlame
open import MonoRef.Dynamics.Efficient.Value public
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


infix 3  _/_,_⟶ₑ_,_,_
infix 3  _,_,_⟶_,_,_

data _/_,_⟶ₑ_,_,_ {Σ} : ∀ {Σ' A}
  → BypassCast
  → Σ   ∣ ∅ ⊢ A → (μ : Store Σ Σ)
  → (Q : List (SuspendedCast Σ'))
  → proj₁ (merge Q) ∣ ∅ ⊢ A
  → Store (proj₁ (merge Q)) Σ'
  → Set

⟶ₑ⟹rtti⊑Σ : ∀ {Σ Σ' A} {μ : Store Σ Σ} {Q : List (SuspendedCast Σ')}
  {μ' : Store (proj₁ (merge Q)) Σ'} {bc : BypassCast}
  {M : Σ ∣ ∅ ⊢ A} {M' : proj₁ (merge Q) ∣ ∅ ⊢ A}
  → bc / M , μ ⟶ₑ Q , M' , μ'
  → StoreTypingProgress Σ Σ'

⟶ₑ⟹Σ'⊑Σ : ∀ {Σ Σ' A} {μ : Store Σ Σ} {Q : List (SuspendedCast Σ')}
  {μ' : Store (proj₁ (merge Q)) Σ'} {bc : BypassCast}
  {M : Σ ∣ ∅ ⊢ A} {M' : proj₁ (merge Q) ∣ ∅ ⊢ A}
  → bc / M , μ ⟶ₑ Q , M' , μ'
  → StoreTypingProgress Σ (proj₁ (merge Q))

{- Program Reduction Rules -}

data _/_,_⟶ₑ_,_,_ {Σ} where

  switch : ∀ {Σ' A} {Q : List (SuspendedCast Σ')}
             {μ : Store Σ Σ} {μ' : Store (proj₁ (merge Q)) Σ'}
             {M : Σ ∣ ∅ ⊢ A} {M' : proj₁ (merge Q) ∣ ∅ ⊢ A}
    → disallow / M , μ ⟶ₑ Q , M' , μ'
      -------------------------------
    → allow / M , μ ⟶ₑ Q , M' , μ'

  β-pure : ∀ {A μ} {M' M : Σ ∣ ∅ ⊢ A}
    → M ⟶ₚ M'
      --------------------------------
    → disallow / M , μ ⟶ₑ [] , M' , μ

  β-mono : ∀ {Σ' A} {Q : List (SuspendedCast Σ')}
             {μ : Store Σ Σ} {μ' : Store (proj₁ (merge Q)) Σ'}
             {M : Σ ∣ ∅ ⊢ A} {M' : proj₁ (merge Q) ∣ ∅ ⊢ A}
    → M , μ ⟶ᵢₘ Q , M' , μ'
      --------------------------------
    → disallow / M , μ ⟶ₑ Q , M' , μ'

  cast/succeed : ∀ {A B} {μ : Store Σ Σ} {M : Σ ∣ ∅ ⊢ A} {c : A ⟹ B}
    → (v : Value M)
    → (sc : SuccessfulCast (apply-cast ⊑ₕ-refl [] v c))
      -----------------------------------------------------------------------------------------------------
    → disallow / M < c > , μ
    ⟶ₑ proj₁ (get-val-from-successful-cast sc)
      , (proj₁ (proj₂ (get-val-from-successful-cast sc)))
      , all-map (typeprecise-strenthen-storeval (proj₂ (merge (proj₁ (get-val-from-successful-cast sc))))) μ

  cast/fail : ∀ {A B} {μ : Store Σ Σ} {M : Σ ∣ ∅ ⊢ A} {c : A ⟹ B}
    → (v : Value M)
    → (sc : FailedCast (apply-cast ⊑ₕ-refl [] v c))
      ------------------------------------------
    → disallow / M < c > , μ ⟶ₑ [] , error , μ

  compose-casts : ∀ {A B C} {μ : Store Σ Σ} {M : Σ ∣ ∅ ⊢ A} {c : A ⟹ B} {d : B ⟹ C}
      -----------------------------------------------------------
    → disallow / M < c > < d > , μ ⟶ₑ [] , M < compose c d > , μ

  ξ : ∀ {Σ' A B} {Q : List (SuspendedCast Σ')}
        {μ : Store Σ Σ} {μ' : Store (proj₁ (merge Q)) Σ'}
        {M : Σ ∣ ∅ ⊢ A} {M' : proj₁ (merge Q) ∣ ∅ ⊢ A} 
    → (F : Frame A B)
    → (red : allow / M , μ ⟶ₑ Q , M' , μ')
      ------------------------------------------------------------------------------
    → disallow / plug M F , μ ⟶ₑ Q , plug M' (weaken-frame (⟶ₑ⟹Σ'⊑Σ red) F) , μ'

  ξ-cast : ∀ {Σ' A B} {Q : List (SuspendedCast Σ')}
             {μ : Store Σ Σ} {μ' : Store (proj₁ (merge Q)) Σ'}
             {M : Σ ∣ ∅ ⊢ A} {M' : proj₁ (merge Q) ∣ ∅ ⊢ A} {c : A ⟹ B}
    → (red : disallow / M , μ ⟶ₑ Q , M' , μ')
      ------------------------------------------
    → allow / M < c > , μ ⟶ₑ Q , M' < c >  , μ'

  ξ-error : ∀ {A B} {μ : Store Σ Σ}
    → (ξ : Frame A B)
      ----------------------------------------------
    → disallow / plug error ξ , μ ⟶ₑ [] , error , μ

  ξ-cast-error : ∀ {A B} {μ : Store Σ Σ} {c : A ⟹ B}
      ------------------------------------------
    → allow / error < c > , μ ⟶ₑ [] , error , μ

⟶ₑ⟹rtti⊑Σ (switch red) = ⟶ₑ⟹rtti⊑Σ red
⟶ₑ⟹rtti⊑Σ (β-pure _) = StoreTypingProgress-refl
⟶ₑ⟹rtti⊑Σ (β-mono red) = ⟶ᵢₘ⟹rtti⊑Σ red
⟶ₑ⟹rtti⊑Σ (cast/succeed _ _) = StoreTypingProgress-refl
⟶ₑ⟹rtti⊑Σ (cast/fail _ _) = StoreTypingProgress-refl
⟶ₑ⟹rtti⊑Σ compose-casts = StoreTypingProgress-refl
⟶ₑ⟹rtti⊑Σ (ξ _ red) = ⟶ₑ⟹rtti⊑Σ red
⟶ₑ⟹rtti⊑Σ (ξ-cast red) = ⟶ₑ⟹rtti⊑Σ red
⟶ₑ⟹rtti⊑Σ (ξ-error _) = StoreTypingProgress-refl
⟶ₑ⟹rtti⊑Σ ξ-cast-error = StoreTypingProgress-refl

⟶ₑ⟹Σ'⊑Σ (switch red) = ⟶ₑ⟹Σ'⊑Σ red
⟶ₑ⟹Σ'⊑Σ (β-pure _) = StoreTypingProgress-refl
⟶ₑ⟹Σ'⊑Σ (β-mono red) = ⟶ᵢₘ⟹Σ'⊑Σ red
⟶ₑ⟹Σ'⊑Σ (cast/succeed _ c) = from⊑ₕ (proj₂ (merge (proj₁ (get-val-from-successful-cast c))))
⟶ₑ⟹Σ'⊑Σ (cast/fail _ _) = StoreTypingProgress-refl
⟶ₑ⟹Σ'⊑Σ compose-casts = StoreTypingProgress-refl
⟶ₑ⟹Σ'⊑Σ (ξ _ red) = ⟶ₑ⟹Σ'⊑Σ red
⟶ₑ⟹Σ'⊑Σ (ξ-cast red) = ⟶ₑ⟹Σ'⊑Σ red
⟶ₑ⟹Σ'⊑Σ (ξ-error _) = StoreTypingProgress-refl
⟶ₑ⟹Σ'⊑Σ ξ-cast-error = StoreTypingProgress-refl

{- State Reduction Rules -}

data _,_,_⟶_,_,_ {Σ T} : ∀ {Σ₁ Σ₂ Σ₃} {Σ₁⊑ₕΣ : Σ₁ ⊑ₕ Σ} {Σ₃⊑ₕΣ₂ : Σ₃ ⊑ₕ Σ₂} →
    (Q  : List (SuspendedCast Σ)) →
    (M  : proj₁ (merge' Σ₁⊑ₕΣ Q) ∣ ∅ ⊢ T) →
    (μ  : Store (proj₁ (merge' Σ₁⊑ₕΣ Q)) Σ₁) → 
    (Q' : List (SuspendedCast Σ₂)) →
    (M' : proj₁ (merge' Σ₃⊑ₕΣ₂ Q') ∣ ∅ ⊢ T) →
    (μ' : Store (proj₁ (merge' Σ₃⊑ₕΣ₂ Q')) Σ₃)
  → Set where

  state-reduce : ∀ {Σ₁ Σ₂ A B} {Q Q' : List (SuspendedCast Σ)} {A∈Σ : A ∈ Σ}
                   {Σ₁⊑ₕΣ : Σ₁ ⊑ₕ Σ} {μ : Store (proj₁ (merge' Σ₁⊑ₕΣ (cast A∈Σ B ∷ Q))) Σ₁}
                   {Σ₂⊑ₕΣ₁ : Σ₂ ⊑ₕ Σ₁}
                   {μ' : Store (proj₁ (merge' (⊑ₕ-trans Σ₂⊑ₕΣ₁ Σ₁⊑ₕΣ) Q')) Σ₂}
                   {M : proj₁ (merge' Σ₁⊑ₕΣ (cast A∈Σ B ∷ Q)) ∣ ∅ ⊢ T}
                   {M' : proj₁ (merge' (⊑ₕ-trans Σ₂⊑ₕΣ₁ Σ₁⊑ₕΣ) Q') ∣ ∅ ⊢ T}
    → _,_,_⟶ₛ_,_,_ {A∈Σ = A∈Σ} {Σ₁⊑ₕΣ = Σ₁⊑ₕΣ} Q M μ {Σ₂⊑ₕΣ₁ = Σ₂⊑ₕΣ₁} Q' M' μ'
      --------------------------------------------------------------------------
    → cast A∈Σ B ∷ Q , M , μ ⟶ Q' , M' , μ'

  prog-reduce : ∀ {Σ' bc} {Q : List (SuspendedCast Σ')}
                  {μ : Store Σ Σ} {μ' : Store (proj₁ (merge Q)) Σ'}
                  {M : Σ ∣ ∅ ⊢ T} {M' : proj₁ (merge Q) ∣ ∅ ⊢ T}
    → bc / M , μ ⟶ₑ Q , M' , μ'
      ----------------------------------------------
    → _,_,_⟶_,_,_ {Σ₁⊑ₕΣ = ⊑ₕ-refl} [] M μ Q M' μ'

⟶⟹rtti⊑Σ : ∀ {Σ Σ₁ Σ₂ Σ₃ A} {Q : List (SuspendedCast Σ)} {Q' : List (SuspendedCast Σ₂)}
                {Σ₁⊑ₕΣ : Σ₁ ⊑ₕ Σ} {Σ₃⊑ₕΣ₂ : Σ₃ ⊑ₕ Σ₂} {M : proj₁ (merge' Σ₁⊑ₕΣ Q) ∣ ∅ ⊢ A}
                 {μ : Store (proj₁ (merge' Σ₁⊑ₕΣ Q)) Σ₁}
                 {M' : proj₁ (merge' Σ₃⊑ₕΣ₂ Q') ∣ ∅ ⊢ A}
                 {μ' : Store (proj₁ (merge' Σ₃⊑ₕΣ₂ Q')) Σ₃}
  → Q , M , μ  ⟶ Q' , M' , μ'
  → StoreTypingProgress Σ Σ₃
⟶⟹rtti⊑Σ (prog-reduce red) = ⟶ₑ⟹rtti⊑Σ red
⟶⟹rtti⊑Σ (state-reduce red) = from⊑ₕ (⟶ₛ⟹rtti⊑Σ red)

⟶⟹qst : ∀ {Σ Σ₁ Σ₂ Σ₃ A} {Q : List (SuspendedCast Σ)} {Q' : List (SuspendedCast Σ₂)}
             {Σ₁⊑ₕΣ : Σ₁ ⊑ₕ Σ} {Σ₃⊑ₕΣ₂ : Σ₃ ⊑ₕ Σ₂} {M : proj₁ (merge' Σ₁⊑ₕΣ Q) ∣ ∅ ⊢ A}
             {μ : Store (proj₁ (merge' Σ₁⊑ₕΣ Q)) Σ₁}
             {M' : proj₁ (merge' Σ₃⊑ₕΣ₂ Q') ∣ ∅ ⊢ A}
             {μ' : Store (proj₁ (merge' Σ₃⊑ₕΣ₂ Q')) Σ₃}
  → Q , M , μ  ⟶ Q' , M' , μ'
  → QueueStoreTyping Σ₁⊑ₕΣ Q
⟶⟹qst (prog-reduce red) = normal
⟶⟹qst (state-reduce {Q = Q} {A∈Σ = A∈Σ} red) = evolving Q A∈Σ
