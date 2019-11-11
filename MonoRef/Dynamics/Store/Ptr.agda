module MonoRef.Dynamics.Store.Ptr where

open import Data.Fin using (Fin)
open import Data.List using (length)
open import Data.List.Any using (here ; there ; index)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no)

open import MonoRef.Static.Types.Relations

{-

  ≡Ptr-decidable checks for pointer equality given that the things are pointed to
  have the same exact type.

-}

≡Ptr-decidable : ∀ {Σ : StoreTyping} {A} → Decidable (_≡_ {A = A ∈ Σ})
≡Ptr-decidable (here refl) (here refl) = yes refl
≡Ptr-decidable (here refl) (there _) = no (λ ())
≡Ptr-decidable (there p1) (here px) = no (λ ())
≡Ptr-decidable (there p1) (there p2)
  with ≡Ptr-decidable p1 p2
... | yes refl = yes refl
... | no ¬p = no λ {refl → ¬p refl}

data SamePtrLocs {A B} : ∀ {Σ Σ' : StoreTyping} → A ∈ Σ → B ∈ Σ' → Set where
  here : ∀ {Σₗ Σᵣ} → SamePtrLocs (here {x = A} {xs = Σₗ} refl) (here {x = B} {xs = Σᵣ} refl)
  there : ∀ {Tₗ Tᵣ Σₗ Σᵣ} {A∈Σₗ : A ∈ Σₗ} {B∈Σᵣ : B ∈ Σᵣ}
    → SamePtrLocs A∈Σₗ B∈Σᵣ → SamePtrLocs (there {x = Tₗ} A∈Σₗ) (there {x = Tᵣ} B∈Σᵣ)

SamePtrLocs-decidable : ∀ {Σ Σ' A B} → (A∈Σ : A ∈ Σ) → (B∈Σ' : B ∈ Σ') → Dec (SamePtrLocs A∈Σ B∈Σ')
SamePtrLocs-decidable (here refl) (here refl) = yes here
SamePtrLocs-decidable (here refl) (there B∈Σ') = no (λ ())
SamePtrLocs-decidable (there A∈Σ) (here refl) = no (λ ())
SamePtrLocs-decidable (there A∈Σ) (there B∈Σ')
  with SamePtrLocs-decidable A∈Σ B∈Σ'
... | yes p = yes (there p)
... | no ¬p = no λ { (there x) → ¬p x}

data PtrEquality {Σ : StoreTyping}{A} (A∈Σ : A ∈ Σ) : ∀ {Σ' B} → B ∈ Σ' → Set where
  intro : PtrEquality A∈Σ A∈Σ

{-

  PtrInEquality provides a proof that two pointers are not pointing to the same
  element.

-}

data PtrInEquality {Σ : StoreTyping}{A} (A∈Σ : A ∈ Σ) : ∀ {B} → B ∈ Σ → Set where
  PIE-ty : (A'∈Σ : A ∈ Σ) → A'∈Σ ≢ A∈Σ → PtrInEquality A∈Σ A'∈Σ
  PIE-ptr : ∀ {B} → A ≢ B → (B∈Σ : B ∈ Σ) → PtrInEquality A∈Σ B∈Σ

data Ptr (Σ : StoreTyping) : Set where
  addr : ∀ {A} → A ∈ Σ → Ptr Σ

ptr-index : ∀ {Σ} → Ptr Σ → Fin (length Σ)
ptr-index (addr x) = index x
