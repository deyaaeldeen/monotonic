module MonoRef.Dynamics.EvolvingStore.Ptr where

open import Data.List.Any using (here ; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary using (yes ; no)

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


{-

  PtrInEquality provides a proof that two pointers are not pointing to the same
  element.

-}

data PtrInEquality {Σ : StoreTyping}{A} (A∈Σ : A ∈ Σ) : ∀ {B} → B ∈ Σ → Set where
  PIE-ty : (A'∈Σ : A ∈ Σ) → A'∈Σ ≢ A∈Σ → PtrInEquality A∈Σ A'∈Σ
  PIE-ptr : ∀ {B} → A ≢ B → (B∈Σ : B ∈ Σ) → PtrInEquality A∈Σ B∈Σ
