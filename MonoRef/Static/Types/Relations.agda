module MonoRef.Static.Types.Relations where

open import Data.List using (List)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Binary using (Decidable)
open import Relation.Nullary using (yes ; no)

open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations.Consistency public
open import MonoRef.Static.Types.Relations.Meet public
open import MonoRef.Static.Types.Relations.TypePreciseness public
open import MonoRef.Static.Types.Relations.Unary public


StoreTyping = List Type

≡Type-decidable : Decidable (_≡_ {A = Type})
≡Type-decidable (A ⇒ B) (A' ⇒ B')
  with ≡Type-decidable A A' | ≡Type-decidable B B'
... | yes refl | yes refl = yes refl
... | yes refl | no B≢B' = no λ {refl → B≢B' refl}
... | no A≢A'  | _ = no λ {refl → A≢A' refl}
≡Type-decidable (_ ⇒ _) (Ref _) = no (λ ())
≡Type-decidable (_ ⇒ _) (_ `× _) = no (λ ())
≡Type-decidable (_ ⇒ _) `ℕ = no (λ ())
≡Type-decidable (_ ⇒ _) Unit = no (λ ())
≡Type-decidable (_ ⇒ _) ⋆ = no (λ ())
≡Type-decidable (Ref A) (_ ⇒ _) = no (λ ())
≡Type-decidable (Ref A) (Ref B) with ≡Type-decidable A B
≡Type-decidable (Ref A) (Ref .A) | yes refl = yes refl
≡Type-decidable (Ref A) (Ref B) | no A≢B = no (λ {refl → A≢B refl})
≡Type-decidable (Ref _) (_ `× _) = no (λ ())
≡Type-decidable (Ref _) `ℕ = no (λ ())
≡Type-decidable (Ref _) Unit = no (λ ())
≡Type-decidable (Ref _) ⋆ = no (λ ())
≡Type-decidable (_ `× _) (_ ⇒ _) = no (λ ())
≡Type-decidable (_ `× _) (Ref _) = no (λ ())
≡Type-decidable (A `× B) (A' `× B')
  with ≡Type-decidable A A' | ≡Type-decidable B B'
... | yes refl | yes refl = yes refl
... | yes refl | no B≢B' = no λ {refl → B≢B' refl}
... | no A≢A' | _ = no λ {refl → A≢A' refl}
≡Type-decidable (_ `× _) `ℕ = no (λ ())
≡Type-decidable (_ `× _) Unit = no (λ ())
≡Type-decidable (_ `× _) ⋆ = no (λ ())
≡Type-decidable `ℕ (_ ⇒ _) = no (λ ())
≡Type-decidable `ℕ (Ref _) = no (λ ())
≡Type-decidable `ℕ (_ `× _) = no (λ ())
≡Type-decidable `ℕ `ℕ = yes refl
≡Type-decidable `ℕ Unit = no (λ ())
≡Type-decidable `ℕ ⋆ = no (λ ())
≡Type-decidable Unit (_ ⇒ _) = no (λ ())
≡Type-decidable Unit (Ref _) = no (λ ())
≡Type-decidable Unit (_ `× _) = no (λ ())
≡Type-decidable Unit `ℕ = no (λ ())
≡Type-decidable Unit Unit = yes refl
≡Type-decidable Unit ⋆ = no (λ ())
≡Type-decidable ⋆ (_ ⇒ _) = no (λ ())
≡Type-decidable ⋆ (Ref _) = no (λ ())
≡Type-decidable ⋆ (_ `× _) = no (λ ())
≡Type-decidable ⋆ `ℕ = no (λ ())
≡Type-decidable ⋆ Unit = no (λ ())
≡Type-decidable ⋆ ⋆ = yes refl
