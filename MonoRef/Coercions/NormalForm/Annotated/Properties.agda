module MonoRef.Coercions.NormalForm.Annotated.Properties where

open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality using (_≢_ ; refl)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Relation.Nullary.Negation using (contradiction)

open import MonoRef.Coercions.NormalForm.Annotated.Compose
open import MonoRef.Coercions.NormalForm.Annotated.Make
open import MonoRef.Coercions.NormalForm.Annotated.Syntax
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


make-coercionA⋆⇒Inert : ∀ {A} → Injectable A → InertNormalForm (make-normal-form-coercion A ⋆)
make-coercionA⋆⇒Inert {A} iA
  with ⌣-decidable A ⋆
make-coercionA⋆⇒Inert () | yes ⌣-⋆L
make-coercionA⋆⇒Inert {A} iA | yes ⌣-⋆R
  with T≡⋆? A
make-coercionA⋆⇒Inert () | yes ⌣-⋆R | yes refl
... | no ¬p = I-final (I-injSeq (¬⋆⇒Injectable ¬p))
make-coercionA⋆⇒Inert _ | no ¬p = ⊥-elim (¬p ⌣-⋆R)

A⇒RefB-coercion⇒Active : ∀ {A B} → (c : NormalFormCoercion A (Ref B)) → ActiveNormalForm c
A⇒RefB-coercion⇒Active (prjSeq iA x) = A-prjSeq iA x
A⇒RefB-coercion⇒Active (final (middle (id _))) = A-final (A-middle A-id)
A⇒RefB-coercion⇒Active (final (middle (Ref _ _ C x))) = A-final (A-middle (A-Ref C x))
A⇒RefB-coercion⇒Active (final (middle (fail _ _))) = A-final (A-middle A-fail)

⋆Acoercion⇒Active : ∀ {A} → Injectable A → (c : NormalFormCoercion ⋆ A) → ActiveNormalForm c
⋆Acoercion⇒Active iA (prjSeq iA₁ x) = A-prjSeq iA₁ x
⋆Acoercion⇒Active () (final (injSeq iB x))
⋆Acoercion⇒Active iA (final (middle (id _))) = A-final (A-middle A-id)
⋆Acoercion⇒Active iA (final (middle (fail _ _))) = A-final (A-middle A-fail)

Inert⇒¬Active-normform : ∀ {A B} {c : NormalFormCoercion A B} → InertNormalForm c → ¬ ActiveNormalForm c
Inert⇒¬Active-normform (I-final (I-injSeq iB)) = λ { (A-final ()) }
Inert⇒¬Active-normform (I-final (I-middle I-fun)) = λ { (A-final (A-middle ())) }
