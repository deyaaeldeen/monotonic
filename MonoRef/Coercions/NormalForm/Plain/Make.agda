module MonoRef.Coercions.NormalForm.Plain.Make where

open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes ; no)

open import MonoRef.Coercions.NormalForm.Plain.Syntax
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


make-normal-form-coercion : ∀ A B → NormalFormCoercion A B
make-normal-form-coercion A B with ⌣-decidable A B
... | no _            = final (middle fail)
... | yes ⌣-ℕ-refl    = final (middle id)
... | yes ⌣-Unit-refl = final (middle id)
make-normal-form-coercion A .⋆ | yes ⌣-⋆R
    with T≡⋆? A
...    | yes refl = final (middle id)
...    | no ¬⋆    = final (injSeq (¬⋆⇒Injectable ¬⋆) id)
make-normal-form-coercion .⋆ B | yes ⌣-⋆L
    with T≡⋆? B
...    | yes refl = final (middle id)
...    | no ¬⋆    = prjSeq (¬⋆⇒Injectable ¬⋆) (middle id)
make-normal-form-coercion (A `× B) (A' `× B') | yes ⌣-×
   with make-normal-form-coercion A A' | make-normal-form-coercion B B'
...   | c | d = final (middle (prod c d))
make-normal-form-coercion (A ⇒ B) (A' ⇒ B') | yes ⌣-⇒
   with make-normal-form-coercion A' A | make-normal-form-coercion B B'
...   | c | d = final (middle (fun c d))
make-normal-form-coercion .(Ref _) (Ref B) | yes ⌣-ref = final (middle (Ref B ⊑-reflexive))

make-middle-coercion : ∀ {A B}
  → Injectable A → Injectable B → MiddleCoercion A B
make-middle-coercion A B with ⌣-decidableᵢ A B
make-middle-coercion {A} {B} _ _ | no _ = fail
... | yes ⌣-ℕ-refl    = id
... | yes ⌣-Unit-refl = id
make-middle-coercion {A ⇒ B} {A' ⇒ B'} _ _ | yes ⌣-⇒
    with make-normal-form-coercion A' A | make-normal-form-coercion B B'
...    | c | d = fun c d
make-middle-coercion {A `× B} {A' `× B'} _ _ | yes ⌣-×
    with make-normal-form-coercion A A' | make-normal-form-coercion B B'
...    | c | d = prod c d
make-middle-coercion {Ref _} {Ref B} _ _ | yes ⌣-ref = Ref B ⊑-reflexive
make-middle-coercion () _ | yes ⌣-⋆L
make-middle-coercion _ () | yes ⌣-⋆R

-- TODO: rewrite compose in terms of make-middle-coercion and delete
-- make-final-coercion
make-final-coercion : ∀ {A B}
  → Injectable A → Injectable B → FinalCoercion A B
make-final-coercion A B = middle (make-middle-coercion A B)
