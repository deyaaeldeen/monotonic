module MonoRef.Coercions.NormalForm.Faithful.Make where

open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes ; no)

open import MonoRef.Coercions.NormalForm.Faithful.Syntax
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


make-normal-form-coercion : ∀ A B → NormalFormCoercion A B
make-normal-form-coercion A B with ⌣-decidable A B
... | no _            = final fail
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
make-normal-form-coercion .(Ref _) (Ref B) | yes ⌣-ref = final (middle (Ref B ⊑-refl))

make-final-coercion : ∀ {A B}
  → Injectable A → Injectable B → FinalCoercion A B
make-final-coercion A B with ⌣-decidableᵢ A B
... | no _            = fail
... | yes ⌣-ℕ-refl    = middle id
... | yes ⌣-Unit-refl = middle id
make-final-coercion {A ⇒ B} {A' ⇒ B'} _ _ | yes ⌣-⇒
    with make-normal-form-coercion A' A | make-normal-form-coercion B B'
...    | c | d = middle (fun c d)
make-final-coercion {A `× B} {A' `× B'} _ _ | yes ⌣-×
    with make-normal-form-coercion A A' | make-normal-form-coercion B B'
...    | c | d = middle (prod c d)
make-final-coercion {.(Ref _)} {Ref B} _ _ | yes ⌣-ref = middle (Ref B ⊑-refl)
make-final-coercion () _ | yes ⌣-⋆L
make-final-coercion _ () | yes ⌣-⋆R
