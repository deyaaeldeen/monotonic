module MonoRef.Coercions.NormalForm.Annotated.Make where

open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes ; no)

open import MonoRef.Coercions.NormalForm.Annotated.Syntax
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


make-normal-form-coercion : ∀ A B → NormalFormCoercion A B
make-normal-form-coercion A B with ⌣-decidable A B
... | no _            = final (middle (fail A B))
... | yes ⌣-ℕ-refl    = final (middle (id `ℕ))
... | yes ⌣-Unit-refl = final (middle (id Unit))
make-normal-form-coercion A .⋆ | yes ⌣-⋆R
    with T≡⋆? A
...    | yes refl = final (middle (id ⋆))
...    | no ¬⋆    = final (injSeq (¬⋆⇒Injectable ¬⋆) (id A))
make-normal-form-coercion .⋆ B | yes ⌣-⋆L
    with T≡⋆? B
...    | yes refl = final (middle (id ⋆))
...    | no ¬⋆    = prjSeq (¬⋆⇒Injectable ¬⋆) (middle (id B))
make-normal-form-coercion (A `× B) (A' `× B') | yes ⌣-×
   with make-normal-form-coercion A A' | make-normal-form-coercion B B'
...   | c | d = final (middle (prod c d))
make-normal-form-coercion (A ⇒ B) (A' ⇒ B') | yes ⌣-⇒
   with make-normal-form-coercion A' A | make-normal-form-coercion B B'
...   | c | d = final (middle (fun c d))
make-normal-form-coercion (Ref A) (Ref B) | yes ⌣-ref = final (middle (Ref A B B ⊑-reflexive))

make-final-coercion : ∀ {A B}
  → Injectable A → Injectable B → FinalCoercion A B
make-final-coercion A B with ⌣-decidableᵢ A B
make-final-coercion {A} {B} _ _ | no _ = middle (fail A B)
... | yes ⌣-ℕ-refl    = middle (id `ℕ)
... | yes ⌣-Unit-refl = middle (id Unit)
make-final-coercion {A ⇒ B} {A' ⇒ B'} _ _ | yes ⌣-⇒
    with make-normal-form-coercion A' A | make-normal-form-coercion B B'
...    | c | d = middle (fun c d)
make-final-coercion {A `× B} {A' `× B'} _ _ | yes ⌣-×
    with make-normal-form-coercion A A' | make-normal-form-coercion B B'
...    | c | d = middle (prod c d)
make-final-coercion {Ref A} {Ref B} _ _ | yes ⌣-ref = middle (Ref A B B ⊑-reflexive)
make-final-coercion () _ | yes ⌣-⋆L
make-final-coercion _ () | yes ⌣-⋆R
