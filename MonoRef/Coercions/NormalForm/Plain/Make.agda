module MonoRef.Coercions.NormalForm.Plain.Make where

open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes ; no)

open import MonoRef.Coercions.NormalForm.Plain.Syntax
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


make-normal-form-coercion : ∀ A B → NormalFormCoercion A B
make-normal-form-coercion A B with ⌣-decidable A B
... | no _            = final (middle fail)
... | yes ⌣-ℕ-refl    = final (middle (id I-ℕ))
... | yes ⌣-Unit-refl = final (middle (id I-Unit))
make-normal-form-coercion A .⋆ | yes ⌣-⋆R
    with T≡⋆? A
...    | yes refl = id⋆
...    | no ¬⋆    = final (injSeq (¬⋆⇒Injectable ¬⋆) (id (¬⋆⇒Injectable ¬⋆)))
make-normal-form-coercion .⋆ B | yes ⌣-⋆L
    with T≡⋆? B
...    | yes refl = id⋆
...    | no ¬⋆    = prjSeq (¬⋆⇒Injectable ¬⋆) (middle (id (¬⋆⇒Injectable ¬⋆)))
make-normal-form-coercion (A `× B) (A' `× B') | yes ⌣-×
   with make-normal-form-coercion A A' | make-normal-form-coercion B B'
...   | c | d = final (middle (prod c d))
make-normal-form-coercion (A ⇒ B) (A' ⇒ B') | yes ⌣-⇒
   with make-normal-form-coercion A' A | make-normal-form-coercion B B'
...   | c | d = final (middle (fun c d))
make-normal-form-coercion .(Ref _) (Ref B) | yes ⌣-ref = final (middle (Ref B ⊑-reflexive))

make-middle-coercion : ∀ {A B} → Injectable A → Injectable B → MiddleCoercion A B
make-middle-coercion A B with ⌣-decidableᵢ A B
make-middle-coercion _ _ | no _ = fail
... | yes ⌣-ℕ-refl    = id B
... | yes ⌣-Unit-refl = id B
make-middle-coercion {A ⇒ B} {A' ⇒ B'} _ _ | yes ⌣-⇒
    with make-normal-form-coercion A' A | make-normal-form-coercion B B'
...    | c | d = fun c d
make-middle-coercion {A `× B} {A' `× B'} _ _ | yes ⌣-×
    with make-normal-form-coercion A A' | make-normal-form-coercion B B'
...    | c | d = prod c d
make-middle-coercion {Ref _} {Ref B} _ _ | yes ⌣-ref = Ref B ⊑-reflexive
make-middle-coercion () _ | yes ⌣-⋆L
make-middle-coercion _ () | yes ⌣-⋆R
