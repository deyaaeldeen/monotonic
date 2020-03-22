module MonoRef.Coercions.NormalForm.Plain.Syntax where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)

open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


data NormalFormCoercion : (A B : Type) → Set
data FinalCoercion      : (A B : Type) → Set
data MiddleCoercion     : (A B : Type) → Set

data NormalFormCoercion where

  prjSeq : ∀ {A B}
    → (iA : Injectable A) → FinalCoercion A B
      ---------------------------------------
    → NormalFormCoercion ⋆ B

  id⋆ : NormalFormCoercion ⋆ ⋆

  final : ∀ {A B} → FinalCoercion A B → NormalFormCoercion A B

data FinalCoercion where

  injSeq : ∀ {A B} → (iB : Injectable B) → MiddleCoercion A B → FinalCoercion A ⋆

  middle : ∀ {A B} → MiddleCoercion A B → FinalCoercion A B

data MiddleCoercion where

  id : ∀ {A} → Injectable A → MiddleCoercion A A

  fun : ∀ {A A' B B'}
    → NormalFormCoercion A' A
    → NormalFormCoercion B B'
      --------------------------------
    → MiddleCoercion (A ⇒ B) (A' ⇒ B')

  prod : ∀ {A A' B B'}
    → NormalFormCoercion A A'
    → NormalFormCoercion B B'
      ----------------------------------
    → MiddleCoercion (A `× B) (A' `× B')

  Ref : ∀ {A B} → (C : Type) → C ⊑ B → MiddleCoercion (Ref A) (Ref B)

  fail : ∀ {A B} → MiddleCoercion A B


data InertNormalForm : ∀ {A B} → NormalFormCoercion A B → Set
data InertFinal      : ∀ {A B} → FinalCoercion      A B → Set
data InertMiddle     : ∀ {A B} → MiddleCoercion     A B → Set

data InertMiddle where

  I-fun : ∀{A B A' B'} {c : NormalFormCoercion A' A} {d : NormalFormCoercion B B'}
      ---------------------
    → InertMiddle (fun c d)

data InertFinal where

  I-injSeq : ∀ {A B} {g : MiddleCoercion A B}
      ----------------------------------------------
    → (iB : Injectable B) → InertFinal (injSeq iB g)

  I-middle : ∀ {A B} {g : MiddleCoercion A B}
      -------------------------------------
    → InertMiddle g → InertFinal (middle g)

data InertNormalForm where

  I-final : ∀ {A B} {i : FinalCoercion A B}
      ----------------------------------------
    → InertFinal i → InertNormalForm (final i)

data ActiveNormalForm : ∀ {A B} → NormalFormCoercion A B → Set
data ActiveFinal      : ∀ {A B} → FinalCoercion      A B → Set
data ActiveMiddle     : ∀ {A B} → MiddleCoercion     A B → Set

data ActiveNormalForm where

  A-prjSeq : ∀ {A B}
    → (iA : Injectable A) → (fc : FinalCoercion A B)
      ----------------------------------------------
    → ActiveNormalForm (prjSeq iA fc)

  A-id⋆ : ActiveNormalForm id⋆

  A-final : ∀ {A B} {fc : FinalCoercion A B}
      --------------------------------------------
    → ActiveFinal fc → ActiveNormalForm (final fc)

data ActiveFinal where

  A-middle : ∀ {A B} {mc : MiddleCoercion A B}
      -----------------------------------------
    → ActiveMiddle mc → ActiveFinal (middle mc)

data ActiveMiddle where

  A-id : ∀ {A} → (iA : Injectable A) → ActiveMiddle (id iA)

  A-prod : ∀ {A A' B B'}
    → (c : NormalFormCoercion A A')
    → (d : NormalFormCoercion B B')
      -----------------------------
    → ActiveMiddle (prod c d)

  A-Ref : ∀ {A B} → (C : Type) → (C⊑B : C ⊑ B) → ActiveMiddle (Ref {A} C C⊑B)

  A-fail : ∀ {A B} → ActiveMiddle (fail {A}{B})

Inert⇒¬Ref : ∀ {A B} {c : NormalFormCoercion A (Ref B)} → InertNormalForm c → ⊥
Inert⇒¬Ref (I-final (I-middle ()))

inert-normalform-decidable : ∀ {A B} → (c : NormalFormCoercion A B) → Dec (InertNormalForm c)
inert-final-decidable : ∀ {A B} → (c : FinalCoercion A B) → Dec (InertFinal c)
inert-middle-decidable : ∀ {A B} → (c : MiddleCoercion A B) → Dec (InertMiddle c)

inert-normalform-decidable id⋆ = no (λ ())
inert-normalform-decidable (prjSeq _ _) = no (λ ())
inert-normalform-decidable (final c)
  with inert-final-decidable c
... | yes d = yes (I-final d)
... | no a = no λ { (I-final b) → a b}

inert-final-decidable (injSeq iB _) = yes (I-injSeq iB)
inert-final-decidable (middle c)
  with inert-middle-decidable c
... | yes d = yes (I-middle d)
... | no a = no λ { (I-middle b) → a b}

inert-middle-decidable (id _) = no (λ ())
inert-middle-decidable (fun _ _) = yes I-fun
inert-middle-decidable (prod _ _) = no (λ ())
inert-middle-decidable (Ref _ _) = no (λ ())
inert-middle-decidable fail = no (λ ())

¬Inert⇒Active-normform : ∀ {A B} {c : NormalFormCoercion A B} → ¬ InertNormalForm c → ActiveNormalForm c
¬Inert⇒Active-final : ∀ {A B} {c : FinalCoercion A B} → ¬ InertFinal c → ActiveFinal c
¬Inert⇒Active-middle : ∀ {A B} {c : MiddleCoercion A B} → ¬ InertMiddle c → ActiveMiddle c

¬Inert⇒Active-normform {c = id⋆} _ = A-id⋆
¬Inert⇒Active-normform {c = prjSeq iA x} _ = A-prjSeq iA x
¬Inert⇒Active-normform {c = final fc} ¬Inert =
  A-final (¬Inert⇒Active-final (λ x → ¬Inert (I-final x)))

¬Inert⇒Active-final {c = injSeq iB _} ¬Inert = ⊥-elim (¬Inert (I-injSeq iB))
¬Inert⇒Active-final {c = middle x} ¬Inert =
  A-middle (¬Inert⇒Active-middle (λ x → ¬Inert (I-middle x)))

¬Inert⇒Active-middle {c = id x} _ = A-id x
¬Inert⇒Active-middle {c = fun _ _} ¬Inert = ⊥-elim (¬Inert I-fun)
¬Inert⇒Active-middle {c = prod c d} ¬Inert = A-prod c d
¬Inert⇒Active-middle {c = Ref x y} ¬Inert = A-Ref x y
¬Inert⇒Active-middle {c = fail} ¬Inert = A-fail
