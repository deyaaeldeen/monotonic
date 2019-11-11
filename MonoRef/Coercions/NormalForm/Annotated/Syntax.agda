module MonoRef.Coercions.NormalForm.Annotated.Syntax where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
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

  final : ∀ {A B} → FinalCoercion A B → NormalFormCoercion A B

data FinalCoercion where

  injSeq : ∀ {A B} → (iB : Injectable B) → MiddleCoercion A B → FinalCoercion A ⋆

  middle : ∀ {A B} → MiddleCoercion A B → FinalCoercion A B

data MiddleCoercion where

  id : ∀ A → MiddleCoercion A A

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

  Ref : ∀ A B → (C : Type) → C ⊑ B → MiddleCoercion (Ref A) (Ref B)

  fail : ∀ A B → MiddleCoercion A B


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

  A-final : ∀ {A B} {fc : FinalCoercion A B}
      --------------------------------------------
    → ActiveFinal fc → ActiveNormalForm (final fc)

data ActiveFinal where

  A-middle : ∀ {A B} {mc : MiddleCoercion A B}
      -----------------------------------------
    → ActiveMiddle mc → ActiveFinal (middle mc)

data ActiveMiddle where

  A-id : ∀ {A} → ActiveMiddle (id A)

  A-prod : ∀ {A A' B B'}
    → (c : NormalFormCoercion A A')
    → (d : NormalFormCoercion B B')
      -----------------------------
    → ActiveMiddle (prod c d)

  A-Ref : ∀ {A B} → (C : Type) → (C⊑B : C ⊑ B) → ActiveMiddle (Ref A B C C⊑B)

  A-fail : ∀ {A B} → ActiveMiddle (fail A B)

Inert⇒¬Ref : ∀ {A B} {c : NormalFormCoercion A (Ref B)} → InertNormalForm c → ⊥
Inert⇒¬Ref (I-final (I-middle ()))

inert-normalform-decidable : ∀ {A B} → (c : NormalFormCoercion A B) → Dec (InertNormalForm c)
inert-final-decidable : ∀ {A B} → (c : FinalCoercion A B) → Dec (InertFinal c)
inert-middle-decidable : ∀ {A B} → (c : MiddleCoercion A B) → Dec (InertMiddle c)

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
inert-middle-decidable (Ref _ _ _ _) = no (λ ())
inert-middle-decidable (fail _ _) = no (λ ())

¬Inert⇒Active-normform : ∀ {A B} {c : NormalFormCoercion A B} → ¬ InertNormalForm c → ActiveNormalForm c
¬Inert⇒Active-final : ∀ {A B} {c : FinalCoercion A B} → ¬ InertFinal c → ActiveFinal c
¬Inert⇒Active-middle : ∀ {A B} {c : MiddleCoercion A B} → ¬ InertMiddle c → ActiveMiddle c

¬Inert⇒Active-normform {c = prjSeq iA x} _ = A-prjSeq iA x
¬Inert⇒Active-normform {c = final fc} ¬Inert =
  A-final (¬Inert⇒Active-final (λ x → ¬Inert (I-final x)))

¬Inert⇒Active-final {c = injSeq iB _} ¬Inert = ⊥-elim (¬Inert (I-injSeq iB))
¬Inert⇒Active-final {c = middle x} ¬Inert =
  A-middle (¬Inert⇒Active-middle (λ x → ¬Inert (I-middle x)))

¬Inert⇒Active-middle {c = id _} _ = A-id
¬Inert⇒Active-middle {c = fun _ _} ¬Inert = ⊥-elim (¬Inert I-fun)
¬Inert⇒Active-middle {c = prod c d} ¬Inert = A-prod c d
¬Inert⇒Active-middle {c = Ref _ _ x y} ¬Inert = A-Ref x y
¬Inert⇒Active-middle {c = fail _ _} ¬Inert = A-fail

get-source-type : ∀ {A B} → NormalFormCoercion A B → Type
get-source-type/middle : ∀ {A B} → MiddleCoercion A B → Type
get-target-type : ∀ {A B} → NormalFormCoercion A B → Type
get-target-type/final : ∀ {A B} → FinalCoercion A B → Type
get-target-type/middle : ∀ {A B} → MiddleCoercion A B → Type

get-source-type (prjSeq iA x) = ⋆
get-source-type (final (injSeq iB c)) = get-source-type/middle c
get-source-type (final (middle c)) = get-source-type/middle c

get-source-type/middle (id A) = A
get-source-type/middle (fun c d) = get-target-type c ⇒ get-source-type d
get-source-type/middle (prod c d) = get-source-type c `× get-source-type d
get-source-type/middle (Ref A B C x) = Ref A
get-source-type/middle (fail A B) = A

get-target-type (prjSeq iA c) = get-target-type/final c
get-target-type (final c) = get-target-type/final c

get-target-type/final (injSeq _ _) = ⋆
get-target-type/final (middle c) = get-target-type/middle c


get-target-type/middle (id A) = A
get-target-type/middle (fun c d) = get-source-type c ⇒ get-target-type d
get-target-type/middle (prod c d) = get-target-type c `× get-target-type d
get-target-type/middle (Ref A B C x) = Ref B
get-target-type/middle (fail A B) = B

get-source-type-wt : ∀ {A B} → (c : NormalFormCoercion A B) → get-source-type c ≡ A
get-source-type/middle-wt : ∀ {A B} → (c : MiddleCoercion A B) → get-source-type/middle c ≡ A
get-target-type-wt : ∀ {A B} → (c : NormalFormCoercion A B) → get-target-type c ≡ B
get-target-type/final-wt : ∀ {A B} → (c : FinalCoercion A B) → get-target-type/final c ≡ B
get-target-type/middle-wt : ∀ {A B} → (c : MiddleCoercion A B) → get-target-type/middle c ≡ B

get-source-type/middle-wt (id A) = refl
get-source-type/middle-wt (fun c d)
  rewrite get-target-type-wt c | get-source-type-wt d = refl
get-source-type/middle-wt (prod c d)
  rewrite get-source-type-wt c | get-source-type-wt d = refl
get-source-type/middle-wt (Ref A B C x) = refl
get-source-type/middle-wt (fail A B) = refl

get-source-type-wt (prjSeq iA x) = refl
get-source-type-wt (final (injSeq iB c)) = get-source-type/middle-wt c
get-source-type-wt (final (middle c)) = get-source-type/middle-wt c

get-target-type-wt (prjSeq iA c) = get-target-type/final-wt c
get-target-type-wt (final c) = get-target-type/final-wt c

get-target-type/final-wt (injSeq iB x) = refl
get-target-type/final-wt (middle c) = get-target-type/middle-wt c

get-target-type/middle-wt (id A) = refl
get-target-type/middle-wt (fun c d)
  rewrite get-source-type-wt c | get-target-type-wt d = refl
get-target-type/middle-wt (prod c d)
  rewrite get-target-type-wt c | get-target-type-wt d = refl
get-target-type/middle-wt (Ref A B C x) = refl
get-target-type/middle-wt (fail A B) = refl
