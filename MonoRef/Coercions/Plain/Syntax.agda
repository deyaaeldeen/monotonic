module MonoRef.Coercions.Plain.Syntax where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product using (∃ ; ∃-syntax ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)

open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


infix  4 _⟹_

data _⟹_ : Type → Type → Set where
  ι : ∀ {A} → A ⟹ A
  prj : ∀ {A} → Injectable A → ⋆ ⟹ A
  inj : ∀ {A} → Injectable A → A ⟹ ⋆
  _⇒_ : ∀ {A A' B B'}
    → (c : A' ⟹ A) → (d : B ⟹ B')
      ------------------------------
    → A ⇒ B ⟹ A' ⇒ B'
  _`×_ : ∀ {A A' B B'}
    → A ⟹ A' → B ⟹ B'
      ------------------
    → A `× B ⟹ A' `× B'
  Ref : (A B : Type) → Ref A ⟹ Ref B
  `⊥ : ∀ {A B} → ¬ A ∼ B → A ⟹ B

data Inert : ∀ {A B} → A ⟹ B → Set where
  I-⇒ : ∀{A B A' B'}{c : B ⟹ A} {d : A' ⟹ B'} → Inert (c ⇒ d)
  I-inj : ∀ {A} → (iA : Injectable A) → Inert (inj iA)

data Active : ∀ {A B} → A ⟹ B → Set where
  A-ι : ∀ {A} → Active (ι {A})
  A-prj : ∀ {A} → (iA : Injectable A) → Active (prj iA)
  A-× : ∀ {A B A' B'} {c : A ⟹ A'} {d : B ⟹ B'} → Active (c `× d)
  A-Ref : ∀ {A B} → Active (Ref A B)
  A-⊥ : ∀ {A B} {A≁B : ¬ A ∼ B} → Active (`⊥ A≁B)

Inert⇒¬Ref : ∀ {A B} {c : A ⟹ Ref B} → Inert c → ⊥
Inert⇒¬Ref ()

make-coercion : ∀ A B → A ⟹ B
make-coercion A B with ⌣-decidable A B
... | no ¬p            = `⊥ (¬⌣⇒¬∼ ¬p)
... | yes ⌣-ℕ-refl    = ι
... | yes ⌣-Unit-refl = ι
make-coercion .⋆ B | yes ⌣-⋆L with T≡⋆? B
...  | yes refl = ι
...  | no ¬⋆ = prj (¬⋆⇒Injectable ¬⋆)
make-coercion A .⋆ | yes ⌣-⋆R with T≡⋆? A
...  | yes refl = ι
...  | no ¬⋆ = inj (¬⋆⇒Injectable ¬⋆)
make-coercion (A ⇒ B) (A' ⇒ B') | yes ⌣-⇒ =
  make-coercion A' A ⇒ make-coercion B B'
make-coercion (A `× B) (A' `× B') | yes ⌣-× =
  make-coercion A A' `× make-coercion B B'
make-coercion (Ref A) (Ref B) | yes ⌣-ref = Ref A B

inertP : ∀ {A B} → (c : A ⟹ B) → Dec (Inert c)
inertP ι = no (λ ())
inertP (prj _) = no (λ ())
inertP (inj x) = yes (I-inj x)
inertP (_ ⇒ _) = yes I-⇒
inertP (_ `× _) = no (λ ())
inertP (Ref _ _) = no (λ ())
inertP (`⊥ _) = no (λ ())

¬Inert⇒Active : ∀ {A B} {c : A ⟹ B} → ¬ Inert c → Active c
¬Inert⇒Active {c = ι} _ = A-ι
¬Inert⇒Active {c = prj x} _ = A-prj x
¬Inert⇒Active {c = inj x} ¬Inert = ⊥-elim (¬Inert (I-inj x))
¬Inert⇒Active {c = _ ⇒ _} ¬Inert = ⊥-elim (¬Inert I-⇒)
¬Inert⇒Active {c = _ `× _} _ = A-×
¬Inert⇒Active {c = Ref _ _} _ = A-Ref
¬Inert⇒Active {c = `⊥ _} _ = A-⊥
