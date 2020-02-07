module MonoRef.Coercions.Annotated.Syntax where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product using (∃ ; ∃-syntax ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)

open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


infix  4 _⟹_

data _⟹_ : Type → Type → Set where
  ι : (A : Type) → A ⟹ A
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
  `⊥ : (A B : Type) → ¬ A ∼ B → A ⟹ B

data Inert : ∀ {A B} → A ⟹ B → Set where
  I-⇒ : ∀{A B A' B'}{c : B ⟹ A} {d : A' ⟹ B'} → Inert (c ⇒ d)
  I-inj : ∀ {A} → (iA : Injectable A) → Inert (inj iA)

data Active : ∀ {A B} → A ⟹ B → Set where
  A-ι : ∀ {A} → Active (ι A)
  A-prj : ∀ {A} → (iA : Injectable A) → Active (prj iA)
  A-× : ∀ {A B A' B'} {c : A ⟹ A'} {d : B ⟹ B'} → Active (c `× d)
  A-Ref : ∀ {A B} → Active (Ref A B)
  A-⊥ : ∀ {A B} {A≁B : ¬ A ∼ B} → Active (`⊥ A B A≁B)

Inert⇒¬Ref : ∀ {A B} {c : A ⟹ Ref B} → Inert c → ⊥
Inert⇒¬Ref ()

make-coercion : ∀ A B → A ⟹ B
make-coercion A B with ⌣-decidable A B
... | no ¬p            = `⊥ A B (¬⌣⇒¬∼ ¬p)
... | yes ⌣-ℕ-refl    = ι `ℕ
... | yes ⌣-Unit-refl = ι Unit
make-coercion .⋆ B | yes ⌣-⋆L with T≡⋆? B
...  | yes refl = ι ⋆
...  | no ¬⋆ = prj (¬⋆⇒Injectable ¬⋆)
make-coercion A .⋆ | yes ⌣-⋆R with T≡⋆? A
...  | yes refl = ι ⋆
...  | no ¬⋆ = inj (¬⋆⇒Injectable ¬⋆)
make-coercion (A ⇒ B) (A' ⇒ B') | yes ⌣-⇒ =
  make-coercion A' A ⇒ make-coercion B B'
make-coercion (A `× B) (A' `× B') | yes ⌣-× =
  make-coercion A A' `× make-coercion B B'
make-coercion (Ref A) (Ref B) | yes ⌣-ref = Ref A B

inertP : ∀ {A B} → (c : A ⟹ B) → Dec (Inert c)
inertP (ι _) = no (λ ())
inertP (prj _) = no (λ ())
inertP (inj x) = yes (I-inj x)
inertP (_ ⇒ _) = yes I-⇒
inertP (_ `× _) = no (λ ())
inertP (Ref _ _) = no (λ ())
inertP (`⊥ _ _ _) = no (λ ())

¬Inert⇒Active : ∀ {A B} {c : A ⟹ B} → ¬ Inert c → Active c
¬Inert⇒Active {c = ι _} _ = A-ι
¬Inert⇒Active {c = prj x} _ = A-prj x
¬Inert⇒Active {c = inj x} ¬Inert = ⊥-elim (¬Inert (I-inj x))
¬Inert⇒Active {c = _ ⇒ _} ¬Inert = ⊥-elim (¬Inert I-⇒)
¬Inert⇒Active {c = _ `× _} _ = A-×
¬Inert⇒Active {c = Ref _ _} _ = A-Ref
¬Inert⇒Active {c = `⊥ _ _ _} _ = A-⊥

get-source-type : ∀ {A B} → A ⟹ B → Type
get-target-type : ∀ {A B} → A ⟹ B → Type

get-source-type (ι A) = A
get-source-type (prj x) = ⋆
get-source-type (inj x) = injectable-to-type x
get-source-type (c ⇒ d) = get-target-type c ⇒ get-source-type d
get-source-type (c `× d) = get-source-type c `× get-source-type d
get-source-type (Ref A B) = Ref A
get-source-type (`⊥ A B x) = A

get-target-type (ι A) = A
get-target-type (prj x) = injectable-to-type x
get-target-type (inj x) = ⋆
get-target-type (c ⇒ d) = get-source-type c ⇒ get-target-type d
get-target-type (c `× d) = get-target-type c `× get-target-type d
get-target-type (Ref A B) = Ref B
get-target-type (`⊥ A B x) = B

get-source-type-wt : ∀ {A B} → (c : A ⟹ B) → get-source-type c ≡ A
get-target-type-wt : ∀ {A B} → (c : A ⟹ B) → get-target-type c ≡ B

get-source-type-wt (ι A) = refl
get-source-type-wt (prj x) = refl
get-source-type-wt (inj x) = refl
get-source-type-wt (c ⇒ d) rewrite get-target-type-wt c | get-source-type-wt d = refl
get-source-type-wt (c `× d) rewrite get-source-type-wt c | get-source-type-wt d = refl
get-source-type-wt (Ref A B) = refl
get-source-type-wt (`⊥ A B x) = refl

get-target-type-wt (ι A) = refl
get-target-type-wt (prj x) = refl
get-target-type-wt (inj x) = refl
get-target-type-wt (c ⇒ d) rewrite get-source-type-wt c | get-target-type-wt d = refl
get-target-type-wt (c `× d) rewrite get-target-type-wt c | get-target-type-wt d = refl
get-target-type-wt (Ref A B) = refl
get-target-type-wt (`⊥ A B x) = refl
