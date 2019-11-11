module MonoRef.Static.Types.Relations.TypePreciseness where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Binary using (Antisymmetric ; Decidable ; Reflexive ; Transitive)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)

open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations.Unary
open import MonoRef.Static.Types.Relations.Consistency


infix  4 _⊑_

data _⊑_ : Type → Type → Set where
  ⊑-refl : ∀ {A} → Base A → A ⊑ A
  ⊑-dyn  : ∀ {A} → A ⊑ ⋆
  ⊑-×    : ∀ {A B C D} → A ⊑ B → C ⊑ D → A `× C ⊑ B `× D
  ⊑-⇒    : ∀ {A B A' B'} → A ⊑ A' → B ⊑ B' → A ⇒ B ⊑ A' ⇒ B'
  ⊑-ref  : ∀ {A B} → A ⊑ B → Ref A ⊑ Ref B

{- Properties of type precision  -}

⊑-trans : Transitive _⊑_
⊑-trans (⊑-refl x) y = y
⊑-trans ⊑-dyn (⊑-refl ())
⊑-trans ⊑-dyn ⊑-dyn = ⊑-dyn
⊑-trans (⊑-× _ _) (⊑-refl ())
⊑-trans (⊑-× _ _) ⊑-dyn = ⊑-dyn
⊑-trans (⊑-× x x₁) (⊑-× y y₁) = ⊑-× (⊑-trans x y) (⊑-trans x₁ y₁)
⊑-trans (⊑-⇒ _ _) (⊑-refl ())
⊑-trans (⊑-⇒ _ _) ⊑-dyn = ⊑-dyn
⊑-trans (⊑-⇒ x x₁) (⊑-⇒ y y₁) = ⊑-⇒ (⊑-trans x y) (⊑-trans x₁ y₁)
⊑-trans (⊑-ref _) (⊑-refl ())
⊑-trans (⊑-ref _) ⊑-dyn = ⊑-dyn
⊑-trans (⊑-ref x) (⊑-ref y) = ⊑-ref (⊑-trans x y)

⋆⊑⋆ : ∀ {A} → ⋆ ⊑ A → A ≡ ⋆
⋆⊑⋆ (⊑-refl ())
⋆⊑⋆ ⊑-dyn = refl

⊑-antisymmetric : Antisymmetric _≡_ _⊑_
⊑-antisymmetric (⊑-refl _) _ = refl
⊑-antisymmetric ⊑-dyn x = ⋆⊑⋆ x
⊑-antisymmetric (⊑-× _ _) (⊑-refl ())
⊑-antisymmetric (⊑-× a b) (⊑-× a' b')
  rewrite ⊑-antisymmetric a a' | ⊑-antisymmetric b b' = refl
⊑-antisymmetric (⊑-⇒ _ _) (⊑-refl ())
⊑-antisymmetric (⊑-⇒ a b) (⊑-⇒ a' b')
  rewrite ⊑-antisymmetric a a' | ⊑-antisymmetric b b' = refl
⊑-antisymmetric (⊑-ref _) (⊑-refl ())
⊑-antisymmetric (⊑-ref a) (⊑-ref x) rewrite ⊑-antisymmetric a x = refl

⊑-decidable : Decidable _⊑_
⊑-decidable (A ⇒ B) (A' ⇒ B')
  with ⊑-decidable A A' | ⊑-decidable B B'
... | yes A⊑A' | yes B⊑B' = yes (⊑-⇒ A⊑A' B⊑B')
... | yes A⊑A' | no ¬B⊑B' = no λ { (⊑-refl ()) ; (⊑-⇒ _ x) → ¬B⊑B' x}
... | no ¬A⊑A' | q = no (λ { (⊑-refl ()) ; (⊑-⇒ x _) → ¬A⊑A' x})
⊑-decidable (_ ⇒ _) (Ref _) = no (λ ())
⊑-decidable (_ ⇒ _) (_ `× _) = no (λ ())
⊑-decidable (_ ⇒ _) `ℕ = no (λ ())
⊑-decidable (_ ⇒ _) Unit = no (λ ())
⊑-decidable (_ ⇒ _) ⋆ = yes ⊑-dyn
⊑-decidable (Ref _) (_ ⇒ _) = no (λ ())
⊑-decidable (Ref A) (Ref B)
  with ⊑-decidable A B
... | yes A⊑B = yes (⊑-ref A⊑B)
... | no ¬A⊑A' = no (λ { (⊑-refl ()) ; (⊑-ref x) → ¬A⊑A' x})
⊑-decidable (Ref _) (_ `× _) = no (λ ())
⊑-decidable (Ref _) `ℕ = no (λ ())
⊑-decidable (Ref _) Unit = no (λ ())
⊑-decidable (Ref _) ⋆ = yes ⊑-dyn
⊑-decidable (A `× B) (A' `× B')
  with ⊑-decidable A A' | ⊑-decidable B B'
... | yes A⊑A' | yes B⊑B' = yes (⊑-× A⊑A' B⊑B')
... | yes A⊑A' | no ¬B⊑B' = no λ { (⊑-refl ()) ; (⊑-× _ x) → ¬B⊑B' x}
... | no ¬A⊑A' | q = no (λ { (⊑-refl ()) ; (⊑-× x _) → ¬A⊑A' x})
⊑-decidable (_ `× _) (Ref _) = no (λ ())
⊑-decidable (_ `× _) (_ ⇒ _) = no (λ ())
⊑-decidable (_ `× _) `ℕ = no (λ ())
⊑-decidable (_ `× _) Unit = no (λ ())
⊑-decidable (_ `× _) ⋆ = yes ⊑-dyn
⊑-decidable `ℕ (_ ⇒ _) = no (λ ())
⊑-decidable `ℕ (Ref _) = no (λ ())
⊑-decidable `ℕ (_ `× _) = no (λ ())
⊑-decidable `ℕ `ℕ = yes (⊑-refl B-`ℕ)
⊑-decidable `ℕ Unit = no (λ ())
⊑-decidable `ℕ ⋆ = yes ⊑-dyn
⊑-decidable Unit (_ ⇒ _) = no (λ ())
⊑-decidable Unit (Ref _) = no (λ ())
⊑-decidable Unit (_ `× _) = no (λ ())
⊑-decidable Unit `ℕ = no (λ ())
⊑-decidable Unit Unit = yes (⊑-refl B-Unit)
⊑-decidable Unit ⋆ = yes ⊑-dyn
⊑-decidable ⋆ (_ ⇒ _) = no (λ ())
⊑-decidable ⋆ (Ref _) = no (λ ())
⊑-decidable ⋆ (_ `× _) = no (λ ())
⊑-decidable ⋆ `ℕ = no (λ ())
⊑-decidable ⋆ Unit = no (λ ())
⊑-decidable ⋆ ⋆ = yes ⊑-dyn

⊑-respect-static : ∀ {t t'} → t' ⊑ t → static t → t' ≡ t
⊑-respect-static (⊑-refl _) st = refl
⊑-respect-static ⊑-dyn ()
⊑-respect-static (⊑-× prec₁ prec₂) (static-× st₁ st₂)
  rewrite ⊑-respect-static prec₁ st₁ | ⊑-respect-static prec₂ st₂ = refl
⊑-respect-static (⊑-⇒ prec₁ prec₂) (static-⇒ st₁ st₂)
  rewrite ⊑-respect-static prec₁ st₁ | ⊑-respect-static prec₂ st₂ = refl
⊑-respect-static (⊑-ref prec) (static-ref st)
  rewrite ⊑-respect-static prec st  = refl

⊑⇒∼ : ∀ {A B} → A ⊑ B → A ∼ B
⊑⇒∼ (⊑-refl _) = ∼-refl
⊑⇒∼ {A} ⊑-dyn
  with T≡⋆? A
... | yes refl = ∼-⋆-refl
... | no ¬A≡⋆ = ∼-⋆R (¬⋆⇒Injectable ¬A≡⋆)
⊑⇒∼ (⊑-× x y) = ~-× (⊑⇒∼ x) (⊑⇒∼ y)
⊑⇒∼ (⊑-⇒ x y) = ~-⇒ (⊑⇒∼ x) (⊑⇒∼ y)
⊑⇒∼ (⊑-ref x) = ~-ref (⊑⇒∼ x)

A⊑A : ∀ A → A ⊑ A

Type/>0Args⇒⊑ : ∀ {A} → Type/>0Args A → A ⊑ A
Type/>0Args⇒⊑ {A = A ⇒ B} T-⇒ = ⊑-⇒ (A⊑A A) (A⊑A B)
Type/>0Args⇒⊑ {A = Ref A} T-Ref = ⊑-ref (A⊑A A)
Type/>0Args⇒⊑ {A = A `× B} T-× = ⊑-× (A⊑A A) (A⊑A B)

inj⇒⊑ : ∀ {A} → Injectable A → A ⊑ A
inj⇒⊑ {A} A-inj
  with base-decidable A
... | yes A-base = ⊑-refl A-base
... | no ¬A-base = Type/>0Args⇒⊑ (¬Base⇒>0Arg A-inj ¬A-base)

¬Injectable⇒⊑ : ∀ {A} → ¬ Injectable A → A ⊑ A
¬Injectable⇒⊑ {A ⇒ A₁} x = ⊥-elim (x I-⇒)
¬Injectable⇒⊑ {Ref A} x = ⊥-elim (x I-Ref)
¬Injectable⇒⊑ {A `× A₁} x = ⊥-elim (x I-×)
¬Injectable⇒⊑ {`ℕ} x = ⊥-elim (x I-ℕ)
¬Injectable⇒⊑ {Unit} x = ⊥-elim (x I-Unit)
¬Injectable⇒⊑ {⋆} x = ⊑-dyn

A⊑A A with inj-decidable A
... | no ¬A-inj = ¬Injectable⇒⊑ ¬A-inj
... | yes A-inj = inj⇒⊑ A-inj

A⊑B⊑D≡A⊑C⊑D : ∀ {A B C D}
  → (A⊑B : A ⊑ B)
  → (A⊑C : A ⊑ C)
  → (B⊑D : B ⊑ D)
  → (C⊑D : C ⊑ D)
  → (⊑-trans A⊑B B⊑D) ≡ (⊑-trans A⊑C C⊑D)
A⊑B⊑D≡A⊑C⊑D (⊑-refl x) (⊑-refl x₂) (⊑-refl B-`ℕ) (⊑-refl B-`ℕ) = refl
A⊑B⊑D≡A⊑C⊑D (⊑-refl x) (⊑-refl x₂) (⊑-refl B-Unit) (⊑-refl B-Unit) = refl
A⊑B⊑D≡A⊑C⊑D (⊑-refl x) ⊑-dyn (⊑-refl x₁) (⊑-refl ())
A⊑B⊑D≡A⊑C⊑D (⊑-refl x) ⊑-dyn (⊑-refl ()) ⊑-dyn
A⊑B⊑D≡A⊑C⊑D (⊑-refl x) (⊑-× A⊑C A⊑C₁) (⊑-refl ()) C⊑D
A⊑B⊑D≡A⊑C⊑D (⊑-refl x) (⊑-⇒ A⊑C A⊑C₁) (⊑-refl ()) C⊑D
A⊑B⊑D≡A⊑C⊑D (⊑-refl x) (⊑-ref A⊑C) (⊑-refl ()) C⊑D
A⊑B⊑D≡A⊑C⊑D (⊑-refl x) (⊑-refl x₁) ⊑-dyn (⊑-refl ())
A⊑B⊑D≡A⊑C⊑D (⊑-refl x) (⊑-refl x₁) ⊑-dyn ⊑-dyn = refl
A⊑B⊑D≡A⊑C⊑D (⊑-refl x) ⊑-dyn ⊑-dyn (⊑-refl ())
A⊑B⊑D≡A⊑C⊑D (⊑-refl x) ⊑-dyn ⊑-dyn ⊑-dyn = refl
A⊑B⊑D≡A⊑C⊑D (⊑-refl ()) (⊑-× A⊑C A⊑C₁) ⊑-dyn C⊑D
A⊑B⊑D≡A⊑C⊑D (⊑-refl ()) (⊑-⇒ A⊑C A⊑C₁) ⊑-dyn C⊑D
A⊑B⊑D≡A⊑C⊑D (⊑-refl ()) (⊑-ref A⊑C) ⊑-dyn C⊑D
A⊑B⊑D≡A⊑C⊑D (⊑-refl ()) A⊑C (⊑-× B⊑D B⊑D₁) C⊑D
A⊑B⊑D≡A⊑C⊑D (⊑-refl ()) A⊑C (⊑-⇒ B⊑D B⊑D₁) C⊑D
A⊑B⊑D≡A⊑C⊑D (⊑-refl ()) A⊑C (⊑-ref B⊑D) C⊑D
A⊑B⊑D≡A⊑C⊑D ⊑-dyn A⊑C (⊑-refl ()) C⊑D
A⊑B⊑D≡A⊑C⊑D ⊑-dyn A⊑C ⊑-dyn (⊑-refl ())
A⊑B⊑D≡A⊑C⊑D ⊑-dyn (⊑-refl x) ⊑-dyn ⊑-dyn = refl
A⊑B⊑D≡A⊑C⊑D ⊑-dyn ⊑-dyn ⊑-dyn ⊑-dyn = refl
A⊑B⊑D≡A⊑C⊑D ⊑-dyn (⊑-× A⊑C A⊑C₁) ⊑-dyn ⊑-dyn = refl
A⊑B⊑D≡A⊑C⊑D ⊑-dyn (⊑-⇒ A⊑C A⊑C₁) ⊑-dyn ⊑-dyn = refl
A⊑B⊑D≡A⊑C⊑D ⊑-dyn (⊑-ref A⊑C) ⊑-dyn ⊑-dyn = refl
A⊑B⊑D≡A⊑C⊑D (⊑-× A⊑B A⊑B₁) A⊑C (⊑-refl ()) C⊑D
A⊑B⊑D≡A⊑C⊑D (⊑-× A⊑B A⊑B₁) A⊑C ⊑-dyn (⊑-refl ())
A⊑B⊑D≡A⊑C⊑D (⊑-× A⊑B A⊑B₁) (⊑-refl ()) ⊑-dyn ⊑-dyn
A⊑B⊑D≡A⊑C⊑D (⊑-× A⊑B A⊑B₁) ⊑-dyn ⊑-dyn ⊑-dyn = refl
A⊑B⊑D≡A⊑C⊑D (⊑-× A⊑B A⊑B₁) (⊑-× A⊑C A⊑C₁) ⊑-dyn ⊑-dyn = refl
A⊑B⊑D≡A⊑C⊑D (⊑-× A⊑B A⊑B₁) (⊑-refl ()) (⊑-× B⊑D B⊑D₁) C⊑D
A⊑B⊑D≡A⊑C⊑D (⊑-× A⊑B A⊑B₁) ⊑-dyn (⊑-× B⊑D B⊑D₁) ()
A⊑B⊑D≡A⊑C⊑D (⊑-× A⊑B A⊑B₁) (⊑-× A⊑C A⊑C₁) (⊑-× B⊑D B⊑D₁) (⊑-refl ())
A⊑B⊑D≡A⊑C⊑D (⊑-× A⊑B A⊑B₁) (⊑-× A⊑C A⊑C₁) (⊑-× B⊑D B⊑D₁) (⊑-× C⊑D C⊑D₁)
  rewrite A⊑B⊑D≡A⊑C⊑D A⊑B A⊑C B⊑D C⊑D | A⊑B⊑D≡A⊑C⊑D A⊑B₁ A⊑C₁ B⊑D₁ C⊑D₁ = refl
A⊑B⊑D≡A⊑C⊑D (⊑-⇒ A⊑B A⊑B₁) A⊑C (⊑-refl ()) C⊑D
A⊑B⊑D≡A⊑C⊑D (⊑-⇒ A⊑B A⊑B₁) A⊑C ⊑-dyn (⊑-refl ())
A⊑B⊑D≡A⊑C⊑D (⊑-⇒ A⊑B A⊑B₁) (⊑-refl ()) ⊑-dyn ⊑-dyn
A⊑B⊑D≡A⊑C⊑D (⊑-⇒ A⊑B A⊑B₁) ⊑-dyn ⊑-dyn ⊑-dyn = refl
A⊑B⊑D≡A⊑C⊑D (⊑-⇒ A⊑B A⊑B₁) (⊑-⇒ A⊑C A⊑C₁) ⊑-dyn ⊑-dyn = refl
A⊑B⊑D≡A⊑C⊑D (⊑-⇒ A⊑B A⊑B₁) (⊑-refl ()) (⊑-⇒ B⊑D B⊑D₁) C⊑D
A⊑B⊑D≡A⊑C⊑D (⊑-⇒ A⊑B A⊑B₁) ⊑-dyn (⊑-⇒ B⊑D B⊑D₁) ()
A⊑B⊑D≡A⊑C⊑D (⊑-⇒ A⊑B A⊑B₁) (⊑-⇒ A⊑C A⊑C₁) (⊑-⇒ B⊑D B⊑D₁) (⊑-refl ())
A⊑B⊑D≡A⊑C⊑D (⊑-⇒ A⊑B A⊑B₁) (⊑-⇒ A⊑C A⊑C₁) (⊑-⇒ B⊑D B⊑D₁) (⊑-⇒ C⊑D C⊑D₁)
  rewrite A⊑B⊑D≡A⊑C⊑D A⊑B A⊑C B⊑D C⊑D | A⊑B⊑D≡A⊑C⊑D A⊑B₁ A⊑C₁ B⊑D₁ C⊑D₁ = refl
A⊑B⊑D≡A⊑C⊑D (⊑-ref A⊑B) A⊑C (⊑-refl ()) C⊑D
A⊑B⊑D≡A⊑C⊑D (⊑-ref A⊑B) A⊑C ⊑-dyn (⊑-refl ())
A⊑B⊑D≡A⊑C⊑D (⊑-ref A⊑B) (⊑-refl ()) ⊑-dyn ⊑-dyn
A⊑B⊑D≡A⊑C⊑D (⊑-ref A⊑B) ⊑-dyn ⊑-dyn ⊑-dyn = refl
A⊑B⊑D≡A⊑C⊑D (⊑-ref A⊑B) (⊑-ref A⊑C) ⊑-dyn ⊑-dyn = refl
A⊑B⊑D≡A⊑C⊑D (⊑-ref A⊑B) (⊑-refl ()) (⊑-ref B⊑D) C⊑D
A⊑B⊑D≡A⊑C⊑D (⊑-ref A⊑B) ⊑-dyn (⊑-ref B⊑D) ()
A⊑B⊑D≡A⊑C⊑D (⊑-ref A⊑B) (⊑-ref A⊑C) (⊑-ref B⊑D) (⊑-refl ())
A⊑B⊑D≡A⊑C⊑D (⊑-ref A⊑B) (⊑-ref A⊑C) (⊑-ref B⊑D) (⊑-ref C⊑D)
  rewrite A⊑B⊑D≡A⊑C⊑D A⊑B A⊑C B⊑D C⊑D = refl

⊑-reflexive : Reflexive _⊑_
⊑-reflexive {A} = A⊑A A

∼-respects-⊑ : ∀ {A B C} → B ⊑ A → B ∼ C → A ∼ C
∼-respects-⊑ (⊑-refl x) B∼C = B∼C
∼-respects-⊑ {C = C} ⊑-dyn B∼C
  with T≡⋆? C
... | yes refl = ∼-⋆-refl
... | no ¬p = ∼-⋆L (¬⋆⇒Injectable ¬p)
∼-respects-⊑ (⊑-× B⊑A B⊑A₁) (∼-⋆R x) = ∼-⋆R I-×
∼-respects-⊑ (⊑-× B⊑A B⊑A₁) (~-× B∼C B∼C₁) = ~-× (∼-respects-⊑ B⊑A B∼C) (∼-respects-⊑ B⊑A₁ B∼C₁)
∼-respects-⊑ (⊑-⇒ B⊑A B⊑A₁) (∼-⋆R x) = ∼-⋆R I-⇒
∼-respects-⊑ (⊑-⇒ B⊑A B⊑A₁) (~-⇒ B∼C B∼C₁) = ~-⇒ (∼-respects-⊑ B⊑A B∼C) (∼-respects-⊑ B⊑A₁ B∼C₁)
∼-respects-⊑ (⊑-ref B⊑A) (∼-⋆R x) = ∼-⋆R I-Ref
∼-respects-⊑ (⊑-ref B⊑A) (~-ref B∼C) = ~-ref (∼-respects-⊑ B⊑A B∼C)

⊑-trans-respects-reflʳ : ∀ {A B} → (B⊑A : B ⊑ A) → ⊑-trans B⊑A ⊑-reflexive ≡ B⊑A
⊑-trans-respects-reflʳ {A} (⊑-refl x)
  with inj-decidable A
... | no ¬p
    with A
⊑-trans-respects-reflʳ {A} (⊑-refl x) | no ¬p | w ⇒ w₁ = ⊥-elim (¬p I-⇒)
⊑-trans-respects-reflʳ {A} (⊑-refl x) | no ¬p | Ref w = ⊥-elim (¬p I-Ref)
⊑-trans-respects-reflʳ {A} (⊑-refl x) | no ¬p | w `× w₁ = ⊥-elim (¬p I-×)
⊑-trans-respects-reflʳ {A} (⊑-refl x) | no ¬p | `ℕ = ⊥-elim (¬p I-ℕ)
⊑-trans-respects-reflʳ {A} (⊑-refl x) | no ¬p | Unit = ⊥-elim (¬p I-Unit)
⊑-trans-respects-reflʳ {A} (⊑-refl ()) | no ¬p | ⋆
⊑-trans-respects-reflʳ {A} (⊑-refl x) | yes p
    with base-decidable A
...   | yes A-base rewrite Base-respect-≡ A-base x = refl
...   | no ¬A-base = ⊥-elim (¬A-base x)
⊑-trans-respects-reflʳ ⊑-dyn = refl
⊑-trans-respects-reflʳ (⊑-× B⊑A B⊑A₁)
  rewrite ⊑-trans-respects-reflʳ B⊑A | ⊑-trans-respects-reflʳ B⊑A₁ = refl
⊑-trans-respects-reflʳ (⊑-⇒ B⊑A B⊑A₁)
  rewrite ⊑-trans-respects-reflʳ B⊑A | ⊑-trans-respects-reflʳ B⊑A₁ = refl
⊑-trans-respects-reflʳ (⊑-ref B⊑A)
  rewrite ⊑-trans-respects-reflʳ B⊑A = refl

⊑-trans-respects-reflˡ : ∀ {A B} → (B⊑A : B ⊑ A) → ⊑-trans ⊑-reflexive B⊑A ≡ B⊑A
⊑-trans-respects-reflˡ {A} (⊑-refl x)
  with inj-decidable A
... | no ¬p
    with A
⊑-trans-respects-reflˡ {A} (⊑-refl x) | no ¬p | w ⇒ w₁ = ⊥-elim (¬p I-⇒)
⊑-trans-respects-reflˡ {A} (⊑-refl x) | no ¬p | Ref w = ⊥-elim (¬p I-Ref)
⊑-trans-respects-reflˡ {A} (⊑-refl x) | no ¬p | w `× w₁ = ⊥-elim (¬p I-×)
⊑-trans-respects-reflˡ {A} (⊑-refl x) | no ¬p | `ℕ = ⊥-elim (¬p I-ℕ)
⊑-trans-respects-reflˡ {A} (⊑-refl x) | no ¬p | Unit = ⊥-elim (¬p I-Unit)
⊑-trans-respects-reflˡ {A} (⊑-refl ()) | no ¬p | ⋆
⊑-trans-respects-reflˡ {A} (⊑-refl x) | yes p
    with base-decidable A
...   | yes A-base rewrite Base-respect-≡ A-base x = refl
...   | no ¬A-base = ⊥-elim (¬A-base x)
⊑-trans-respects-reflˡ {B = B} ⊑-dyn
  with inj-decidable B
... | no ¬p
    with B
⊑-trans-respects-reflˡ {B = B} ⊑-dyn | no ¬p | w ⇒ w₁ = ⊥-elim (¬p I-⇒)
⊑-trans-respects-reflˡ {B = B} ⊑-dyn | no ¬p | Ref w = ⊥-elim (¬p I-Ref)
⊑-trans-respects-reflˡ {B = B} ⊑-dyn | no ¬p | w `× w₁ = ⊥-elim (¬p I-×)
⊑-trans-respects-reflˡ {B = B} ⊑-dyn | no ¬p | `ℕ = ⊥-elim (¬p I-ℕ)
⊑-trans-respects-reflˡ {B = B} ⊑-dyn | no ¬p | Unit = ⊥-elim (¬p I-Unit)
⊑-trans-respects-reflˡ {B = B} ⊑-dyn | no ¬p | ⋆ = refl
⊑-trans-respects-reflˡ {B = B} ⊑-dyn | yes p
    with base-decidable B
...   | yes B-base = refl
...   | no ¬B-base
      with B
⊑-trans-respects-reflˡ {B = B} ⊑-dyn | yes I-⇒ | no ¬B-base | w ⇒ w₁ = refl
⊑-trans-respects-reflˡ {B = B} ⊑-dyn | yes I-Ref | no ¬B-base | Ref w = refl
⊑-trans-respects-reflˡ {B = B} ⊑-dyn | yes I-× | no ¬B-base | w `× w₁ = refl
⊑-trans-respects-reflˡ {B = B} ⊑-dyn | yes p | no ¬B-base | `ℕ = ⊥-elim (¬B-base B-`ℕ)
⊑-trans-respects-reflˡ {B = B} ⊑-dyn | yes p | no ¬B-base | Unit = ⊥-elim (¬B-base B-Unit)
⊑-trans-respects-reflˡ {B = B} ⊑-dyn | yes () | no ¬B-base | ⋆
⊑-trans-respects-reflˡ (⊑-× B⊑A B⊑A₁)
  rewrite ⊑-trans-respects-reflˡ B⊑A | ⊑-trans-respects-reflˡ B⊑A₁ = refl
⊑-trans-respects-reflˡ (⊑-⇒ B⊑A B⊑A₁)
  rewrite ⊑-trans-respects-reflˡ B⊑A | ⊑-trans-respects-reflˡ B⊑A₁ = refl
⊑-trans-respects-reflˡ (⊑-ref B⊑A)
  rewrite ⊑-trans-respects-reflˡ B⊑A = refl

⊑-trans-assoc : ∀ {A B C D}
  → (D⊑C : D ⊑ C)
  → (C⊑B : C ⊑ B)
  → (B⊑A : B ⊑ A)
  → ⊑-trans (⊑-trans D⊑C C⊑B) B⊑A ≡ ⊑-trans D⊑C (⊑-trans C⊑B B⊑A)
⊑-trans-assoc (⊑-refl _) _ _ = refl
⊑-trans-assoc ⊑-dyn (⊑-refl ()) _
⊑-trans-assoc ⊑-dyn ⊑-dyn (⊑-refl ())
⊑-trans-assoc ⊑-dyn ⊑-dyn ⊑-dyn = refl
⊑-trans-assoc (⊑-× _ _) (⊑-refl ()) _
⊑-trans-assoc (⊑-× D⊑C D⊑C₁) ⊑-dyn (⊑-refl ())
⊑-trans-assoc (⊑-× _ _) ⊑-dyn ⊑-dyn = refl
⊑-trans-assoc (⊑-× D⊑C D⊑C₁) (⊑-× C⊑B C⊑B₁) (⊑-refl ())
⊑-trans-assoc (⊑-× D⊑C D⊑C₁) (⊑-× C⊑B C⊑B₁) ⊑-dyn = refl
⊑-trans-assoc (⊑-× D⊑C D⊑C₁) (⊑-× C⊑B C⊑B₁) (⊑-× B⊑A B⊑A₁)
  rewrite ⊑-trans-assoc D⊑C C⊑B B⊑A | ⊑-trans-assoc D⊑C₁ C⊑B₁ B⊑A₁ = refl
⊑-trans-assoc (⊑-⇒ _ _) (⊑-refl ()) _
⊑-trans-assoc (⊑-⇒ D⊑C D⊑C₁) ⊑-dyn (⊑-refl ())
⊑-trans-assoc (⊑-⇒ _ _) ⊑-dyn ⊑-dyn = refl
⊑-trans-assoc (⊑-⇒ D⊑C D⊑C₁) (⊑-⇒ C⊑B C⊑B₁) (⊑-refl ())
⊑-trans-assoc (⊑-⇒ D⊑C D⊑C₁) (⊑-⇒ C⊑B C⊑B₁) ⊑-dyn = refl
⊑-trans-assoc (⊑-⇒ D⊑C D⊑C₁) (⊑-⇒ C⊑B C⊑B₁) (⊑-⇒ B⊑A B⊑A₁)
  rewrite ⊑-trans-assoc D⊑C C⊑B B⊑A | ⊑-trans-assoc D⊑C₁ C⊑B₁ B⊑A₁ = refl
⊑-trans-assoc (⊑-ref D⊑C) (⊑-refl ()) B⊑A
⊑-trans-assoc (⊑-ref D⊑C) ⊑-dyn (⊑-refl ())
⊑-trans-assoc (⊑-ref D⊑C) ⊑-dyn ⊑-dyn = refl
⊑-trans-assoc (⊑-ref D⊑C) (⊑-ref C⊑B) (⊑-refl ())
⊑-trans-assoc (⊑-ref D⊑C) (⊑-ref C⊑B) ⊑-dyn = refl
⊑-trans-assoc (⊑-ref D⊑C) (⊑-ref C⊑B) (⊑-ref B⊑A)
  rewrite ⊑-trans-assoc D⊑C C⊑B B⊑A = refl
