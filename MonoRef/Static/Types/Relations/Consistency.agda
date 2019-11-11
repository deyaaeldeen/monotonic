module MonoRef.Static.Types.Relations.Consistency where

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl)
open import Relation.Binary using (Decidable ; Reflexive ; Symmetric)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)

open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations.Unary


infix  4 _∼_

data _∼_ : Type → Type → Set where
  ∼-ℕ-refl : `ℕ ∼ `ℕ
  ∼-Unit-refl : Unit ∼ Unit
  ∼-⋆-refl : ⋆ ∼ ⋆
  ∼-⋆R : ∀ {A} → Injectable A → A ∼ ⋆
  ∼-⋆L : ∀ {A} → Injectable A → ⋆ ∼ A
  ~-⇒ : ∀ {A B A' B'} → A ∼ B → A' ∼ B' → A ⇒ A' ∼ B ⇒ B'
  ~-× : ∀ {A B A' B'} → A ∼ B → A' ∼ B' → A `× A' ∼ B `× B'
  ~-ref : ∀ {A B} → A ∼ B → Ref A ∼ Ref B

{- Shallow Consistency, used in Lazy Casts -}

data _⌣_ : Type → Type → Set where
  ⌣-ℕ-refl : `ℕ ⌣ `ℕ
  ⌣-Unit-refl : Unit ⌣ Unit
  ⌣-⋆L : ∀ {A} → ⋆ ⌣ A
  ⌣-⋆R : ∀ {A} → A ⌣ ⋆
  ⌣-⇒ : ∀{A B A' B'} → (A ⇒ B) ⌣ (A' ⇒ B')
  ⌣-× : ∀{A B A' B'} → (A `× B) ⌣ (A' `× B')
  ⌣-ref : ∀{A B} → (Ref A) ⌣ (Ref B)

{- Properties of the consistency relation -}

∼-refl : Reflexive _∼_
∼-refl {_ ⇒ _} = ~-⇒ ∼-refl ∼-refl
∼-refl {Ref _} = ~-ref ∼-refl
∼-refl {_ `× _} = ~-× ∼-refl ∼-refl
∼-refl {`ℕ} = ∼-ℕ-refl
∼-refl {Unit} = ∼-Unit-refl
∼-refl {⋆} = ∼-⋆-refl

∼-sym : Symmetric _∼_
∼-sym ∼-ℕ-refl = ∼-ℕ-refl
∼-sym ∼-Unit-refl = ∼-Unit-refl
∼-sym ∼-⋆-refl = ∼-⋆-refl
∼-sym (∼-⋆R x) = ∼-⋆L x
∼-sym (∼-⋆L x) = ∼-⋆R x
∼-sym (~-⇒ x x₁) = ~-⇒ (∼-sym x) (∼-sym x₁)
∼-sym (~-× x x₁) = ~-× (∼-sym x) (∼-sym x₁)
∼-sym (~-ref x) = ~-ref (∼-sym x)

∼-decidable : Decidable _∼_
∼-decidable (A ⇒ B) (A' ⇒ B')
  with ∼-decidable A A' | ∼-decidable B B'
... | yes p | yes p₁ = yes (~-⇒ p p₁)
... | yes p | no ¬p = no λ {(~-⇒ _ x) → ¬p x}
... | no ¬p | yes p = no λ {(~-⇒ x _) → ¬p x}
... | no ¬p | no ¬p₁ = no λ {(~-⇒ x _) → ¬p x}
∼-decidable (_ ⇒ _) (Ref _) = no (λ ())
∼-decidable (_ ⇒ _) (_ `× _) = no (λ ())
∼-decidable (_ ⇒ _) `ℕ = no (λ ())
∼-decidable (_ ⇒ _) Unit = no (λ ())
∼-decidable (_ ⇒ _) ⋆ = yes (∼-⋆R I-⇒)
∼-decidable (Ref _) (_ ⇒ _) = no (λ ())
∼-decidable (Ref A) (Ref B)
  with ∼-decidable A B
... | yes p = yes (~-ref p)
... | no ¬p = no λ {(~-ref x) → ¬p x}
∼-decidable (Ref _) (_ `× _) = no (λ ())
∼-decidable (Ref _) `ℕ = no (λ ())
∼-decidable (Ref _) Unit = no (λ ())
∼-decidable (Ref _) ⋆ = yes (∼-⋆R I-Ref)
∼-decidable (_ `× _) (_ ⇒ _) = no (λ ())
∼-decidable (_ `× _) (Ref _) = no (λ ())
∼-decidable (A `× B) (A' `× B')
  with ∼-decidable A A' | ∼-decidable B B'
... | yes p | yes p₁ = yes (~-× p p₁)
... | yes p | no ¬p = no λ {(~-× _ x) → ¬p x}
... | no ¬p | yes p = no λ {(~-× x _) → ¬p x}
... | no ¬p | no ¬p₁ = no λ {(~-× x _) → ¬p x}
∼-decidable (_ `× _) `ℕ = no (λ ())
∼-decidable (_ `× _) Unit = no (λ ())
∼-decidable (_ `× _) ⋆ = yes (∼-⋆R I-×)
∼-decidable `ℕ (A' ⇒ B) = no (λ ())
∼-decidable `ℕ (Ref _) = no (λ ())
∼-decidable `ℕ (_ `× _) = no (λ ())
∼-decidable `ℕ `ℕ = yes ∼-ℕ-refl
∼-decidable `ℕ Unit = no (λ ())
∼-decidable `ℕ ⋆ = yes (∼-⋆R I-ℕ)
∼-decidable Unit (_ ⇒ _) = no (λ ())
∼-decidable Unit (Ref _) = no (λ ())
∼-decidable Unit (_ `× _) = no (λ ())
∼-decidable Unit `ℕ = no (λ ())
∼-decidable Unit Unit = yes ∼-Unit-refl
∼-decidable Unit ⋆ = yes (∼-⋆R I-Unit)
∼-decidable ⋆ A
  with T≡⋆? A
... | yes refl = yes ∼-⋆-refl
... | no ¬A≡⋆ = yes (∼-⋆L (¬⋆⇒Injectable ¬A≡⋆))

{- Properties of shallow consistency -}

⌣-decidable : Decidable _⌣_
⌣-decidable (_ ⇒ _) (_ ⇒ _) = yes ⌣-⇒
⌣-decidable (_ ⇒ _) (Ref _) = no (λ ())
⌣-decidable (_ ⇒ _) (_ `× _) = no (λ ())
⌣-decidable (_ ⇒ _) `ℕ = no (λ ())
⌣-decidable (_ ⇒ _) Unit = no (λ ())
⌣-decidable (_ ⇒ _) ⋆ = yes ⌣-⋆R
⌣-decidable (Ref _) (_ ⇒ _) = no (λ ())
⌣-decidable (Ref _) (Ref _) = yes ⌣-ref
⌣-decidable (Ref _) (_ `× _) = no (λ ())
⌣-decidable (Ref _) `ℕ = no (λ ())
⌣-decidable (Ref _) Unit = no (λ ())
⌣-decidable (Ref _) ⋆ = yes ⌣-⋆R
⌣-decidable (_ `× _) (_ ⇒ _) = no (λ ())
⌣-decidable (_ `× _) (Ref _) = no (λ ())
⌣-decidable (_ `× _) (_ `× _) = yes ⌣-×
⌣-decidable (_ `× _) `ℕ = no (λ ())
⌣-decidable (_ `× _) Unit = no (λ ())
⌣-decidable (_ `× _) ⋆ = yes ⌣-⋆R
⌣-decidable `ℕ (_ ⇒ _) = no (λ ())
⌣-decidable `ℕ (Ref _) = no (λ ())
⌣-decidable `ℕ (_ `× _) = no (λ ())
⌣-decidable `ℕ `ℕ = yes ⌣-ℕ-refl
⌣-decidable `ℕ Unit = no (λ ())
⌣-decidable `ℕ ⋆ = yes ⌣-⋆R
⌣-decidable Unit (_ ⇒ _) = no (λ ())
⌣-decidable Unit (Ref _) = no (λ ())
⌣-decidable Unit (_ `× _) = no (λ ())
⌣-decidable Unit `ℕ = no (λ ())
⌣-decidable Unit Unit = yes ⌣-Unit-refl
⌣-decidable Unit ⋆ = yes ⌣-⋆R
⌣-decidable ⋆ _ = yes ⌣-⋆L

⌣-decidableᵢ : ∀ {A B} → Injectable A → Injectable B → Dec (A ⌣ B)
⌣-decidableᵢ {A} {B} _ _ = ⌣-decidable A B

∼-respects-≡ : ∀ {A B} → (A∼B A∼B' : A ∼ B) → A∼B ≡ A∼B'
∼-respects-≡ ∼-ℕ-refl ∼-ℕ-refl = refl
∼-respects-≡ ∼-Unit-refl ∼-Unit-refl = refl
∼-respects-≡ ∼-⋆-refl ∼-⋆-refl = refl
∼-respects-≡ ∼-⋆-refl (∼-⋆R ())
∼-respects-≡ ∼-⋆-refl (∼-⋆L ())
∼-respects-≡ (∼-⋆R ()) ∼-⋆-refl
∼-respects-≡ (∼-⋆R x) (∼-⋆R y)
  rewrite injectable-respect-≡ x y = refl
∼-respects-≡ (∼-⋆R ()) (∼-⋆L x₁)
∼-respects-≡ (∼-⋆L ()) ∼-⋆-refl
∼-respects-≡ (∼-⋆L ()) (∼-⋆R x₁)
∼-respects-≡ (∼-⋆L x) (∼-⋆L y)
  rewrite injectable-respect-≡ x y = refl
∼-respects-≡ (~-⇒ x x₁) (~-⇒ y y₁)
  rewrite ∼-respects-≡ x y | ∼-respects-≡ x₁ y₁ = refl
∼-respects-≡ (~-× x x₁) (~-× y y₁)
  rewrite ∼-respects-≡ x y | ∼-respects-≡ x₁ y₁ = refl
∼-respects-≡ (~-ref x) (~-ref y)
  rewrite ∼-respects-≡ x y = refl

¬⌣⇒≢⋆R : ∀ {A B} → ¬ (A ⌣ B) → B ≢ ⋆
¬⌣⇒≢⋆R ¬p refl = ¬p ⌣-⋆R

∼⇒⌣ : ∀ {A B} → A ∼ B → A ⌣ B
∼⇒⌣ ∼-ℕ-refl = ⌣-ℕ-refl
∼⇒⌣ ∼-Unit-refl = ⌣-Unit-refl
∼⇒⌣ ∼-⋆-refl = ⌣-⋆L
∼⇒⌣ (∼-⋆R _) = ⌣-⋆R
∼⇒⌣ (∼-⋆L _) = ⌣-⋆L
∼⇒⌣ (~-⇒ _ _) = ⌣-⇒
∼⇒⌣ (~-× _ _) = ⌣-×
∼⇒⌣ (~-ref _) = ⌣-ref

¬⌣⇒¬∼ : ∀ {A B} → ¬ (A ⌣ B) → ¬ A ∼ B
¬⌣⇒¬∼ ¬p x = ¬p (∼⇒⌣ x)
