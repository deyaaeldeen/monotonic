module MonoRef.Static.Types.Relations.Unary where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Product using (∃-syntax ; -,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
open import Relation.Nullary.Negation using (contradiction)

open import MonoRef.Static.Types


infix  4 static_

data Injectable : Type → Set where
  I-⇒    : ∀ {A B} → Injectable (A ⇒ B)
  I-Ref  : ∀ {A}   → Injectable (Ref A)
  I-×    : ∀ {A B} → Injectable (A `× B)
  I-ℕ    :           Injectable `ℕ
  I-Unit :           Injectable Unit

data Base : Type → Set where
  B-`ℕ   : Base `ℕ
  B-Unit : Base Unit

data Type/>0Args : Type → Set where
  T-⇒    : ∀ {A B} → Type/>0Args (A ⇒ B)
  T-Ref  : ∀ {A}   → Type/>0Args (Ref A)
  T-×    : ∀ {A B} → Type/>0Args (A `× B)

data static_ : Type → Set where
  static-ℕ    : static `ℕ
  static-unit : static Unit
  static-⇒    : ∀ {A B} → static A → static B → static A ⇒ B
  static-ref  : ∀ {A} → static A → static Ref A
  static-×    : ∀ {A B} → static A → static B → static A `× B

T≡⋆? : (A : Type) → Dec (A ≡ ⋆)
T≡⋆? ⋆ = yes refl
T≡⋆? (_ ⇒ _) = no (λ ())
T≡⋆? (Ref _) = no (λ ())
T≡⋆? (_ `× _) = no (λ ())
T≡⋆? `ℕ = no (λ ())
T≡⋆? Unit = no (λ ())

T≡Ref? : (A : Type) → Dec (∃[ B ] (A ≡ Ref B))
T≡Ref? (_ ⇒ _) = no (λ ())
T≡Ref? (Ref _) = yes (-, refl)
T≡Ref? (_ `× _) = no (λ ())
T≡Ref? `ℕ = no (λ ())
T≡Ref? Unit = no (λ ())
T≡Ref? ⋆ = no (λ ())

¬⋆⇒Injectable : ∀ {A} → A ≢ ⋆ → Injectable A
¬⋆⇒Injectable {_ ⇒ _}  ¬⋆ = I-⇒
¬⋆⇒Injectable {Ref _}  ¬⋆ = I-Ref
¬⋆⇒Injectable {_ `× _} ¬⋆ = I-×
¬⋆⇒Injectable {`ℕ}     ¬⋆ = I-ℕ
¬⋆⇒Injectable {Unit}   ¬⋆ = I-Unit
¬⋆⇒Injectable {⋆}      ¬⋆ = contradiction refl ¬⋆

Injectable⋆⇒⊥ : Injectable ⋆ → ⊥
Injectable⋆⇒⊥ ()

base-decidable : ∀ A → Dec (Base A)
base-decidable (A ⇒ A₁) = no (λ ())
base-decidable (Ref A) = no (λ ())
base-decidable (A `× A₁) = no (λ ())
base-decidable `ℕ = yes B-`ℕ
base-decidable Unit = yes B-Unit
base-decidable ⋆ = no (λ ())

inj-decidable : ∀ A → Dec (Injectable A)
inj-decidable (A ⇒ A₁) = yes I-⇒
inj-decidable (Ref A) = yes I-Ref
inj-decidable (A `× A₁) = yes I-×
inj-decidable `ℕ = yes I-ℕ
inj-decidable Unit = yes I-Unit
inj-decidable ⋆ = no (λ ())

¬Base⇒>0Arg : ∀ {A} → Injectable A → ¬ Base A → Type/>0Args A
¬Base⇒>0Arg I-⇒ y = T-⇒
¬Base⇒>0Arg I-Ref y = T-Ref
¬Base⇒>0Arg I-× y = T-×
¬Base⇒>0Arg I-ℕ y = ⊥-elim (y B-`ℕ)
¬Base⇒>0Arg I-Unit y = ⊥-elim (y B-Unit)

injectable-respect-≡ : ∀ {A} → (x y : Injectable A) → x ≡ y
injectable-respect-≡ I-⇒ I-⇒ = refl
injectable-respect-≡ I-Ref I-Ref = refl
injectable-respect-≡ I-× I-× = refl
injectable-respect-≡ I-ℕ I-ℕ = refl
injectable-respect-≡ I-Unit I-Unit = refl

Base-respect-≡ : ∀ {A} → (x y : Base A) → x ≡ y
Base-respect-≡ B-`ℕ B-`ℕ = refl
Base-respect-≡ B-Unit B-Unit = refl

¬Injectable⇒≡⋆ : ∀ {A} → ¬ Injectable A → A ≡ ⋆
¬Injectable⇒≡⋆ {A ⇒ A₁} ¬p = ⊥-elim (¬p I-⇒)
¬Injectable⇒≡⋆ {Ref A} ¬p = ⊥-elim (¬p I-Ref)
¬Injectable⇒≡⋆ {A `× A₁} ¬p = ⊥-elim (¬p I-×)
¬Injectable⇒≡⋆ {`ℕ} ¬p = ⊥-elim (¬p I-ℕ)
¬Injectable⇒≡⋆ {Unit} ¬p = ⊥-elim (¬p I-Unit)
¬Injectable⇒≡⋆ {⋆} _ = refl

injectable-to-type : ∀ {A} → Injectable A → Type
injectable-to-type {A} _ = A
