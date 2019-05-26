module MonoRef.Static.Types.Relations where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List)
open import Data.Product using (∃-syntax ; -,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl ; cong₂)
open import Relation.Binary using (Antisymmetric ; Decidable ; Reflexive ; Transitive ; Symmetric)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
open import Relation.Nullary.Negation using (contradiction)

open import MonoRef.Static.Types


infix  4 _⊑_
infix  4 static_
infix  4 _∼_

StoreTyping = List Type

data Injectable : Type → Set where
  I-⇒    : ∀ {A B} → Injectable (A ⇒ B)
  I-Ref  : ∀ {A}   → Injectable (Ref A)
  I-×    : ∀ {A B} → Injectable (A `× B)
  I-ℕ    :           Injectable `ℕ
  I-Unit :           Injectable Unit

data Base : Type → Set where
  B-`ℕ   : Base `ℕ
  B-Unit : Base Unit

data _⊑_ : Type → Type → Set where
  ⊑-refl : ∀ {A} → A ⊑ A
  ⊑-dyn  : ∀ {A} → A ⊑ ⋆
  ⊑-×    : ∀ {A B C D} → A ⊑ B → C ⊑ D → A `× C ⊑ B `× D
  ⊑-⇒    : ∀ {A B A' B'} → A ⊑ A' → B ⊑ B' → A ⇒ B ⊑ A' ⇒ B'
  ⊑-ref  : ∀ {A B} → A ⊑ B → Ref A ⊑ Ref B

data static_ : Type → Set where
  static-ℕ    : static `ℕ
  static-unit : static Unit
  static-⇒    : ∀ {A B} → static A → static B → static A ⇒ B
  static-ref  : ∀ {A} → static A → static Ref A
  static-×    : ∀ {A B} → static A → static B → static A `× B

data _∼_ : Type → Type → Set where
  ∼-ℕ-refl : `ℕ ∼ `ℕ
  ∼-Unit-refl : Unit ∼ Unit
  ∼-⋆R : ∀ {A} → A ∼ ⋆
  ∼-⋆L : ∀ {A} → ⋆ ∼ A
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

≡Type-decidable : Decidable (_≡_ {A = Type})
≡Type-decidable (A ⇒ B) (A' ⇒ B')
  with ≡Type-decidable A A' | ≡Type-decidable B B'
... | yes refl | yes refl = yes refl
... | yes refl | no B≢B' = no λ {refl → B≢B' refl}
... | no A≢A'  | _ = no λ {refl → A≢A' refl}
≡Type-decidable (_ ⇒ _) (Ref _) = no (λ ())
≡Type-decidable (_ ⇒ _) (_ `× _) = no (λ ())
≡Type-decidable (_ ⇒ _) `ℕ = no (λ ())
≡Type-decidable (_ ⇒ _) Unit = no (λ ())
≡Type-decidable (_ ⇒ _) ⋆ = no (λ ())
≡Type-decidable (Ref A) (_ ⇒ _) = no (λ ())
≡Type-decidable (Ref A) (Ref B) with ≡Type-decidable A B
≡Type-decidable (Ref A) (Ref .A) | yes refl = yes refl
≡Type-decidable (Ref A) (Ref B) | no A≢B = no (λ {refl → A≢B refl})
≡Type-decidable (Ref _) (_ `× _) = no (λ ())
≡Type-decidable (Ref _) `ℕ = no (λ ())
≡Type-decidable (Ref _) Unit = no (λ ())
≡Type-decidable (Ref _) ⋆ = no (λ ())
≡Type-decidable (_ `× _) (_ ⇒ _) = no (λ ())
≡Type-decidable (_ `× _) (Ref _) = no (λ ())
≡Type-decidable (A `× B) (A' `× B')
  with ≡Type-decidable A A' | ≡Type-decidable B B'
... | yes refl | yes refl = yes refl
... | yes refl | no B≢B' = no λ {refl → B≢B' refl}
... | no A≢A' | _ = no λ {refl → A≢A' refl}
≡Type-decidable (_ `× _) `ℕ = no (λ ())
≡Type-decidable (_ `× _) Unit = no (λ ())
≡Type-decidable (_ `× _) ⋆ = no (λ ())
≡Type-decidable `ℕ (_ ⇒ _) = no (λ ())
≡Type-decidable `ℕ (Ref _) = no (λ ())
≡Type-decidable `ℕ (_ `× _) = no (λ ())
≡Type-decidable `ℕ `ℕ = yes refl
≡Type-decidable `ℕ Unit = no (λ ())
≡Type-decidable `ℕ ⋆ = no (λ ())
≡Type-decidable Unit (_ ⇒ _) = no (λ ())
≡Type-decidable Unit (Ref _) = no (λ ())
≡Type-decidable Unit (_ `× _) = no (λ ())
≡Type-decidable Unit `ℕ = no (λ ())
≡Type-decidable Unit Unit = yes refl
≡Type-decidable Unit ⋆ = no (λ ())
≡Type-decidable ⋆ (_ ⇒ _) = no (λ ())
≡Type-decidable ⋆ (Ref _) = no (λ ())
≡Type-decidable ⋆ (_ `× _) = no (λ ())
≡Type-decidable ⋆ `ℕ = no (λ ())
≡Type-decidable ⋆ Unit = no (λ ())
≡Type-decidable ⋆ ⋆ = yes refl

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

{- Properties of the consistency relation -}

∼-refl : Reflexive _∼_
∼-refl {_ ⇒ _} = ~-⇒ ∼-refl ∼-refl
∼-refl {Ref _} = ~-ref ∼-refl
∼-refl {_ `× _} = ~-× ∼-refl ∼-refl
∼-refl {`ℕ} = ∼-ℕ-refl
∼-refl {Unit} = ∼-Unit-refl
∼-refl {⋆} = ∼-⋆R

∼-sym : Symmetric _∼_
∼-sym ∼-ℕ-refl = ∼-ℕ-refl
∼-sym ∼-Unit-refl = ∼-Unit-refl
∼-sym ∼-⋆R = ∼-⋆L
∼-sym ∼-⋆L = ∼-⋆R
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
∼-decidable (_ ⇒ _) ⋆ = yes ∼-⋆R
∼-decidable (Ref _) (_ ⇒ _) = no (λ ())
∼-decidable (Ref A) (Ref B)
  with ∼-decidable A B
... | yes p = yes (~-ref p)
... | no ¬p = no λ {(~-ref x) → ¬p x}
∼-decidable (Ref _) (_ `× _) = no (λ ())
∼-decidable (Ref _) `ℕ = no (λ ())
∼-decidable (Ref _) Unit = no (λ ())
∼-decidable (Ref _) ⋆ = yes ∼-⋆R
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
∼-decidable (_ `× _) ⋆ = yes ∼-⋆R
∼-decidable `ℕ (A' ⇒ B) = no (λ ())
∼-decidable `ℕ (Ref _) = no (λ ())
∼-decidable `ℕ (_ `× _) = no (λ ())
∼-decidable `ℕ `ℕ = yes ∼-ℕ-refl
∼-decidable `ℕ Unit = no (λ ())
∼-decidable `ℕ ⋆ = yes ∼-⋆R
∼-decidable Unit (_ ⇒ _) = no (λ ())
∼-decidable Unit (Ref _) = no (λ ())
∼-decidable Unit (_ `× _) = no (λ ())
∼-decidable Unit `ℕ = no (λ ())
∼-decidable Unit Unit = yes ∼-Unit-refl
∼-decidable Unit ⋆ = yes ∼-⋆R
∼-decidable ⋆ _ = yes ∼-⋆L

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

{- Properties of type precision  -}

⊑-trans : Transitive _⊑_
⊑-trans ⊑-refl prec2 = prec2
⊑-trans ⊑-dyn ⊑-refl = ⊑-dyn
⊑-trans ⊑-dyn ⊑-dyn = ⊑-dyn
⊑-trans (⊑-× prec1 prec3) ⊑-refl = ⊑-× prec1 prec3
⊑-trans (⊑-× prec1 prec3) ⊑-dyn = ⊑-dyn
⊑-trans (⊑-× prec1 prec3) (⊑-× prec2 prec4) =
  ⊑-× (⊑-trans prec1 prec2) (⊑-trans prec3 prec4)
⊑-trans (⊑-⇒ prec1 prec3) ⊑-refl = ⊑-⇒ prec1 prec3
⊑-trans (⊑-⇒ prec1 prec3) ⊑-dyn = ⊑-dyn
⊑-trans (⊑-⇒ prec1 prec3) (⊑-⇒ prec2 prec4) =
  ⊑-⇒ (⊑-trans prec1 prec2) (⊑-trans prec3 prec4)
⊑-trans (⊑-ref prec1) ⊑-refl = ⊑-ref prec1
⊑-trans (⊑-ref prec1) ⊑-dyn = ⊑-dyn
⊑-trans (⊑-ref prec1) (⊑-ref prec2) = ⊑-ref (⊑-trans prec1 prec2)

⋆⊑⋆ : ∀ {A} → ⋆ ⊑ A → A ≡ ⋆
⋆⊑⋆ ⊑-refl = refl
⋆⊑⋆ ⊑-dyn = refl

⊑-antisymmetric : Antisymmetric _≡_ _⊑_
⊑-antisymmetric ⊑-refl _ = refl
⊑-antisymmetric ⊑-dyn x = ⋆⊑⋆ x
⊑-antisymmetric (⊑-× a b) x
  with ⊑-antisymmetric a | ⊑-antisymmetric b
⊑-antisymmetric (⊑-× a b) ⊑-refl | w | q = refl
⊑-antisymmetric (⊑-× a b) (⊑-× a' b') | w | q rewrite w a' | q b' = refl
⊑-antisymmetric (⊑-⇒ a b) x
  with ⊑-antisymmetric a | ⊑-antisymmetric b
⊑-antisymmetric (⊑-⇒ a b) ⊑-refl | w | q = refl
⊑-antisymmetric (⊑-⇒ a b) (⊑-⇒ a' b') | w | q rewrite w a' | q b' = refl
⊑-antisymmetric (⊑-ref a) ⊑-refl = refl
⊑-antisymmetric (⊑-ref a) (⊑-ref x)
  with ⊑-antisymmetric a
... | w rewrite w x = refl

⊑-decidable : Decidable _⊑_
⊑-decidable (A ⇒ B) (A' ⇒ B')
  with ⊑-decidable A A' | ⊑-decidable B B'
... | yes A⊑A' | yes B⊑B' = yes (⊑-⇒ A⊑A' B⊑B')
... | yes A⊑A' | no ¬B⊑B' = no λ { ⊑-refl → ¬B⊑B' ⊑-refl ; (⊑-⇒ _ x) → ¬B⊑B' x}
... | no ¬A⊑A' | q = no (λ { ⊑-refl → ¬A⊑A' ⊑-refl ; (⊑-⇒ x _) → ¬A⊑A' x})
⊑-decidable (_ ⇒ _) (Ref _) = no (λ ())
⊑-decidable (_ ⇒ _) (_ `× _) = no (λ ())
⊑-decidable (_ ⇒ _) `ℕ = no (λ ())
⊑-decidable (_ ⇒ _) Unit = no (λ ())
⊑-decidable (_ ⇒ _) ⋆ = yes ⊑-dyn
⊑-decidable (Ref _) (_ ⇒ _) = no (λ ())
⊑-decidable (Ref A) (Ref B)
  with ⊑-decidable A B
... | yes A⊑B = yes (⊑-ref A⊑B)
... | no ¬A⊑A' = no (λ { ⊑-refl → ¬A⊑A' ⊑-refl ; (⊑-ref x) → ¬A⊑A' x})
⊑-decidable (Ref _) (_ `× _) = no (λ ())
⊑-decidable (Ref _) `ℕ = no (λ ())
⊑-decidable (Ref _) Unit = no (λ ())
⊑-decidable (Ref _) ⋆ = yes ⊑-dyn
⊑-decidable (A `× B) (A' `× B')
  with ⊑-decidable A A' | ⊑-decidable B B'
... | yes A⊑A' | yes B⊑B' = yes (⊑-× A⊑A' B⊑B')
... | yes A⊑A' | no ¬B⊑B' = no λ { ⊑-refl → ¬B⊑B' ⊑-refl ; (⊑-× _ x) → ¬B⊑B' x}
... | no ¬A⊑A' | q = no (λ { ⊑-refl → ¬A⊑A' ⊑-refl ; (⊑-× x _) → ¬A⊑A' x})
⊑-decidable (_ `× _) (Ref _) = no (λ ())
⊑-decidable (_ `× _) (_ ⇒ _) = no (λ ())
⊑-decidable (_ `× _) `ℕ = no (λ ())
⊑-decidable (_ `× _) Unit = no (λ ())
⊑-decidable (_ `× _) ⋆ = yes ⊑-dyn
⊑-decidable `ℕ (_ ⇒ _) = no (λ ())
⊑-decidable `ℕ (Ref _) = no (λ ())
⊑-decidable `ℕ (_ `× _) = no (λ ())
⊑-decidable `ℕ `ℕ = yes ⊑-refl
⊑-decidable `ℕ Unit = no (λ ())
⊑-decidable `ℕ ⋆ = yes ⊑-dyn
⊑-decidable Unit (_ ⇒ _) = no (λ ())
⊑-decidable Unit (Ref _) = no (λ ())
⊑-decidable Unit (_ `× _) = no (λ ())
⊑-decidable Unit `ℕ = no (λ ())
⊑-decidable Unit Unit = yes ⊑-refl
⊑-decidable Unit ⋆ = yes ⊑-dyn
⊑-decidable ⋆ (_ ⇒ _) = no (λ ())
⊑-decidable ⋆ (Ref _) = no (λ ())
⊑-decidable ⋆ (_ `× _) = no (λ ())
⊑-decidable ⋆ `ℕ = no (λ ())
⊑-decidable ⋆ Unit = no (λ ())
⊑-decidable ⋆ ⋆ = yes ⊑-refl

⊑-respect-static : ∀ {t t'} → t' ⊑ t → static t → t' ≡ t
⊑-respect-static ⊑-refl st = refl
⊑-respect-static ⊑-dyn ()
⊑-respect-static (⊑-× prec₁ prec₂) (static-× st₁ st₂)
  with ⊑-respect-static prec₁ st₁ | ⊑-respect-static prec₂ st₂
... | refl | refl = refl
⊑-respect-static (⊑-⇒ prec₁ prec₂) (static-⇒ st₁ st₂)
  with ⊑-respect-static prec₁ st₁ | ⊑-respect-static prec₂ st₂
... | refl | refl = refl
⊑-respect-static (⊑-ref prec) (static-ref st) with ⊑-respect-static prec st
... | refl = refl

⊑⇒∼ : ∀ {A B} → A ⊑ B → A ∼ B
⊑⇒∼ ⊑-refl = ∼-refl
⊑⇒∼ ⊑-dyn = ∼-⋆R
⊑⇒∼ (⊑-× x y) = ~-× (⊑⇒∼ x) (⊑⇒∼ y)
⊑⇒∼ (⊑-⇒ x y) = ~-⇒ (⊑⇒∼ x) (⊑⇒∼ y)
⊑⇒∼ (⊑-ref x) = ~-ref (⊑⇒∼ x)

{- greatest lower bound function -}

⊓ : ∀ {T₁ T₂} → T₁ ∼ T₂ → Type
⊓ ∼-ℕ-refl = `ℕ
⊓ ∼-Unit-refl = Unit
⊓ {T₁} ∼-⋆R = T₁
⊓ {T₂ = T₂} ∼-⋆L = T₂
⊓ (~-× x y) = (⊓ x) `× (⊓ y)
⊓ (~-⇒ x y) = (⊓ x) ⇒ (⊓ y)
⊓ (~-ref x) = Ref (⊓ x)

⊓⟹⊑ᵣ : ∀ {T₁ T₂} → (T₁∼T₂ : T₁ ∼ T₂) → ⊓ T₁∼T₂ ⊑ T₂
⊓⟹⊑ᵣ ∼-ℕ-refl = ⊑-refl
⊓⟹⊑ᵣ ∼-Unit-refl = ⊑-refl
⊓⟹⊑ᵣ ∼-⋆R = ⊑-dyn
⊓⟹⊑ᵣ ∼-⋆L = ⊑-refl
⊓⟹⊑ᵣ (~-× x x₁) = ⊑-× (⊓⟹⊑ᵣ x) (⊓⟹⊑ᵣ x₁)
⊓⟹⊑ᵣ (~-⇒ x x₁) = ⊑-⇒ (⊓⟹⊑ᵣ x) (⊓⟹⊑ᵣ x₁)
⊓⟹⊑ᵣ (~-ref x) = ⊑-ref (⊓⟹⊑ᵣ x)

⊓⟹⊑ᵣ-with-≡ : ∀ {T T₁ T₂} → (T₁∼T₂ : T₁ ∼ T₂) → ⊓ T₁∼T₂ ≡ T → T ⊑ T₂
⊓⟹⊑ᵣ-with-≡ T₁∼T₂ refl = ⊓⟹⊑ᵣ T₁∼T₂

⊓⟹⊑ₗ : ∀ {T₁ T₂} → (T₁∼T₂ : T₁ ∼ T₂) → ⊓ T₁∼T₂ ⊑ T₁
⊓⟹⊑ₗ ∼-ℕ-refl = ⊑-refl
⊓⟹⊑ₗ ∼-Unit-refl = ⊑-refl
⊓⟹⊑ₗ ∼-⋆R = ⊑-refl
⊓⟹⊑ₗ ∼-⋆L = ⊑-dyn
⊓⟹⊑ₗ (~-× x x₁) = ⊑-× (⊓⟹⊑ₗ x) (⊓⟹⊑ₗ x₁)
⊓⟹⊑ₗ (~-⇒ x x₁) = ⊑-⇒ (⊓⟹⊑ₗ x) (⊓⟹⊑ₗ x₁)
⊓⟹⊑ₗ (~-ref x) = ⊑-ref (⊓⟹⊑ₗ x)

¬⌣⇒≢⋆R : ∀ {A B} → ¬ (A ⌣ B) → B ≢ ⋆
¬⌣⇒≢⋆R ¬p refl = ¬p ⌣-⋆R

∼⇒⌣ : ∀ {A B} → A ∼ B → A ⌣ B
∼⇒⌣ ∼-ℕ-refl = ⌣-ℕ-refl
∼⇒⌣ ∼-Unit-refl = ⌣-Unit-refl
∼⇒⌣ ∼-⋆R = ⌣-⋆R
∼⇒⌣ ∼-⋆L = ⌣-⋆L
∼⇒⌣ (~-⇒ _ _) = ⌣-⇒
∼⇒⌣ (~-× _ _) = ⌣-×
∼⇒⌣ (~-ref _) = ⌣-ref

¬⌣⇒¬∼ : ∀ {A B} → ¬ (A ⌣ B) → ¬ A ∼ B
¬⌣⇒¬∼ ¬p x = ¬p (∼⇒⌣ x)
