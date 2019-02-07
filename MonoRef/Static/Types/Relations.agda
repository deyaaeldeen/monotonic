module MonoRef.Static.Types.Relations where

open import Data.Product
  using (_×_)
open import Data.Sum
  using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; cong₂ ; sym)
open import Relation.Binary
  using (Reflexive ; Transitive)
open import Relation.Nullary using
  (Dec ; yes ; no ; ¬_)

open import MonoRef.Static.Types


infix  4 _⊑_
infix  4 static_
infix  4 _∼_

data _⊑_ : Type → Type → Set where
  ⊑-refl : ∀ {A} → A ⊑ A
  ⊑-dyn : ∀ {A} → A ⊑ ⋆
  ⊑-× : ∀ {A B C D} → A ⊑ B → C ⊑ D → A `× C ⊑ B `× D
  ⊑-⇒ : ∀ {A B C D} → A ⊑ B → C ⊑ D → A ⇒ C ⊑ B ⇒ D
  ⊑-ref : ∀ {A B} → A ⊑ B → Ref A ⊑ Ref B

data static_ : Type → Set where
  static-ℕ : static `ℕ
  static-unit : static Unit
  static-⇒ : ∀ {A B} → static A → static B → static A ⇒ B
  static-ref : ∀ {A} → static A → static Ref A
  static-× : ∀ {A B} → static A → static B → static A `× B

data _∼_ : Type → Type → Set where
  ∼-ℕ-refl : `ℕ ∼ `ℕ
  ∼-Unit-refl : Unit ∼ Unit
  ∼-ld : ∀ {A} → A ∼ ⋆
  ∼-rd : ∀ {A} → ⋆ ∼ A
  ~-× : ∀ {A B C D} → A ∼ B → C ∼ D → A `× C ∼ B `× D
  ~-⇒ : ∀ {A B C D} → A ∼ B → C ∼ D → A ⇒ C ∼ B ⇒ D
  ~-ref : ∀ {A B} → A ∼ B → Ref A ∼ Ref B

∼-refl : Reflexive _∼_
∼-refl {x ⇒ x₁} = ~-⇒ ∼-refl ∼-refl
∼-refl {Ref x} = ~-ref ∼-refl
∼-refl {x `× x₁} = ~-× ∼-refl ∼-refl
∼-refl {`ℕ} = ∼-ℕ-refl
∼-refl {Unit} = ∼-Unit-refl
∼-refl {⋆} = ∼-ld

¬∼×ₗ : ∀ {T₁ T₂ T₃ T₄} → ¬ T₁ ∼ T₂ → ¬ (_`×_ T₁ T₃) ∼ (_`×_ T₂ T₄)
¬∼×ₗ ¬T₁∼T₂ (~-× x _) = ¬T₁∼T₂ x

¬∼×ᵣ : ∀ {T₁ T₂ T₃ T₄} → ¬ T₃ ∼ T₄ → ¬ (_`×_ T₁ T₃) ∼ (_`×_ T₂ T₄)
¬∼×ᵣ ¬T₃∼T₄ (~-× _ x) = ¬T₃∼T₄ x

¬∼⇒ᵢ : ∀ {T₁ T₂ T₃ T₄} → ¬ T₁ ∼ T₂ → ¬ (_⇒_ T₁ T₃) ∼ (_⇒_ T₂ T₄)
¬∼⇒ᵢ ¬T₁∼T₂ (~-⇒ x _) = ¬T₁∼T₂ x

¬∼⇒ₒ : ∀ {T₁ T₂ T₃ T₄} → ¬ T₃ ∼ T₄ → ¬ (_⇒_ T₁ T₃) ∼ (_⇒_ T₂ T₄)
¬∼⇒ₒ ¬T₃∼T₄ (~-⇒ _ x) = ¬T₃∼T₄ x

¬∼Ref : ∀ {T₁ T₂} → ¬ T₁ ∼ T₂ → ¬ (Ref T₁) ∼ (Ref T₂)
¬∼Ref ¬T₁∼T₂ (~-ref x) = ¬T₁∼T₂ x

⊑-Ref-injective : ∀ {A B : Type} → Ref A ⊑ Ref B → A ⊑ B
⊑-Ref-injective ⊑-refl = ⊑-refl
⊑-Ref-injective (⊑-ref x) = x

⊑-⇒-injectiveₗ : ∀ {A B C D : Type} → A ⇒ C ⊑ B ⇒ D → A ⊑ B
⊑-⇒-injectiveₗ ⊑-refl = ⊑-refl
⊑-⇒-injectiveₗ (⊑-⇒ x _) = x

⊑-⇒-injectiveᵣ : ∀ {A B C D : Type} → A ⇒ C ⊑ B ⇒ D → C ⊑ D
⊑-⇒-injectiveᵣ ⊑-refl = ⊑-refl
⊑-⇒-injectiveᵣ (⊑-⇒ _ x) = x

⊑-×-injectiveₗ : ∀ {A B C D : Type} → A `× C ⊑ B `× D → A ⊑ B
⊑-×-injectiveₗ ⊑-refl = ⊑-refl
⊑-×-injectiveₗ (⊑-× x _) = x

⊑-×-injectiveᵣ : ∀ {A B C D : Type} → A `× C ⊑ B `× D → C ⊑ D
⊑-×-injectiveᵣ ⊑-refl = ⊑-refl
⊑-×-injectiveᵣ (⊑-× _ x) = x

∼⊑P : ∀ {T₁ T₂} → T₁ ∼ T₂ → Dec (T₂ ⊑ T₁)
∼⊑P ∼-ℕ-refl = yes ⊑-refl
∼⊑P ∼-Unit-refl = yes ⊑-refl
∼⊑P {T₁ ⇒ T₂} ∼-ld = no (λ ())
∼⊑P {Ref T₁} ∼-ld = no (λ ())
∼⊑P {T₁ `× T₂} ∼-ld = no (λ ())
∼⊑P {`ℕ} ∼-ld = no (λ ())
∼⊑P {Unit} ∼-ld = no (λ ())
∼⊑P {⋆} ∼-ld = yes ⊑-refl
∼⊑P ∼-rd = yes ⊑-dyn
∼⊑P (~-× x y) with ∼⊑P x | ∼⊑P y
∼⊑P (~-× x y) | yes p | yes p₁ = yes (⊑-× p p₁)
∼⊑P (~-× x y) | yes p | no ¬p = no λ k → ¬p (⊑-×-injectiveᵣ k)
∼⊑P (~-× x y) | no ¬p | yes p = no λ k → ¬p (⊑-×-injectiveₗ k)
∼⊑P (~-× x y) | no ¬p | no ¬p₁ = no λ k → ¬p (⊑-×-injectiveₗ k)
∼⊑P (~-⇒ x y) with ∼⊑P x | ∼⊑P y
∼⊑P (~-⇒ x y) | yes p | yes p₁ = yes (⊑-⇒ p p₁)
∼⊑P (~-⇒ x y) | yes p | no ¬p = no λ k → ¬p (⊑-⇒-injectiveᵣ k)
∼⊑P (~-⇒ x y) | no ¬p | yes p = no λ k → ¬p (⊑-⇒-injectiveₗ k)
∼⊑P (~-⇒ x y) | no ¬p | no ¬p₁ = no λ k → ¬p (⊑-⇒-injectiveₗ k)
∼⊑P (~-ref x) with ∼⊑P x
∼⊑P (~-ref x) | yes p = yes (⊑-ref p)
∼⊑P (~-ref x) | no ¬p = no λ k → ¬p (⊑-Ref-injective k)

∼≡P : ∀ {T₁ T₂} → T₁ ∼ T₂ → Dec (T₁ ≡ T₂)
∼≡P ∼-ℕ-refl = yes refl
∼≡P ∼-Unit-refl = yes refl
∼≡P {T₁ ⇒ T₂} ∼-ld = no (λ ())
∼≡P {Ref T₁} ∼-ld = no (λ ())
∼≡P {T₁ `× T₂} ∼-ld = no (λ ())
∼≡P {`ℕ} ∼-ld = no (λ ())
∼≡P {Unit} ∼-ld = no (λ ())
∼≡P {⋆} ∼-ld = yes refl
∼≡P {T₂ = T₂ ⇒ T₃} ∼-rd = no (λ ())
∼≡P {T₂ = Ref T₂} ∼-rd = no (λ ())
∼≡P {T₂ = T₂ `× T₃} ∼-rd = no (λ ())
∼≡P {T₂ = `ℕ} ∼-rd = no (λ ())
∼≡P {T₂ = Unit} ∼-rd = no (λ ())
∼≡P {T₂ = ⋆} ∼-rd = yes refl
∼≡P (~-× x y) with ∼≡P x | ∼≡P y
∼≡P (~-× x y) | yes p | yes p₁ = yes (cong₂ _`×_ p p₁)
∼≡P (~-× x y) | yes refl | no ¬p = no λ {refl → ¬p refl}
∼≡P (~-× x y) | no ¬p | yes p = no λ {refl → ¬p refl}
∼≡P (~-× x y) | no ¬p | no ¬p₁ = no λ {refl → ¬p refl}
∼≡P (~-⇒ x y) with ∼≡P x | ∼≡P y
∼≡P (~-⇒ x y) | yes p | yes p₁ = yes (cong₂ _⇒_ p p₁)
∼≡P (~-⇒ x y) | yes p | no ¬p = no λ {refl → ¬p refl}
∼≡P (~-⇒ x y) | no ¬p | yes p = no λ {refl → ¬p refl}
∼≡P (~-⇒ x y) | no ¬p | no ¬p₁ = no λ {refl → ¬p refl}
∼≡P (~-ref x) with ∼≡P x
∼≡P (~-ref x) | yes refl = yes refl
∼≡P (~-ref x) | no ¬p = no λ {refl → ¬p refl}

-- greatest lower bound
⊓ : ∀ {T₁ T₂} → T₁ ∼ T₂ → Type
⊓ ∼-ℕ-refl = `ℕ
⊓ ∼-Unit-refl = Unit
⊓ {T₁} ∼-ld = T₁
⊓ {T₂ = T₂} ∼-rd = T₂
⊓ (~-× x y) = (⊓ x) `× (⊓ y)
⊓ (~-⇒ x y) = (⊓ x) ⇒ (⊓ y)
⊓ (~-ref x) = Ref (⊓ x)

⊓⟹⊑ᵣ : ∀ {T₁ T₂} → (T₁∼T₂ : T₁ ∼ T₂) → ⊓ T₁∼T₂ ⊑ T₂
⊓⟹⊑ᵣ ∼-ℕ-refl = ⊑-refl
⊓⟹⊑ᵣ ∼-Unit-refl = ⊑-refl
⊓⟹⊑ᵣ ∼-ld = ⊑-dyn
⊓⟹⊑ᵣ ∼-rd = ⊑-refl
⊓⟹⊑ᵣ (~-× x x₁) = ⊑-× (⊓⟹⊑ᵣ x) (⊓⟹⊑ᵣ x₁)
⊓⟹⊑ᵣ (~-⇒ x x₁) = ⊑-⇒ (⊓⟹⊑ᵣ x) (⊓⟹⊑ᵣ x₁)
⊓⟹⊑ᵣ (~-ref x) = ⊑-ref (⊓⟹⊑ᵣ x)

⊓⟹⊑ᵣ-with-≡ : ∀ {T T₁ T₂} → (T₁∼T₂ : T₁ ∼ T₂) → ⊓ T₁∼T₂ ≡ T → T ⊑ T₂
⊓⟹⊑ᵣ-with-≡ T₁∼T₂ refl = ⊓⟹⊑ᵣ T₁∼T₂

≡⟹∼ : ∀ {T₁ T₂} → T₁ ≡ T₂ → T₁ ∼ T₂
≡⟹∼ {T₁} {T₂} refl = ∼-refl

≡⟹⊓∼ : ∀ {A B} → (eq : A ≡ B) → ⊓ (≡⟹∼ eq) ≡ A
≡⟹⊓∼ eq with ≡⟹∼ eq
... | consis rewrite eq = helper consis
  where
    helper : ∀ {A} → (eq : A ∼ A) → ⊓ eq ≡ A
    helper ∼-ℕ-refl = refl
    helper ∼-Unit-refl = refl
    helper ∼-ld = refl
    helper ∼-rd = refl
    helper (~-× x y) with helper x
    ... | l rewrite l with helper y
    ... | r rewrite r = refl
    helper (~-⇒ x y) with helper x
    ... | l rewrite l with helper y
    ... | r rewrite r = refl
    helper (~-ref x) with helper x
    ... | w rewrite w = refl

postulate
  ¬⊑⟹⊑' : ∀ {A B} → (c : A ∼ B) → ¬ B ⊑ A → A ⊑ B
  -- ¬ (⋆ ⇒ Int) ⊑ (Int ⇒ Int)
  -- ¬⊑-⇒-injective : ∀ {A B C D : Type} → ¬ ((A ⇒ C) ⊑ (B ⇒ D)) → ((¬ A ⊑ B) × (¬ C ⊑ D)) ⊎ ((¬ A ⊑ B) × (C ⊑ D)) ⊎ ((B ⊑ A) × (¬ C ⊑ D))

-- ¬⊑⟹⊑' : ∀ {A B} → (c : A ∼ B) → ¬ B ⊑ A → A ⊑ B
-- ¬⊑⟹⊑' ∼-ℕ-refl x = ⊑-refl
-- ¬⊑⟹⊑' ∼-Unit-refl x = ⊑-refl
-- ¬⊑⟹⊑' ∼-ld x = ⊑-dyn
-- ¬⊑⟹⊑' ∼-rd x with x ⊑-dyn
-- ... | ()
-- ¬⊑⟹⊑' (~-× c c₁) x = {!!}
-- ¬⊑⟹⊑' (~-⇒ c c₁) x with ¬⊑-⇒-injective x
-- ¬⊑⟹⊑' (~-⇒ c c₁) x | inj₁ (fst , snd) = ⊑-⇒ (¬⊑⟹⊑' c fst) (¬⊑⟹⊑' c₁ snd)
-- ¬⊑⟹⊑' (~-⇒ c c₁) x | inj₂ (inj₁ (fst , ⊑-refl)) = ⊑-⇒ (¬⊑⟹⊑' c fst) ⊑-refl
-- ¬⊑⟹⊑' (~-⇒ c c₁) x | inj₂ (inj₁ (fst , ⊑-dyn)) = {!!}
-- ¬⊑⟹⊑' (~-⇒ c c₁) x | inj₂ (inj₁ (fst , ⊑-× snd snd₁)) = ⊑-⇒ (¬⊑⟹⊑' c fst) {!!}
-- ¬⊑⟹⊑' (~-⇒ c c₁) x | inj₂ (inj₁ (fst , ⊑-⇒ snd snd₁)) = ⊑-⇒ (¬⊑⟹⊑' c fst) {!!}
-- ¬⊑⟹⊑' (~-⇒ c c₁) x | inj₂ (inj₁ (fst , ⊑-ref snd)) = ⊑-⇒ (¬⊑⟹⊑' c fst) {!!}
-- ¬⊑⟹⊑' (~-⇒ c c₁) x | inj₂ (inj₂ y) = {!!}
-- ¬⊑⟹⊑' (~-ref c) x = ⊑-ref (¬⊑⟹⊑' c (λ z → x (⊑-ref z)))

⊑⟹⊓≡ : ∀ {A B} → (c : A ∼ B) → A ⊑ B → ⊓ c ≡ A
⊑⟹⊓≡ ∼-ℕ-refl y = refl
⊑⟹⊓≡ ∼-Unit-refl y = refl
⊑⟹⊓≡ ∼-ld y = refl
⊑⟹⊓≡ ∼-rd ⊑-refl = refl
⊑⟹⊓≡ ∼-rd ⊑-dyn = refl
⊑⟹⊓≡ (~-× x x₁) ⊑-refl with ⊑⟹⊓≡ x ⊑-refl
... | l rewrite l with ⊑⟹⊓≡ x₁ ⊑-refl
... | r rewrite r = refl
⊑⟹⊓≡ (~-× x x₁) (⊑-× y y₁) with ⊑⟹⊓≡ x y 
... | l rewrite l with ⊑⟹⊓≡ x₁ y₁
... | r rewrite r = refl
⊑⟹⊓≡ (~-⇒ x x₁) ⊑-refl with ⊑⟹⊓≡ x ⊑-refl
... | l rewrite l with ⊑⟹⊓≡ x₁ ⊑-refl
... | r rewrite r = refl
⊑⟹⊓≡ (~-⇒ x x₁) (⊑-⇒ y y₁) with ⊑⟹⊓≡ x y 
... | l rewrite l with ⊑⟹⊓≡ x₁ y₁
... | r rewrite r = refl
⊑⟹⊓≡ (~-ref x) ⊑-refl with ⊑⟹⊓≡ x ⊑-refl
... | w rewrite w = refl
⊑⟹⊓≡ (~-ref x) (⊑-ref y) with ⊑⟹⊓≡ x y
... | w rewrite w = refl

¬⊑⟹⊓≡ : ∀ {A B} → (c : A ∼ B) → ¬ B ⊑ A → ⊓ c ≡ A
¬⊑⟹⊓≡ x y with ¬⊑⟹⊑' x y
... | w = ⊑⟹⊓≡ x w

≡-Ref-injective : ∀ {A B : Type} → (_≡_ {A = Type} (Ref A) (Ref B)) → A ≡ B
≡-Ref-injective refl = refl

≡-⇒-injectiveₗ : ∀ {A B C D : Type} → (_≡_ {A = Type} (A ⇒ C) (B ⇒ D)) → A ≡ B
≡-⇒-injectiveₗ refl = refl

≡-⇒-injectiveᵣ : ∀ {A B C D : Type} → (_≡_ {A = Type} (A ⇒ C) (B ⇒ D)) → C ≡ D
≡-⇒-injectiveᵣ refl = refl

-- TODO: prove these
postulate
  ¬≡-⇒-injective : ∀ {A B C D : Type} → ¬ (_≡_ {A = Type} (A ⇒ C) (B ⇒ D)) → (¬ A ≡ B) ⊎ (¬ C ≡ D)
  ¬≡-×-injective : ∀ {A B C D : Type} → ¬ (_≡_ {A = Type} (A `× C) (B `× D)) → (¬ A ≡ B) ⊎ (¬ C ≡ D)

≡-×-injectiveₗ : ∀ {A B C D : Type} → (_≡_ {A = Type} (A `× C) (B `× D)) → A ≡ B
≡-×-injectiveₗ refl = refl

≡-×-injectiveᵣ : ∀ {A B C D : Type} → (_≡_ {A = Type} (A `× C) (B `× D)) → C ≡ D
≡-×-injectiveᵣ refl = refl

¬≡⟹¬⊓∼ : ∀ {A B} → ¬ A ≡ B → B ⊑ A → (c : A ∼ B) → ¬ ⊓ c ≡ A
¬≡⟹¬⊓∼ x prec ∼-ℕ-refl w = x refl
¬≡⟹¬⊓∼ x prec ∼-Unit-refl w = x refl
¬≡⟹¬⊓∼ x ⊑-refl ∼-ld w = x refl
¬≡⟹¬⊓∼ x ⊑-dyn ∼-ld w = x refl
¬≡⟹¬⊓∼ x prec ∼-rd w = x (sym w)
¬≡⟹¬⊓∼ x prec (~-× c c₁) w with ¬≡-×-injective x
¬≡⟹¬⊓∼ x prec (~-× c c₁) w | inj₁ x₁ with ¬≡⟹¬⊓∼ x₁ (⊑-×-injectiveₗ prec) c
...| l = l (≡-×-injectiveₗ w)
¬≡⟹¬⊓∼ x prec (~-× c c₁) w | inj₂ y with ¬≡⟹¬⊓∼ y (⊑-×-injectiveᵣ prec) c₁
... | r = r (≡-×-injectiveᵣ w)
¬≡⟹¬⊓∼ x prec (~-⇒ c c₁) w with ¬≡-⇒-injective x
¬≡⟹¬⊓∼ x prec (~-⇒ c c₁) w | inj₁ x₁ with ¬≡⟹¬⊓∼ x₁ (⊑-⇒-injectiveₗ prec) c
... | l = l (≡-⇒-injectiveₗ w)
¬≡⟹¬⊓∼ x prec (~-⇒ c c₁) w | inj₂ y with ¬≡⟹¬⊓∼ y (⊑-⇒-injectiveᵣ prec) c₁
... | r = r (≡-⇒-injectiveᵣ w)
¬≡⟹¬⊓∼ x prec (~-ref c) w with ¬≡⟹¬⊓∼ (λ{ refl → x refl}) (⊑-Ref-injective prec) c
... | g = g (≡-Ref-injective w)

⊓⟹⊑ₗ : ∀ {T₁ T₂} → (T₁∼T₂ : T₁ ∼ T₂) → ⊓ T₁∼T₂ ⊑ T₁
⊓⟹⊑ₗ ∼-ℕ-refl = ⊑-refl
⊓⟹⊑ₗ ∼-Unit-refl = ⊑-refl
⊓⟹⊑ₗ ∼-ld = ⊑-refl
⊓⟹⊑ₗ ∼-rd = ⊑-dyn
⊓⟹⊑ₗ (~-× x x₁) = ⊑-× (⊓⟹⊑ₗ x) (⊓⟹⊑ₗ x₁)
⊓⟹⊑ₗ (~-⇒ x x₁) = ⊑-⇒ (⊓⟹⊑ₗ x) (⊓⟹⊑ₗ x₁)
⊓⟹⊑ₗ (~-ref x) = ⊑-ref (⊓⟹⊑ₗ x)

∼P : (T₁ : Type) → (T₂ : Type) → Dec (T₁ ∼ T₂)
∼P (t₁ ⇒ t₃) (t₂ ⇒ t₄) with ∼P t₁ t₂ | ∼P t₃ t₄
∼P (t₁ ⇒ t₃) (t₂ ⇒ t₄) | yes p | yes p₁ = yes (~-⇒ p p₁)
∼P (t₁ ⇒ t₃) (t₂ ⇒ t₄) | yes p | no ¬p = no (¬∼⇒ₒ ¬p)
∼P (t₁ ⇒ t₃) (t₂ ⇒ t₄) | no ¬p | yes p = no (¬∼⇒ᵢ ¬p)
∼P (t₁ ⇒ t₃) (t₂ ⇒ t₄) | no ¬p | no ¬p₁ = no (¬∼⇒ᵢ ¬p)
∼P (t₁ ⇒ t₃) (Ref t₂) = no (λ ())
∼P (t₁ ⇒ t₃) (t₂ `× t₄) = no (λ ())
∼P (t₁ ⇒ t₃) `ℕ = no (λ ())
∼P (t₁ ⇒ t₃) Unit = no (λ ())
∼P (t₁ ⇒ t₃) ⋆ = yes ∼-ld
∼P (Ref t₁) (t₂ ⇒ t₃) = no (λ ())
∼P (Ref t₁) (Ref t₂) with ∼P t₁ t₂
∼P (Ref t₁) (Ref t₂) | yes p = yes (~-ref p)
∼P (Ref t₁) (Ref t₂) | no ¬p = no (¬∼Ref ¬p)
∼P (Ref t₁) (t₂ `× t₃) = no (λ ())
∼P (Ref t₁) `ℕ = no (λ ())
∼P (Ref t₁) Unit = no (λ ())
∼P (Ref t₁) ⋆ = yes ∼-ld
∼P (t₁ `× t₃) (t₂ ⇒ t₄) = no (λ ())
∼P (t₁ `× t₃) (Ref t₂) = no (λ ())
∼P (t₁ `× t₃) (t₂ `× t₄) with ∼P t₁ t₂ | ∼P t₃ t₄
∼P (t₁ `× t₃) (t₂ `× t₄) | yes p | yes p₁ = yes (~-× p p₁)
∼P (t₁ `× t₃) (t₂ `× t₄) | yes p | no ¬p = no (¬∼×ᵣ ¬p)
∼P (t₁ `× t₃) (t₂ `× t₄) | no ¬p | yes p = no (¬∼×ₗ ¬p)
∼P (t₁ `× t₃) (t₂ `× t₄) | no ¬p | no ¬p₁ = no (¬∼×ₗ ¬p)
∼P (t₁ `× t₃) `ℕ = no (λ ())
∼P (t₁ `× t₃) Unit = no (λ ())
∼P (t₁ `× t₃) ⋆ = yes ∼-ld
∼P `ℕ (t₂ ⇒ t₃) = no (λ ())
∼P `ℕ (Ref t₂) = no (λ ())
∼P `ℕ (t₂ `× t₃) = no (λ ())
∼P `ℕ `ℕ = yes ∼-ℕ-refl
∼P `ℕ Unit = no (λ ())
∼P `ℕ ⋆ = yes ∼-ld
∼P Unit (t₂ ⇒ t₃) = no (λ ())
∼P Unit (Ref t₂) = no (λ ())
∼P Unit (t₂ `× t₃) = no (λ ())
∼P Unit `ℕ = no (λ ())
∼P Unit Unit = yes ∼-Unit-refl
∼P Unit ⋆ = yes ∼-ld
∼P ⋆ t₂ = yes ∼-rd

⊑-trans : Transitive _⊑_
⊑-trans ⊑-refl prec2 = prec2
⊑-trans ⊑-dyn ⊑-refl = ⊑-dyn
⊑-trans ⊑-dyn ⊑-dyn = ⊑-dyn
⊑-trans (⊑-× prec1 prec3) ⊑-refl = ⊑-× prec1 prec3
⊑-trans (⊑-× prec1 prec3) ⊑-dyn = ⊑-dyn
⊑-trans (⊑-× prec1 prec3) (⊑-× prec2 prec4) = ⊑-× (⊑-trans prec1 prec2) (⊑-trans prec3 prec4)
⊑-trans (⊑-⇒ prec1 prec3) ⊑-refl = ⊑-⇒ prec1 prec3
⊑-trans (⊑-⇒ prec1 prec3) ⊑-dyn = ⊑-dyn
⊑-trans (⊑-⇒ prec1 prec3) (⊑-⇒ prec2 prec4) = ⊑-⇒ (⊑-trans prec1 prec2) (⊑-trans prec3 prec4)
⊑-trans (⊑-ref prec1) ⊑-refl = ⊑-ref prec1
⊑-trans (⊑-ref prec1) ⊑-dyn = ⊑-dyn
⊑-trans (⊑-ref prec1) (⊑-ref prec2) = ⊑-ref (⊑-trans prec1 prec2)

⊑-respect-static : ∀ {t t'} → t' ⊑ t → static t → t' ≡ t
⊑-respect-static ⊑-refl st = refl
⊑-respect-static ⊑-dyn ()
⊑-respect-static (⊑-× prec₁ prec₂) (static-× st₁ st₂) with ⊑-respect-static prec₁ st₁ | ⊑-respect-static prec₂ st₂
... | refl | refl = refl
⊑-respect-static (⊑-⇒ prec₁ prec₂) (static-⇒ st₁ st₂) with ⊑-respect-static prec₁ st₁ | ⊑-respect-static prec₂ st₂
... | refl | refl = refl
⊑-respect-static (⊑-ref prec) (static-ref st) with ⊑-respect-static prec st
... | refl = refl
