module MonoRef.Static.Types.Relations.Meet where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Binary using (Antisymmetric ; Decidable ; Reflexive ; Transitive)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)

open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations.Unary
open import MonoRef.Static.Types.Relations.Consistency
open import MonoRef.Static.Types.Relations.TypePreciseness


{- greatest lower bound function -}

⊓ : ∀ {T₁ T₂} → T₁ ∼ T₂ → Type
⊓ ∼-ℕ-refl = `ℕ
⊓ ∼-Unit-refl = Unit
⊓ ∼-⋆-refl = ⋆
⊓ {T₁} (∼-⋆R _) = T₁
⊓ {T₂ = T₂} (∼-⋆L _) = T₂
⊓ (~-× x y) = (⊓ x) `× (⊓ y)
⊓ (~-⇒ x y) = (⊓ x) ⇒ (⊓ y)
⊓ (~-ref x) = Ref (⊓ x)

⊓⟹⊑ᵣ : ∀ {T₁ T₂} → (T₁∼T₂ : T₁ ∼ T₂) → ⊓ T₁∼T₂ ⊑ T₂
⊓⟹⊑ᵣ ∼-ℕ-refl = ⊑-refl B-`ℕ
⊓⟹⊑ᵣ ∼-Unit-refl = ⊑-refl B-Unit
⊓⟹⊑ᵣ ∼-⋆-refl = ⊑-dyn
⊓⟹⊑ᵣ (∼-⋆R _) = ⊑-dyn
⊓⟹⊑ᵣ {T₂ = A} (∼-⋆L _) = A⊑A A
⊓⟹⊑ᵣ (~-× x x₁) = ⊑-× (⊓⟹⊑ᵣ x) (⊓⟹⊑ᵣ x₁)
⊓⟹⊑ᵣ (~-⇒ x x₁) = ⊑-⇒ (⊓⟹⊑ᵣ x) (⊓⟹⊑ᵣ x₁)
⊓⟹⊑ᵣ (~-ref x) = ⊑-ref (⊓⟹⊑ᵣ x)

⊓⋆T≡T : ∀ {A} → (⋆∼A : ⋆ ∼ A) → ⊓ ⋆∼A ≡ A
⊓⋆T≡T ∼-⋆-refl = refl
⊓⋆T≡T (∼-⋆R x) = refl
⊓⋆T≡T (∼-⋆L x) = refl

B⊑A⇒⊓AB≡B : ∀ {A B} → (A∼B : A ∼ B) → B ⊑ A → ⊓ A∼B ≡ B
B⊑A⇒⊓AB≡B A∼B ⊑-dyn = ⊓⋆T≡T A∼B
B⊑A⇒⊓AB≡B (~-× A∼B A∼B₁) (⊑-× B⊑A B⊑A₁) rewrite B⊑A⇒⊓AB≡B A∼B B⊑A | B⊑A⇒⊓AB≡B A∼B₁ B⊑A₁ = refl
B⊑A⇒⊓AB≡B (~-⇒ A∼B A∼B₁) (⊑-⇒ B⊑A B⊑A₁) rewrite B⊑A⇒⊓AB≡B A∼B B⊑A | B⊑A⇒⊓AB≡B A∼B₁ B⊑A₁ = refl
B⊑A⇒⊓AB≡B (~-ref A∼B) (⊑-ref B⊑A) rewrite B⊑A⇒⊓AB≡B A∼B B⊑A = refl
B⊑A⇒⊓AB≡B ∼-ℕ-refl (⊑-refl x) = refl
B⊑A⇒⊓AB≡B ∼-Unit-refl (⊑-refl x) = refl
B⊑A⇒⊓AB≡B ∼-⋆-refl (⊑-refl x) = refl
B⊑A⇒⊓AB≡B (∼-⋆R ()) (⊑-refl x)
B⊑A⇒⊓AB≡B (∼-⋆L ()) (⊑-refl x)
B⊑A⇒⊓AB≡B (~-⇒ A∼B A∼B₁) (⊑-refl ())
B⊑A⇒⊓AB≡B (~-× A∼B A∼B₁) (⊑-refl ())
B⊑A⇒⊓AB≡B (~-ref A∼B) (⊑-refl ())

⊓⟹⊑ᵣ-with-≡ : ∀ {T T₁ T₂} → (T₁∼T₂ : T₁ ∼ T₂) → ⊓ T₁∼T₂ ≡ T → T ⊑ T₂
⊓⟹⊑ᵣ-with-≡ T₁∼T₂ refl = ⊓⟹⊑ᵣ T₁∼T₂

⊓⟹⊑ₗ : ∀ {T₁ T₂} → (T₁∼T₂ : T₁ ∼ T₂) → ⊓ T₁∼T₂ ⊑ T₁
⊓⟹⊑ₗ ∼-ℕ-refl = ⊑-refl B-`ℕ
⊓⟹⊑ₗ ∼-Unit-refl = ⊑-refl B-Unit
⊓⟹⊑ₗ ∼-⋆-refl = ⊑-dyn
⊓⟹⊑ₗ {T₁ = A} (∼-⋆R _) = A⊑A A
⊓⟹⊑ₗ (∼-⋆L _) = ⊑-dyn
⊓⟹⊑ₗ (~-× x x₁) = ⊑-× (⊓⟹⊑ₗ x) (⊓⟹⊑ₗ x₁)
⊓⟹⊑ₗ (~-⇒ x x₁) = ⊑-⇒ (⊓⟹⊑ₗ x) (⊓⟹⊑ₗ x₁)
⊓⟹⊑ₗ (~-ref x) = ⊑-ref (⊓⟹⊑ₗ x)

⊓⟹⊑ₗ-with-≡ : ∀ {T T₁ T₂} → (T₁∼T₂ : T₁ ∼ T₂) → ⊓ T₁∼T₂ ≡ T → T ⊑ T₁
⊓⟹⊑ₗ-with-≡ T₁∼T₂ refl = ⊓⟹⊑ₗ T₁∼T₂

⊓-respects-∼ᵣ : ∀ {A B} → (A∼B : A ∼ B) → A ∼ ⊓ A∼B
⊓-respects-∼ᵣ ∼-ℕ-refl = ∼-ℕ-refl
⊓-respects-∼ᵣ ∼-Unit-refl = ∼-Unit-refl
⊓-respects-∼ᵣ ∼-⋆-refl = ∼-⋆-refl
⊓-respects-∼ᵣ (∼-⋆R _) = ∼-refl
⊓-respects-∼ᵣ (∼-⋆L x) = (∼-⋆L x)
⊓-respects-∼ᵣ (~-⇒ x x₁) = ~-⇒ (⊓-respects-∼ᵣ x) (⊓-respects-∼ᵣ x₁)
⊓-respects-∼ᵣ (~-× x x₁) = ~-× (⊓-respects-∼ᵣ x) (⊓-respects-∼ᵣ x₁)
⊓-respects-∼ᵣ (~-ref x) = ~-ref (⊓-respects-∼ᵣ x)

⊓-respects-∼ : ∀ {A B C} → (A∼B : A ∼ B) → (A∼C : A ∼ C) → (B∼C : B ∼ C) → A ∼ ⊓ B∼C
⊓-respects-∼ _ A∼C ∼-ℕ-refl = A∼C
⊓-respects-∼ _ A∼C ∼-Unit-refl = A∼C
⊓-respects-∼ _ A∼C ∼-⋆-refl = A∼C
⊓-respects-∼ A∼B _ (∼-⋆R _) = A∼B
⊓-respects-∼ _ A∼C (∼-⋆L _) = A∼C
⊓-respects-∼ (∼-⋆L _) _ (~-⇒ _ _) = ∼-⋆L I-⇒
⊓-respects-∼ (~-⇒ x x₁) (~-⇒ y y₁) (~-⇒ B∼C B∼C₁) = ~-⇒ (⊓-respects-∼ x y B∼C) (⊓-respects-∼ x₁ y₁ B∼C₁)
⊓-respects-∼ (∼-⋆L x) _ (~-× _ _) = ∼-⋆L I-×
⊓-respects-∼ (~-× x x₁) (~-× y y₁) (~-× B∼C B∼C₁) = ~-× (⊓-respects-∼ x y B∼C) (⊓-respects-∼ x₁ y₁ B∼C₁)
⊓-respects-∼ _ (∼-⋆L x) (~-ref _) = ∼-⋆L I-Ref
⊓-respects-∼ (~-ref x) (~-ref y) (~-ref B∼C) = ~-ref (⊓-respects-∼ x y B∼C)

⊓A∼A≡A : ∀ {A} → (A∼A : A ∼ A) → ⊓ A∼A ≡ A
⊓A∼A≡A ∼-ℕ-refl = refl
⊓A∼A≡A ∼-Unit-refl = refl
⊓A∼A≡A ∼-⋆-refl = refl
⊓A∼A≡A (∼-⋆R _) = refl
⊓A∼A≡A (∼-⋆L _) = refl
⊓A∼A≡A (~-⇒ A∼A A∼A₁) rewrite ⊓A∼A≡A A∼A | ⊓A∼A≡A A∼A₁ = refl
⊓A∼A≡A (~-× A∼A A∼A₁) rewrite ⊓A∼A≡A A∼A | ⊓A∼A≡A A∼A₁ = refl
⊓A∼A≡A (~-ref A∼A) rewrite ⊓A∼A≡A A∼A = refl

⊓-respects-≡ : ∀ {A B} → (A∼B A∼B' : A ∼ B) → ⊓ A∼B ≡ ⊓ A∼B'
⊓-respects-≡ x y rewrite ∼-respects-≡ x y = refl
