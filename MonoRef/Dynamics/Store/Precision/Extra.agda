open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Precision.Extra
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.Empty using (⊥-elim)
open import Data.List using ([] ; _∷_)
open import Data.List.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Pointwise
  using (Pointwise ; [] ; _∷_) renaming (refl to pw-refl ; transitive to pw-trans ; map to pw-map)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Product using (∃-syntax ; _×_ ; -,_ ; proj₁ ; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary using (Transitive ; Rel)
open import Relation.Binary.HeterogeneousEquality using (_≅_ ; ≅-to-≡) renaming (refl to hrefl)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary using (yes ; no)

open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Ptr
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Types.Relations



A⊑ₕB⊑ₕD≡A⊑ₕC⊑ₕD : ∀ {A B C D}
  → (A⊑B : A ⊑ₕ B)
  → (A⊑C : A ⊑ₕ C)
  → (B⊑D : B ⊑ₕ D)
  → (C⊑D : C ⊑ₕ D)
  → (⊑ₕ-trans A⊑B B⊑D) ≡ (⊑ₕ-trans A⊑C C⊑D)
A⊑ₕB⊑ₕD≡A⊑ₕC⊑ₕD [] [] [] [] = refl
A⊑ₕB⊑ₕD≡A⊑ₕC⊑ₕD (x∼y ∷ A⊑B) (x∼y₁ ∷ A⊑C) (x∼y₂ ∷ B⊑D) (x∼y₃ ∷ C⊑D)
  rewrite A⊑B⊑D≡A⊑C⊑D x∼y x∼y₁ x∼y₂ x∼y₃ | A⊑ₕB⊑ₕD≡A⊑ₕC⊑ₕD A⊑B A⊑C B⊑D C⊑D = refl

∈ᵣ-⊒ₕ-refl : ∀ {A Σ} → (A∈Σ : A ∈ Σ) → proj₁ (∈ᵣ-⊒ₕ (pw-lift-∈ᵣ ⊑ₕ-refl A∈Σ)) ≡ A
∈ᵣ-⊒ₕ-refl (here refl) = refl
∈ᵣ-⊒ₕ-refl (there A∈Σ) rewrite ∈ᵣ-⊒ₕ-refl A∈Σ = refl

⊑ₕ∈⇒∈ᵣ-refl : ∀ {A Σ}
  → (A∈Σ : A ∈ Σ) → ⊑ₕ∈⇒∈ᵣ (proj₂ (∈ᵣ-⊒ₕ (pw-lift-∈ᵣ ⊑ₕ-refl A∈Σ))) ≅ A∈Σ
⊑ₕ∈⇒∈ᵣ-refl (here refl) = hrefl
⊑ₕ∈⇒∈ᵣ-refl (there A∈Σ)
  with ⊑ₕ∈⇒∈ᵣ (proj₂ (∈ᵣ-⊒ₕ (pw-lift-∈ᵣ ⊑ₕ-refl A∈Σ))) | ⊑ₕ∈⇒∈ᵣ-refl A∈Σ
... | w | q rewrite ∈ᵣ-⊒ₕ-refl A∈Σ | ≅-to-≡ q = hrefl

Σₗ⊓Σᵣ : ∀ {Σ Σₗ Σᵣ} → Σₗ ⊑ₕ Σ → Σᵣ ⊑ₕ Σ → ∃[ Σ' ] (Σ' ⊑ₕ Σₗ)
Σₗ⊓Σᵣ [] [] = -, []
Σₗ⊓Σᵣ (_∷_ {x = A} x∼y Σₗ) (_∷_ {x = B} x∼y₁  Σᵣ)
  with ∼-decidable A B
... | no ¬A∼B = -, ⊑-reflexive ∷ proj₂ (Σₗ⊓Σᵣ Σₗ Σᵣ)
... | yes A∼B = -, ⊓⟹⊑ₗ A∼B ∷ proj₂ (Σₗ⊓Σᵣ Σₗ Σᵣ)
