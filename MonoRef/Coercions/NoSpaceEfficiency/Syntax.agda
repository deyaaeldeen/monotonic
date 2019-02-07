module MonoRef.Coercions.NoSpaceEfficiency.Syntax where

open import MonoRef.Static.Types

infix  4 _⟹_

data _⟹_ : Type → Type → Set where

  ι : ∀ {A}
    → A ⟹ A

  _`? : (A : Type)
    → ⋆ ⟹ A

  _! : (A : Type)
    → A ⟹ ⋆

  _▹_ : ∀ {A B C}
    → A ⟹ B
    → B ⟹ C
    → A ⟹ C

  _⇒_ : ∀ {A A' B B'}
    → A' ⟹ A
    → B ⟹ B'
    → A ⇒ B ⟹ A' ⇒ B'

  _`×_ : ∀ {A A' B B'}
    → A ⟹ A'
    → B ⟹ B'
    → A `× B ⟹ A' `× B'

  Ref_ : ∀ {A : Type}
    → (B : Type)
    → Ref A ⟹ Ref B

  `⊥ : ∀ {A B}
    → A ⟹ B

coerce : (t₁ t₂ : Type) → t₁ ⟹ t₂
coerce (t₁ ⇒ t₃) (t₂ ⇒ t₄) = coerce t₂ t₁ ⇒ coerce t₃ t₄
coerce (t₁ ⇒ t₃) (Ref t₂) = `⊥
coerce (t₁ ⇒ t₃) (t₂ `× t₄) = `⊥
coerce (t₁ ⇒ t₃) `ℕ = `⊥
coerce (t₁ ⇒ t₃) Unit = `⊥
coerce (t₁ ⇒ t₃) ⋆ = (t₁ ⇒ t₃) !
coerce (Ref t₁) (t₂ ⇒ t₃) = `⊥
coerce (Ref t₁) (Ref t₂) = Ref t₂
coerce (Ref t₁) (t₂ `× t₃) = `⊥
coerce (Ref t₁) `ℕ = `⊥
coerce (Ref t₁) Unit = `⊥
coerce (Ref t₁) ⋆ = (Ref t₁) !
coerce (t₁ `× t₃) (t₂ ⇒ t₄) = `⊥
coerce (t₁ `× t₃) (Ref t₂) = `⊥
coerce (t₁ `× t₃) (t₂ `× t₄) = coerce t₁ t₂ `× coerce t₃ t₄
coerce (t₁ `× t₃) `ℕ = `⊥
coerce (t₁ `× t₃) Unit = `⊥
coerce (t₁ `× t₃) ⋆ = (t₁ `× t₃) !
coerce `ℕ (t₂ ⇒ t₃) = `⊥
coerce `ℕ (Ref t₂) = `⊥
coerce `ℕ (t₂ `× t₃) = `⊥
coerce `ℕ `ℕ = ι
coerce `ℕ Unit = `⊥
coerce `ℕ ⋆ = `ℕ !
coerce Unit t₂ = `⊥
coerce ⋆ t₂ = t₂ `?
