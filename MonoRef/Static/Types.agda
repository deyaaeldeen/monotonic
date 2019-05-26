module MonoRef.Static.Types where

infixr 6 _⇒_
infixr 6 Ty⇓

data Type : Set where
  _⇒_  : Type → Type → Type
  Ref  : Type        → Type
  _`×_ : Type → Type → Type
  `ℕ   : Type
  Unit : Type
  ⋆    : Type

data Ty : Type → Set where
  _⇒_  : ∀ {A B} → Ty A → Ty B → Ty (A ⇒ B)
  Ref : ∀ {A} → Ty A → Ty (Ref A)
  _`×_ : ∀ {A B} → Ty A → Ty B → Ty (A `× B)
  `ℕ   : Ty `ℕ
  Unit : Ty Unit
  ⋆ : Ty ⋆

Ty⇓ : ∀ {A} → Ty A → Type
Ty⇓ {A} _ = A

Type⇑ : (T : Type) → Ty T
Type⇑ (A ⇒ A₁) = Type⇑ A ⇒ Type⇑ A₁
Type⇑ (Ref A) = Ref (Type⇑ A)
Type⇑ (A `× A₁) = Type⇑ A `× Type⇑ A₁
Type⇑ `ℕ = `ℕ
Type⇑ Unit = Unit
Type⇑ ⋆ = ⋆
