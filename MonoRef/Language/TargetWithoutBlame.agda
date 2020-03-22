open import MonoRef.Static.Types

module MonoRef.Language.TargetWithoutBlame
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.List.Membership.Propositional using (_∈_)

open import MonoRef.Static.Types.Relations
open import MonoRef.Static.Context


infix  4 _∣_⊢_
infix  5 !

data _∣_⊢_ (Σ : StoreTyping) : Context → Type → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
      ------
    → Σ ∣ Γ ⊢ A

  ƛ_  :  ∀ {Γ A B}
    → Σ ∣ Γ , A ⊢ B
      ----------
    → Σ ∣ Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Σ ∣ Γ ⊢ A ⇒ B
    → Σ ∣ Γ ⊢ A
      ----------
    → Σ ∣ Γ ⊢ B

  `zero : ∀ {Γ}
      ----------
    → Σ ∣ Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Σ ∣ Γ ⊢ `ℕ
      -------
    → Σ ∣ Γ ⊢ `ℕ

  case : ∀ {Γ A}
    → Σ ∣ Γ ⊢ `ℕ
    → Σ ∣ Γ ⊢ A
    → Σ ∣ Γ , `ℕ ⊢ A
      -----------
    → Σ ∣ Γ ⊢ A

  ref : ∀ {Γ}
    → (A : Type)
    → Σ ∣ Γ ⊢ A
      -------------
    → Σ ∣ Γ ⊢ Ref A

  _`×_ : ∀ {Γ A B}
    → Σ ∣ Γ ⊢ A
    → Σ ∣ Γ ⊢ B
      ------
    → Σ ∣ Γ ⊢ A `× B

  π₁_ : ∀ {Γ A B}
    → Σ ∣ Γ ⊢ A `× B
      ------
    → Σ ∣ Γ ⊢ A

  π₂_ : ∀ {Γ A B}
    → Σ ∣ Γ ⊢ A `× B
      ------
    → Σ ∣ Γ ⊢ B

  addr : ∀ {Γ A B}
    → A ∈ Σ
    → A ⊑ B
      -------------
    → Σ ∣ Γ ⊢ Ref B

  !ₛ_ : ∀ {Γ A}
    → Σ ∣ Γ ⊢ Ref A
    → static A
      --------
    → Σ ∣ Γ ⊢ A

  _:=ₛ_ : ∀ {Γ A}
    → Σ ∣ Γ ⊢ Ref A
    → Σ ∣ Γ ⊢ A
    → static A
      -----------
    → Σ ∣ Γ ⊢ Unit

  ! : ∀ {Γ}
    → (A : Type)
    → Σ ∣ Γ ⊢ Ref A
      -------------
    → Σ ∣ Γ ⊢ A

  := : ∀ {Γ}
    → (A : Type)
    → Σ ∣ Γ ⊢ Ref A
    → Σ ∣ Γ ⊢ A
      -----------
    → Σ ∣ Γ ⊢ Unit

  unit : ∀ {Γ}
      -----------
    → Σ ∣ Γ ⊢ Unit

  _<_> : ∀ {Γ A B}
    → Σ ∣ Γ ⊢ A
    → A ⟹ B
      ---------
    → Σ ∣ Γ ⊢ B

  error : ∀ {Γ A}
      ---------
    → Σ ∣ Γ ⊢ A
