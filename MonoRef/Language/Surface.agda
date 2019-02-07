module MonoRef.Language.Surface where

open import Data.String using (String)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)

open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations
open import MonoRef.Static.Context

infix  4 _⊢ₛ_

infix  5 ƛ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 #_

data _⊢ₛ_ : Context → Type → Set where

  `_ : ∀ {Γ} {A}
    → Γ ∋ A
      ------
    → Γ ⊢ₛ A

  ƛ_  :  ∀ {Γ} {A B}
    → Γ , A ⊢ₛ B
      ----------
    → Γ ⊢ₛ A ⇒ B

  _·_ : ∀ {Γ} {A A' B}
    → Γ ⊢ₛ A ⇒ B
    → Γ ⊢ₛ A'
    → A ∼ A'
      ----------
    → Γ ⊢ₛ B

  _·ᵤ_ : ∀ {Γ} {A}
    → Γ ⊢ₛ ⋆
    → Γ ⊢ₛ A
      ----------
    → Γ ⊢ₛ ⋆

  `zero : ∀ {Γ}
      ----------
    → Γ ⊢ₛ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ₛ `ℕ
      -------
    → Γ ⊢ₛ `ℕ

  case : ∀ {Γ A B}
    → Γ ⊢ₛ A
    → A ∼ `ℕ
    → Γ ⊢ₛ B
    → Γ , `ℕ ⊢ₛ B
      -----------
    → Γ ⊢ₛ B

  ref_ : ∀ {Γ A}
    → Γ ⊢ₛ A
      -----------
    → Γ ⊢ₛ Ref A

  !_ : ∀ {Γ A}
    → Γ ⊢ₛ Ref A
      -----------
    → Γ ⊢ₛ A

  !ᵤ_ : ∀ {Γ}
    → Γ ⊢ₛ ⋆
      -----------
    → Γ ⊢ₛ ⋆

  _:=_ : ∀ {Γ A B}
    → Γ ⊢ₛ Ref A
    → Γ ⊢ₛ B
    → A ∼ B
      -----------
    → Γ ⊢ₛ Unit

  _:=ᵤ_ : ∀ {Γ A}
    → Γ ⊢ₛ ⋆
    → Γ ⊢ₛ A
      -----------
    → Γ ⊢ₛ Unit

  _`×_ : ∀ {Γ A B}
    → Γ ⊢ₛ A
    → Γ ⊢ₛ B
      -----------
    → Γ ⊢ₛ A `× B

  π₁_ : ∀ {Γ A B}
    → Γ ⊢ₛ A `× B
      -----------
    → Γ ⊢ₛ A

  π₁ᵤ_ : ∀ {Γ}
    → Γ ⊢ₛ ⋆
      -----------
    → Γ ⊢ₛ ⋆

  π₂_ : ∀ {Γ A B}
    → Γ ⊢ₛ A `× B
      -----------
    → Γ ⊢ₛ B

  π₂ᵤ_ : ∀ {Γ}
    → Γ ⊢ₛ ⋆
      -----------
    → Γ ⊢ₛ ⋆

  unit : ∀ {Γ}
    → Γ ⊢ₛ Unit

lookup : Context → ℕ → Type
lookup (Γ , A) zero     =  A
lookup (Γ , _) (suc n)  =  lookup Γ n
lookup ∅       _        =  ⊥-elim impossible
  where postulate impossible : ⊥

count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
count {Γ , _} zero     =  Z
count {Γ , _} (suc n)  =  S (count n)
count {∅}     _        =  ⊥-elim impossible
  where postulate impossible : ⊥

#_ : ∀ {Γ} → (n : ℕ) → Γ ⊢ₛ lookup Γ n
# n  =  ` count n

-- Examples

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ₛ `ℕ
_ = ` Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ₛ `ℕ ⇒ `ℕ
_ = ` S Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ₛ `ℕ
_ = (` S Z · ` Z) ∼-ℕ-refl

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ₛ `ℕ
_ = (` S Z · ((` S Z · ` Z) ∼-ℕ-refl)) ∼-ℕ-refl

_ : ∅ , `ℕ ⇒ `ℕ ⊢ₛ `ℕ ⇒ `ℕ
_ = ƛ (` S Z · ((` S Z · ` Z) ∼-ℕ-refl)) ∼-ℕ-refl

_ : ∅ ⊢ₛ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
_ = ƛ ƛ (` S Z · ((` S Z · ` Z) ∼-ℕ-refl)) ∼-ℕ-refl
