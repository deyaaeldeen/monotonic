open import MonoRef.Static.Types

module MonoRef.Language.TargetWithoutBlame (_⟹_ : Type → Type → Set)
                                           (_! : (A : Type) → (A ⟹ ⋆))
                                            where

open import Data.List using (List)
open import Data.List.Membership.Propositional
  using (_∈_)

open import MonoRef.Static.Types.Relations
open import MonoRef.Static.Context


infix  4 _∣_⊢_

StoreTyping = List Type

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

  ref_ : ∀ {Γ A}
    → Σ ∣ Γ ⊢ A
      ------
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
      ------
    → Σ ∣ Γ ⊢ Ref B

  !ₛ_ : ∀ {Γ A}
    → Σ ∣ Γ ⊢ Ref A
    → static A
      ------
    → Σ ∣ Γ ⊢ A

  _:=ₛ_ : ∀ {Γ A}
    → Σ ∣ Γ ⊢ Ref A
    → Σ ∣ Γ ⊢ A
    → static A
      ------
    → Σ ∣ Γ ⊢ Unit

  !_ : ∀ {Γ A}
    → Σ ∣ Γ ⊢ Ref A
      ------
    → Σ ∣ Γ ⊢ A

  _:=_ : ∀ {Γ A}
    → Σ ∣ Γ ⊢ Ref A
    → Σ ∣ Γ ⊢ A
      ------
    → Σ ∣ Γ ⊢ Unit

  unit : ∀ {Γ}
      ------
    → Σ ∣ Γ ⊢ Unit

  _<_> : ∀ {Γ A B}
    → Σ ∣ Γ ⊢ A
    → A ⟹ B
      ------
    → Σ ∣ Γ ⊢ B

  error : ∀ {Γ A}
    → Σ ∣ Γ ⊢ A


data Value : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set where

  V-ƛ : ∀ {Σ Γ A B}
    → (N : Σ ∣ Γ , A ⊢ B)
      ------------------
    → Value (ƛ N)

  V-zero : ∀ {Γ Σ}
      -----------------------------
    → Value (`zero {Σ = Σ} {Γ = Γ})

  V-suc : ∀ {Σ Γ} {V : Σ ∣ Γ ⊢ `ℕ}
    → Value V
      --------------
    → Value (`suc V)

  V-unit : ∀ {Σ Γ}
      ----------------------------
    → Value (unit {Σ = Σ} {Γ = Γ})

  V-addr : ∀ {Σ Γ A B}
    → (x : A ∈ Σ)
    → (y : A ⊑ B)
      ------------------------
    → Value (addr {Γ = Γ} x y)

  V-pair : ∀ {Σ Γ A B}
           {V₁ : Σ ∣ Γ ⊢ A} {V₂ : Σ ∣ Γ ⊢ B}
    → Value V₁
    → Value V₂
      ---------------
    → Value (V₁ `× V₂)

  V-inj : ∀ {Σ Γ A} {V : Σ ∣ Γ ⊢ A}
    → Value V
      -----------------
    → Value (V < A ! >)

  V-ƛₚ : ∀ {Σ Γ A A' B B'} {V : Σ ∣ Γ ⊢ A ⇒ B}
    → Value V
    → (c : (A ⇒ B) ⟹ (A' ⇒ B'))
      ---------------------------
    → Value (V < c >)
