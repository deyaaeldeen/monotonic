open import MonoRef.Static.Types

module MonoRef.Compilation.CastInsertion
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  (make-coercion : (A B : Type) → A ⟹ B)
  where

open import MonoRef.Language.Surface
open import MonoRef.Language.TargetWithoutBlame _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations

infix  3 _∣_⊢_⦂_↪_

data _∣_⊢_⦂_↪_ : (Σ : StoreTyping) → (Γ : Context) → (T : Type)
    → Γ ⊢ₛ T → Σ ∣ Γ ⊢ T → Set where

  `_ : ∀ {Γ Σ T}
    → (var : Γ ∋ T)
      ------------------------
    → Σ ∣ Γ ⊢ T ⦂ ` var ↪ ` var

  ƛ_  : ∀ {Γ Σ A B}
          {s : Γ , A ⊢ₛ B} {t : Σ ∣ Γ , A ⊢ B}
    → Σ ∣ Γ , A ⊢ B ⦂ s ↪ t
      ------------------------
    → Σ ∣ Γ ⊢ A ⇒ B ⦂ ƛ s ↪ ƛ t

  _·_ : ∀ {Γ Σ} {A A' B}
          {sf : Γ ⊢ₛ A ⇒ B} {sa : Γ ⊢ₛ A'}
          {tf : Σ ∣ Γ ⊢ A ⇒ B} {ta : Σ ∣ Γ ⊢ A'}
    → (x : A ∼ A')
    → Σ ∣ Γ ⊢ A ⇒ B ⦂ sf ↪ tf
    → Σ ∣ Γ ⊢ A' ⦂ sa ↪ ta
      --------------------------------------------------
    → Σ ∣ Γ ⊢ B ⦂ (sf · sa) x ↪ tf · (ta < make-coercion A' A >)

  _·ᵤ_ : ∀ {Γ Σ} {A}
           {sf : Γ ⊢ₛ ⋆} {sa : Γ ⊢ₛ A}
           {tf : Σ ∣ Γ ⊢ ⋆} {ta : Σ ∣ Γ ⊢ A}
           {prj : ⋆ ⟹ (⋆ ⇒ ⋆)} {inj : A ⟹ ⋆}
    → (A≢⋆ : Injectable A)
    → Σ ∣ Γ ⊢ ⋆ ⦂ sf ↪ tf
    → Σ ∣ Γ ⊢ A ⦂ sa ↪ ta
      ----------------------------------------------------
    → Σ ∣ Γ ⊢ ⋆ ⦂ sf ·ᵤ sa ↪ tf < prj > · ta < inj >

  `zero : ∀ {Γ Σ}
      --------------------------
    → Σ ∣ Γ ⊢ `ℕ ⦂ `zero ↪ `zero

  `suc_ : ∀ {Γ Σ} {sn tn}
    → Σ ∣ Γ ⊢ `ℕ ⦂ sn ↪ tn
      ------------------------------
    → Σ ∣ Γ ⊢ `ℕ ⦂ `suc sn ↪ `suc tn

  case : ∀ {Γ Σ A} {sn tn sz tz ss ts}
    → Σ ∣ Γ ⊢ `ℕ ⦂ sn ↪ tn
    → Σ ∣ Γ ⊢ A ⦂ sz ↪ tz
    → Σ ∣ Γ , `ℕ ⊢ A ⦂ ss ↪ ts
      -----------------------------------------------
    → Σ ∣ Γ ⊢ A ⦂ case sn ∼-refl sz ss ↪ case tn tz ts

  caseᵤ : ∀ {Γ Σ A} {sn tn sz tz ss ts} {prj : ⋆ ⟹ `ℕ}
    → Σ ∣ Γ ⊢ ⋆ ⦂ sn ↪ tn
    → Σ ∣ Γ ⊢ A ⦂ sz ↪ tz
    → Σ ∣ Γ , `ℕ ⊢ A ⦂ ss ↪ ts
      ----------------------------------------------------------
    → Σ ∣ Γ ⊢ A ⦂ case sn ∼-⋆L sz ss ↪ case (tn < prj >) tz ts

  ref_ : ∀ {Γ Σ A} {s t}
    → Σ ∣ Γ ⊢ A ⦂ s ↪ t
      ----------------------------
    → Σ ∣ Γ ⊢ Ref A ⦂ ref s ↪ ref t

  !ₛ_ : ∀ {Γ Σ A} {s t}
    → Σ ∣ Γ ⊢ Ref A ⦂ s ↪ t
    → (p : static A)
      -------------------------
    → Σ ∣ Γ ⊢ A ⦂ ! s ↪ (!ₛ t) p

  !_ : ∀ {Γ Σ A} {s t}
    → Σ ∣ Γ ⊢ Ref A ⦂ s ↪ t
      --------------------
    → Σ ∣ Γ ⊢ A ⦂ ! s ↪ ! t

  !ᵤ_ : ∀ {Γ Σ} {s t} {prj : ⋆ ⟹ (Ref ⋆)}
    → Σ ∣ Γ ⊢ ⋆ ⦂ s ↪ t
      --------------------------------------
    → Σ ∣ Γ ⊢ ⋆ ⦂ !ᵤ s ↪ ! (t < prj >)

  _:=ₛ_ : ∀ {Γ Σ A A'} {sr tr sv tv}
    → Σ ∣ Γ ⊢ Ref A ⦂ sr ↪ tr
    → Σ ∣ Γ ⊢ A' ⦂ sv ↪ tv
    → (x : A ∼ A')
    → (y : static A)
      -------------------------------------------------------------
    → Σ ∣ Γ ⊢ Unit ⦂ (sr := sv) x ↪ (tr :=ₛ (tv < make-coercion A' A >)) y

  _:=_ : ∀ {Γ Σ A A'} {sr tr sv tv}
    → Σ ∣ Γ ⊢ Ref A ⦂ sr ↪ tr
    → Σ ∣ Γ ⊢ A' ⦂ sv ↪ tv
    → (p : A ∼ A')
      -------------------------------------------------------
    → Σ ∣ Γ ⊢ Unit ⦂ (sr := sv) p ↪ tr := (tv < make-coercion A' A >)

  _:=ᵤ_ : ∀ {Γ Σ A} {sr tr sv tv} {prj : ⋆ ⟹ (Ref ⋆)} {inj : A ⟹ ⋆}
    → (A≢⋆ : Injectable A)
    → Σ ∣ Γ ⊢ ⋆ ⦂ sr ↪ tr
    → Σ ∣ Γ ⊢ A ⦂ sv ↪ tv
      -------------------------------------------------------------
    → Σ ∣ Γ ⊢ Unit ⦂ sr :=ᵤ sv ↪ (tr < prj >) := (tv < inj >)

  _`×_ : ∀ {Γ Σ A B} {sl sr tl tr}
    → Σ ∣ Γ ⊢ A ⦂ sl ↪ tl
    → Σ ∣ Γ ⊢ B ⦂ sr ↪ tr
      ------------------------------------
    → Σ ∣ Γ ⊢ A `× B ⦂ sl `× sr ↪ tl `× tr

  π₁_ : ∀ {Γ Σ A B} {sp tp}
    → Σ ∣ Γ ⊢ A `× B ⦂ sp ↪ tp
      ------------------------
    → Σ ∣ Γ ⊢ A ⦂ π₁ sp ↪ π₁ tp

  π₁ᵤ_ : ∀ {Γ Σ} {sp tp} {prj : ⋆ ⟹ (⋆ `× ⋆)}
    → Σ ∣ Γ ⊢ ⋆ ⦂ sp ↪ tp
      ------------------------------------------
    → Σ ∣ Γ ⊢ ⋆ ⦂ π₁ᵤ sp ↪ π₁ (tp < prj >)

  π₂_ : ∀ {Γ Σ A B} {sp tp}
    → Σ ∣ Γ ⊢ A `× B ⦂ sp ↪ tp
      ------------------------
    → Σ ∣ Γ ⊢ B ⦂ π₂ sp ↪ π₂ tp

  π₂ᵤ_ : ∀ {Γ Σ} {sp tp} {prj : ⋆ ⟹ (⋆ `× ⋆)}
    → Σ ∣ Γ ⊢ ⋆ ⦂ sp ↪ tp
      ------------------------------------------
    → Σ ∣ Γ ⊢ ⋆ ⦂ π₂ᵤ sp ↪ π₂ (tp < prj >)

  unit : ∀ {Γ Σ}
      -------------------------
    → Σ ∣ Γ ⊢ Unit ⦂ unit ↪ unit
