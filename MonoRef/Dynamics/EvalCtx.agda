module MonoRef.Dynamics.EvalCtx where

open import MonoRef.Coercions.NoSpaceEfficiency.Syntax
open import MonoRef.Language.TargetWithoutBlameNoSE
open import MonoRef.Static.Context
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


infix 3 _≡_[_]

-- there is no possibility of capture when placing an expression in the hole of
-- an evaluation context because the hole can not appear inside a binding
-- construct

data ECtx {Γ Σ} : (A B : Type) → Set where

  ξ-ƛₚ : ∀ {A A' B B'}
    → A ⇒ B ⟹ A' ⇒ B'
      -------------
    → ECtx (A ⇒ B) (A' ⇒ B')

  ξ-appₗ : ∀ {A B}
    → Σ ∣ Γ ⊢ A -- the stuff in the context
      -------------
    → ECtx (A ⇒ B) B
    --     ^ the type of the hole
    --             ^ the type of the context after being filled

  ξ-appᵣ : ∀ {A B}
    → Σ ∣ Γ ⊢ A ⇒ B
      -------------
    → ECtx A B

  ξ-suc :
      -----------
      ECtx `ℕ `ℕ

  ξ-caseₚ : ∀ {A}
    → Σ ∣ Γ ⊢ A
    → Σ ∣ Γ , `ℕ ⊢ A
      --------------
    → ECtx `ℕ A

  ξ-×ₗ : ∀ {A B}
    → Σ ∣ Γ ⊢ B
      ---------------
    → ECtx A (A `× B)

  ξ-×ᵣ : ∀ {A B}
    → Σ ∣ Γ ⊢ A
      ---------------
    → ECtx B (A `× B)

  ξ-πₗ : ∀ {A B}
      ---------------
    → ECtx (A `× B) A

  ξ-πᵣ : ∀ {A B}
      ---------------
    → ECtx (A `× B) B

  ξ-ref : ∀ {A}
      --------------
    → ECtx A (Ref A)

  ξ-!ₛ : ∀ {A}
      --------------
    → ECtx (Ref A) A

  ξ-! : ∀ {A}
      --------------
    → ECtx (Ref A) A

  ξ-:=ₛₗ : ∀ {A}
    → Σ ∣ Γ ⊢ A
      -----------------
    → ECtx (Ref A) Unit

  ξ-:=ₛᵣ : ∀ {A}
    → Σ ∣ Γ ⊢ Ref A
      ------------
    → ECtx A Unit

  ξ-:=ₗ : ∀ {A}
    → Σ ∣ Γ ⊢ A
      -----------------
    → ECtx (Ref A) Unit

  ξ-:=ᵣ : ∀ {A}
    → Σ ∣ Γ ⊢ Ref A
      ------------
    → ECtx A Unit

  ξ-<> : ∀ {A B}
    → A ⟹ B
      --------
    → ECtx A B


data _≡_[_] {Γ Σ} : ∀ {A B} → Σ ∣ Γ ⊢ B → ECtx A B → Σ ∣ Γ ⊢ A → Set where

  □-ƛₚ : ∀ {A A' B B'} {t : Σ ∣ Γ ⊢ A ⇒ B}
    → (u : A ⇒ B ⟹ A' ⇒ B')
      ----------------------------
    → (ƛₚ t u) ≡ (ξ-ƛₚ u) [ t ]

  □-·ₗ : ∀ {A B} {t : Σ ∣ Γ ⊢ A ⇒ B}
    → (u : Σ ∣ Γ ⊢ A)
      ----------------------------
    → (t · u) ≡ (ξ-appₗ u) [ t ]

  □-·ᵣ : ∀ {A B u} {t : Σ ∣ Γ ⊢ A ⇒ B}
    → Value t
      ----------------------------
    → (t · u) ≡ (ξ-appᵣ t) [ u ]

  □-suc : ∀ {t : Σ ∣ Γ ⊢ `ℕ}
      ----------------------------
    → (`suc t) ≡ ξ-suc [ t ]

  □-caseₚ : ∀ {A} {p : Σ ∣ Γ ⊢ `ℕ}
    → (z : Σ ∣ Γ ⊢ A)
    → (s : Σ ∣ Γ , `ℕ ⊢ A)
      ----------------------------------
    → (case p z s) ≡ (ξ-caseₚ z s) [ p ]

  □-×ₗ : ∀ {A B}
            {t : Σ ∣ Γ ⊢ A}
    → (u : Σ ∣ Γ ⊢ B)
      -------------------------
    → (t `× u) ≡ (ξ-×ₗ u) [ t ]

  □-×ᵣ : ∀ {A B}
           {u : Σ ∣ Γ ⊢ B} {t : Σ ∣ Γ ⊢ A}
    → Value t
      ------------------------
    → (t `× u) ≡ (ξ-×ᵣ t) [ u ]

  □-π₁ : ∀ {A B}
           {t : Σ ∣ Γ ⊢ A `× B}
      ------------------------
    → (π₁ t) ≡ ξ-πₗ [ t ]

  □-π₂ : ∀ {A B}
           {t : Σ ∣ Γ ⊢ A `× B}
      ------------------------
    → (π₂ t) ≡ ξ-πᵣ [ t ]

  □-ref : ∀ {A} {t : Σ ∣ Γ ⊢ A}
      ------------------------
    → (ref t) ≡ ξ-ref [ t ]

  □-!ₛ : ∀ {A} {t : Σ ∣ Γ ⊢ Ref A}
    → (x : static A)
      ---------------------------
    → (!ₛ t) x ≡ ξ-!ₛ [ t ]

  □-! : ∀ {A} {t : Σ ∣ Γ ⊢ Ref A}
      --------------------------
    → (! t) ≡ ξ-! [ t ]

  □-:=ₛₗ : ∀ {A} {t : Σ ∣ Γ ⊢ Ref A}
    → (u : Σ ∣ Γ ⊢ A)
    → (x : static A)
      ------------------------------
    → (t :=ₛ u) x ≡ (ξ-:=ₛₗ u) [ t ]

  □-:=ₛᵣ : ∀ {A} {u : Σ ∣ Γ ⊢ A} {t : Σ ∣ Γ ⊢ Ref A}
    → Value t
    → (x : static A)
      -----------------------------
    → (t :=ₛ u) x ≡ (ξ-:=ₛᵣ t) [ u ]

  □-:=ₗ : ∀ {A}
            {t : Σ ∣ Γ ⊢ Ref A}
    → (u : Σ ∣ Γ ⊢ A)
      --------------------------
    → (t := u) ≡ (ξ-:=ₗ u) [ t ]

  □-:=ᵣ : ∀ {A} {u : Σ ∣ Γ ⊢ A} {t : Σ ∣ Γ ⊢ Ref A}
    → Value t
      -------------------------
    → (t := u) ≡ (ξ-:=ᵣ t) [ u ]

  □-<> : ∀ {A B}
           {t : Σ ∣ Γ ⊢ A}
    → (c : A ⟹ B)
      --------------------------
    → (t < c >) ≡ (ξ-<> c) [ t ]
