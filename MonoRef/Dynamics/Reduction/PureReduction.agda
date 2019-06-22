{-

  MonoRef.Dynamics.PureReduction provides a reduction relation for pure
  casts. It is parameterized over the representation of values.

-}

open import MonoRef.Static.Types

module MonoRef.Dynamics.Reduction.PureReduction
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  (make-coercion : (A B : Type) → A ⟹ B)
  where

open import MonoRef.Dynamics.Substitution _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame _⟹_ Inert
open import MonoRef.Static.Context


module ParamPureReduction
  (SimpleValue : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (Value : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  where

  infix 3 _⟶_

  data _⟶_ {Γ Σ} : ∀ {A} → Σ ∣ Γ ⊢ A → Σ ∣ Γ ⊢ A → Set where
    β-ƛ : ∀ {A B}
            {N : Σ ∣ Γ , A ⊢ B}
            {W : Σ ∣ Γ ⊢ A}
      → Value W
        --------------------
      → (ƛ N) · W ⟶ N [ W ]

    β-ƛₚ : ∀ {A B A' B'}
             {V : Σ ∣ Γ ⊢ A ⇒ B}
             {W : Σ ∣ Γ ⊢ A'}
             {c : (A ⇒ B) ⟹ (A' ⇒ B')}
      → SimpleValue V
      → Value W
        -------------------------------------------------------------------------
      → (V < c >) · W ⟶ (V · (W < make-coercion A' A >)) < make-coercion B B' >

    β-zero :  ∀ {A}
                {M : Σ ∣ Γ ⊢ A}
                {N : Σ ∣ Γ , `ℕ ⊢ A}
        --------------------
      → case `zero M N ⟶ M

    β-suc : ∀ {A}
              {V : Σ ∣ Γ ⊢ `ℕ}
              {M : Σ ∣ Γ ⊢ A}
              {N : Σ ∣ Γ , `ℕ ⊢ A}
      → Value V
        -----------------------------
      → case (`suc V) M N ⟶ N [ V ]

    β-π₁ : ∀ {A B}
             {M : Σ ∣ Γ ⊢ A}
             {N : Σ ∣ Γ ⊢ B}
      → Value M
      → Value N
        ----------------
      → π₁ (M `× N) ⟶ M

    β-π₂ : ∀ {A B}
             {M : Σ ∣ Γ ⊢ A}
             {N : Σ ∣ Γ ⊢ B}
      → Value M
      → Value N
        ----------------
      → π₂ (M `× N) ⟶ N
