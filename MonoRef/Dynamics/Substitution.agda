open import MonoRef.Static.Types

module MonoRef.Dynamics.Substitution (_⟹_ : Type → Type → Set)
                                     (_! : (A : Type) → A ⟹ ⋆) where

open import MonoRef.Language.TargetWithoutBlame _⟹_ _!
open import MonoRef.Static.Context


ext : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ∋ A)
    -----------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

rename : ∀ {Γ Δ Σ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    ------------------------
  → (∀ {A} → Σ ∣ Γ ⊢ A → Σ ∣ Δ ⊢ A)
rename ρ (` x)           = ` (ρ x)
rename ρ (ƛ N)           = ƛ (rename (ext ρ) N)
rename ρ (ƛₚ L c)        = ƛₚ (rename ρ L) c
rename ρ (L · M)         = (rename ρ L) · (rename ρ M)
rename ρ (`zero)         = `zero
rename ρ (`suc M)        = `suc (rename ρ M)
rename ρ (case L M N)    = case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (ref x)         = ref rename ρ x
rename ρ (x `× x₁)       = rename ρ x `× rename ρ x₁
rename ρ (π₁ x)          = π₁ rename ρ x
rename ρ (π₂ x)          = π₂ rename ρ x
rename ρ (addr x p)      = addr x p
rename ρ ((!ₛ x) x₁)     = (!ₛ rename ρ x) x₁
rename ρ ((x :=ₛ x₁) x₂) = (rename ρ x :=ₛ rename ρ x₁) x₂
rename ρ (! x)           = ! rename ρ x
rename ρ (x := x₁)       = rename ρ x := rename ρ x₁
rename ρ unit            = unit
rename ρ (x < x₁ >)      = rename ρ x < x₁ >
rename ρ error           = error

exts : ∀ {Γ Δ Σ}
  → (∀ {A} →       Γ ∋ A →     Σ ∣ Δ ⊢ A)
    ----------------------------------
  → (∀ {A B} → Γ , B ∋ A → Σ ∣ Δ , B ⊢ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

subst : ∀ {Γ Δ Σ}
  → (∀ {A} → Γ ∋ A → Σ ∣ Δ ⊢ A)
    ------------------------
  → (∀ {A} → Σ ∣ Γ ⊢ A → Σ ∣ Δ ⊢ A)
subst σ (` k)           = σ k
subst σ (ƛ N)           = ƛ (subst (exts σ) N)
subst σ (ƛₚ L c)        = ƛₚ (subst σ L) c
subst σ (L · M)         = (subst σ L) · (subst σ M)
subst σ (`zero)         = `zero
subst σ (`suc M)        = `suc (subst σ M)
subst σ (case L M N)    = case (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (ref x)         = ref subst σ x
subst σ (x `× x₁)       = subst σ x `× subst σ x₁
subst σ (π₁ x)          = π₁ subst σ x
subst σ (π₂ x)          = π₂ subst σ x
subst σ (addr x p)      = addr x p
subst σ ((!ₛ x) x₁)     = (!ₛ subst σ x) x₁
subst σ ((x :=ₛ x₁) x₂) = (subst σ x :=ₛ subst σ x₁) x₂
subst σ (! x)           = ! subst σ x
subst σ (x := x₁)       = subst σ x := subst σ x₁
subst σ unit            = unit
subst σ (x < x₁ >)      = subst σ x < x₁ >
subst σ error           = error

_[_] : ∀ {Γ Σ A B}
        → Σ ∣ Γ , B ⊢ A
        → Σ ∣ Γ ⊢ B 
          ---------
        → Σ ∣ Γ ⊢ A
_[_] {Γ} {Σ} {A} {B} N M =  subst {Γ , B} {Γ} σ {A} N
  where
  σ : ∀ {A} → Γ , B ∋ A → Σ ∣ Γ ⊢ A
  σ Z      =  M
  σ (S x)  =  ` x
