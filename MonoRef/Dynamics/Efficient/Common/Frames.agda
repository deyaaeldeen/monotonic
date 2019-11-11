open import MonoRef.Static.Types

module MonoRef.Dynamics.Efficient.Common.Frames
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

-- standard library++
open import Data.List.Prefix renaming (_⊑_ to _⊑ₗ_)

open import MonoRef.Dynamics.Store.Extension
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Dynamics.Store.TypingProgress
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations using (static_)


{-

  there is no possibility of capture when placing an expression in the hole of
  an evaluation context because the hole can not appear inside a binding
  construct

-}

data Frame {Γ Σ} : (A B : Type) → Set where

  ξ-appₗ : ∀ {A B}
    → Σ ∣ Γ ⊢ A -- the stuff in the frame
      ---------------
    → Frame (A ⇒ B) B
    --      ^ the type of the hole
    --              ^ the type of the frame after being filled

  ξ-appᵣ : ∀ {A B}
    → Σ ∣ Γ ⊢ A ⇒ B
      -------------
    → Frame A B

  ξ-suc :
      -----------
      Frame `ℕ `ℕ

  ξ-caseₚ : ∀ {A}
    → Σ ∣ Γ ⊢ A
    → Σ ∣ Γ , `ℕ ⊢ A
      --------------
    → Frame `ℕ A

  ξ-×ₗ : ∀ {A B}
    → Σ ∣ Γ ⊢ B
      ----------------
    → Frame A (A `× B)

  ξ-×ᵣ : ∀ {A B}
    → Σ ∣ Γ ⊢ A
      ----------------
    → Frame B (A `× B)

  ξ-πₗ : ∀ {A B}
      ----------------
    → Frame (A `× B) A

  ξ-πᵣ : ∀ {A B}
      ----------------
    → Frame (A `× B) B

  ξ-ref : ∀ {A}
      ---------------
    → Frame A (Ref A)

  ξ-!ₛ : ∀ {A}
    → static A
      ---------------
    → Frame (Ref A) A

  ξ-! :
      (A : Type)
      ---------------
    → Frame (Ref A) A

  ξ-:=ₛₗ : ∀ {A}
    → static A
    → Σ ∣ Γ ⊢ A
      ------------------
    → Frame (Ref A) Unit

  ξ-:=ₛᵣ : ∀ {A}
    → static A
    → Σ ∣ Γ ⊢ Ref A
      -------------
    → Frame A Unit

  ξ-:=ₗ :
      (A : Type)
    → Σ ∣ Γ ⊢ A
      ------------------
    → Frame (Ref A) Unit

  ξ-:=ᵣ :
      (A : Type)
    → Σ ∣ Γ ⊢ Ref A
      -------------
    → Frame A Unit

plug : ∀{Σ Γ A B} → Σ ∣ Γ ⊢ A → Frame {Γ} {Σ} A B → Σ ∣ Γ ⊢ B
plug L (ξ-appₗ M) = L · M
plug M (ξ-appᵣ L) = L · M
plug M ξ-suc = `suc M
plug L (ξ-caseₚ M N) = case L M N
plug L (ξ-×ₗ M) = L `× M
plug M (ξ-×ᵣ L) = L `× M
plug M ξ-πₗ = π₁ M
plug M ξ-πᵣ = π₂ M
plug M ξ-ref = ref M
plug M (ξ-!ₛ x) = (!ₛ M) x
plug M (ξ-! A) = ! A M
plug M (ξ-:=ₛₗ x L) = (M :=ₛ L) x
plug L (ξ-:=ₛᵣ x M) = (M :=ₛ L) x
plug M (ξ-:=ₗ A L) = := A M L
plug L (ξ-:=ᵣ A M) = := A M L

prefix-weaken-frame : ∀ {Γ Σ Σ' A B} → Σ ⊑ₗ Σ' → Frame {Γ} {Σ} A B → Frame {Γ} {Σ'} A B
prefix-weaken-frame Σ⊑ₗΣ' (ξ-appₗ M) = ξ-appₗ (prefix-weaken-expr Σ⊑ₗΣ' M)
prefix-weaken-frame Σ⊑ₗΣ' (ξ-appᵣ M) = ξ-appᵣ (prefix-weaken-expr Σ⊑ₗΣ' M)
prefix-weaken-frame _ ξ-suc = ξ-suc
prefix-weaken-frame Σ⊑ₗΣ' (ξ-caseₚ M N) = ξ-caseₚ (prefix-weaken-expr Σ⊑ₗΣ' M) (prefix-weaken-expr Σ⊑ₗΣ' N)
prefix-weaken-frame Σ⊑ₗΣ' (ξ-×ₗ M) = ξ-×ₗ (prefix-weaken-expr Σ⊑ₗΣ' M)
prefix-weaken-frame Σ⊑ₗΣ' (ξ-×ᵣ M) = ξ-×ᵣ (prefix-weaken-expr Σ⊑ₗΣ' M)
prefix-weaken-frame _ ξ-πₗ = ξ-πₗ
prefix-weaken-frame _ ξ-πᵣ = ξ-πᵣ
prefix-weaken-frame _ ξ-ref = ξ-ref
prefix-weaken-frame _ (ξ-!ₛ x) = ξ-!ₛ x
prefix-weaken-frame _ (ξ-! A) = ξ-! A
prefix-weaken-frame Σ⊑ₗΣ' (ξ-:=ₛₗ x M) = ξ-:=ₛₗ x (prefix-weaken-expr Σ⊑ₗΣ' M)
prefix-weaken-frame Σ⊑ₗΣ' (ξ-:=ₛᵣ x M) = ξ-:=ₛᵣ x (prefix-weaken-expr Σ⊑ₗΣ' M)
prefix-weaken-frame Σ⊑ₗΣ' (ξ-:=ₗ A M) = ξ-:=ₗ A (prefix-weaken-expr Σ⊑ₗΣ' M)
prefix-weaken-frame Σ⊑ₗΣ' (ξ-:=ᵣ A M) = ξ-:=ᵣ A (prefix-weaken-expr Σ⊑ₗΣ' M)

typeprecise-strenthen-frame : ∀ {Γ Σ Σ' A B} → Σ' ⊑ₕ Σ → Frame {Γ} {Σ} A B → Frame {Γ} {Σ'} A B
typeprecise-strenthen-frame Σ'⊑ₕΣ (ξ-appₗ M) = ξ-appₗ (typeprecise-strenthen-expr Σ'⊑ₕΣ M)
typeprecise-strenthen-frame Σ'⊑ₕΣ (ξ-appᵣ M) = ξ-appᵣ (typeprecise-strenthen-expr Σ'⊑ₕΣ M)
typeprecise-strenthen-frame _ ξ-suc = ξ-suc
typeprecise-strenthen-frame Σ'⊑ₕΣ (ξ-caseₚ M N) =
  ξ-caseₚ (typeprecise-strenthen-expr Σ'⊑ₕΣ M)
          (typeprecise-strenthen-expr Σ'⊑ₕΣ N)
typeprecise-strenthen-frame Σ'⊑ₕΣ (ξ-×ₗ M) = ξ-×ₗ (typeprecise-strenthen-expr Σ'⊑ₕΣ M)
typeprecise-strenthen-frame Σ'⊑ₕΣ (ξ-×ᵣ M) = ξ-×ᵣ (typeprecise-strenthen-expr Σ'⊑ₕΣ M)
typeprecise-strenthen-frame _ ξ-πₗ = ξ-πₗ
typeprecise-strenthen-frame _ ξ-πᵣ = ξ-πᵣ
typeprecise-strenthen-frame _ ξ-ref = ξ-ref
typeprecise-strenthen-frame _ (ξ-!ₛ x) = ξ-!ₛ x
typeprecise-strenthen-frame _ (ξ-! A) = ξ-! A
typeprecise-strenthen-frame Σ'⊑ₕΣ (ξ-:=ₛₗ x M) = ξ-:=ₛₗ x (typeprecise-strenthen-expr Σ'⊑ₕΣ M)
typeprecise-strenthen-frame Σ'⊑ₕΣ (ξ-:=ₛᵣ x M) = ξ-:=ₛᵣ x (typeprecise-strenthen-expr Σ'⊑ₕΣ M)
typeprecise-strenthen-frame Σ'⊑ₕΣ (ξ-:=ₗ A M) = ξ-:=ₗ A (typeprecise-strenthen-expr Σ'⊑ₕΣ M)
typeprecise-strenthen-frame Σ'⊑ₕΣ (ξ-:=ᵣ A M) = ξ-:=ᵣ A (typeprecise-strenthen-expr Σ'⊑ₕΣ M)

-- TODO: find a better name
weaken-frame : ∀ {Γ Σ Σ' A B} → StoreTypingProgress Σ Σ' → Frame {Γ} {Σ} A B → Frame {Γ} {Σ'} A B
weaken-frame (from⊑ₕ Σ'⊑ₕΣ) f = typeprecise-strenthen-frame Σ'⊑ₕΣ f 
weaken-frame (from⊑ₗ Σ⊑Σ') f = prefix-weaken-frame Σ⊑Σ' f
