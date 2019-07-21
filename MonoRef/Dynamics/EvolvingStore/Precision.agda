open import MonoRef.Static.Types

module MonoRef.Dynamics.EvolvingStore.Precision
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.List using (_∷_)
open import Data.List.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Pointwise
  using (Pointwise ; _∷_) renaming (refl to pw-refl ; transitive to pw-trans)
open import Data.Product using (∃-syntax ; -,_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary using (Transitive ; Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl)

open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Types.Relations


infix  3  _⊑ₕ_
infix  3 _,_∈_

{- Definition 1 (Precision relation on store typings) -}

_⊑ₕ_ : (Σ Σ' : StoreTyping) → Set
_⊑ₕ_ Σ' Σ = Pointwise _⊑_ Σ' Σ

⊑ₕ-refl : ∀ {Σ} → Σ ⊑ₕ Σ
⊑ₕ-refl = pw-refl ⊑-refl

⊑ₕ-trans : Transitive _⊑ₕ_
⊑ₕ-trans = pw-trans ⊑-trans

Σ-cast : ∀ {Σ T} → T ∈ Σ → Type → StoreTyping
Σ-cast {x ∷ Σ} (here refl) t = t ∷ Σ
Σ-cast {x ∷ Σ} (there mem) t = x ∷ Σ-cast mem t

build-prec : ∀ {Σ A B} → (A∈Σ : A ∈ Σ) → B ⊑ A → (Σ-cast A∈Σ B) ⊑ₕ Σ
build-prec (here refl) Σ'⊑ₕΣ = Σ'⊑ₕΣ ∷ ⊑ₕ-refl
build-prec (there A∈Σ) Σ'⊑ₕΣ = ⊑-refl ∷ build-prec A∈Σ Σ'⊑ₕΣ

Σ-cast⟹∈ : ∀ {Σ A}
  → (A∈Σ : A ∈ Σ) → (B : Type) → B ∈ Σ-cast A∈Σ B
Σ-cast⟹∈ A∈Σ B = helper A∈Σ B
  where
    helper : ∀ {Σ A} → (A∈Σ : A ∈ Σ) → (B : Type) → B ∈ Σ-cast A∈Σ B
    helper (here refl) B = here refl
    helper (there A∈Σ) B = there (helper A∈Σ B)

-- Views

data _,_∈_ (t' t : Type) : ∀ {Σ' Σ} → Σ' ⊑ₕ Σ → Set where

  here : ∀ {Σ' Σ} {t'⊑t : t' ⊑ t} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ}
      -------------------------
    → _,_∈_ t' t (t'⊑t ∷ Σ'⊑ₕΣ)

  there : ∀ {x y Σ' Σ} {y⊑x : y ⊑ x} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ}
    → _,_∈_ t' t Σ'⊑ₕΣ
      ------------------------
    → _,_∈_ t' t (y⊑x ∷ Σ'⊑ₕΣ)

data _⊑∈_ (t : Type) : ∀ {Σ' Σ} → Σ' ⊑ₕ Σ → Set where

  here : ∀ {Σ' Σ t'} {t'⊑t : t' ⊑ t} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ}
      -------------------
    → t ⊑∈ (t'⊑t ∷ Σ'⊑ₕΣ)

  there : ∀ {x y Σ' Σ} {y⊑x : y ⊑ x} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ}
    → t ⊑∈ Σ'⊑ₕΣ
      ------------------
    → t ⊑∈ (y⊑x ∷ Σ'⊑ₕΣ)

⊒-⊒ₕ : ∀ {Σ' Σ t' t} {prec : Σ' ⊑ₕ Σ} →  _,_∈_ t' t prec → t' ⊑ t
⊒-⊒ₕ {prec = x∼y ∷ _} here = x∼y
⊒-⊒ₕ (there mem) = ⊒-⊒ₕ mem

∈-⊒ₕ : ∀ {Σ' Σ t} {prec : Σ' ⊑ₕ Σ} → t ⊑∈ prec → ∃[ t' ] _,_∈_ t' t prec
∈-⊒ₕ here = -, here
∈-⊒ₕ (there mem) with ∈-⊒ₕ mem
... | ⟨ fst , snd ⟩  = -, there snd

pw-lift-∈ : ∀ {Σ' Σ t} → (prec : Σ' ⊑ₕ Σ) → t ∈ Σ → t ⊑∈ prec
pw-lift-∈ (x∼y ∷ prec) (here refl) = here
pw-lift-∈ (x∼y ∷ prec) (there mem) = there (pw-lift-∈ prec mem)

∈⇒⊑ₕ∈ : ∀ {Σ' Σ t} → (prec : Σ' ⊑ₕ Σ) → t ∈ Σ → ∃[ t' ] _,_∈_ t' t prec
∈⇒⊑ₕ∈ prec mem = ∈-⊒ₕ (pw-lift-∈ prec mem)

⊑ₕ∈⇒∈ : ∀ {Σ' Σ t' t} {prec : Σ' ⊑ₕ Σ}
  → _,_∈_ t' t prec → t' ∈ Σ'
⊑ₕ∈⇒∈ here = here refl
⊑ₕ∈⇒∈ (there mem) = there (⊑ₕ∈⇒∈ mem)

{- Lemma 1 (Strengthening wrt. the heap typing) -}

typeprecise-strenthen-expr : ∀ {Σ Σ' Γ A}
  → Σ' ⊑ₕ Σ → Σ ∣ Γ ⊢ A → Σ' ∣ Γ ⊢ A
typeprecise-strenthen-expr _    (` x) = ` x
typeprecise-strenthen-expr prec (ƛ e) = ƛ typeprecise-strenthen-expr prec e
typeprecise-strenthen-expr prec (e · e₁) =
  typeprecise-strenthen-expr prec e · typeprecise-strenthen-expr prec e₁
typeprecise-strenthen-expr _    `zero = `zero
typeprecise-strenthen-expr prec (`suc e) = `suc typeprecise-strenthen-expr prec e
typeprecise-strenthen-expr prec (case e e₁ e₂) =
  case (typeprecise-strenthen-expr prec e)
       (typeprecise-strenthen-expr prec e₁)
       (typeprecise-strenthen-expr prec e₂)
typeprecise-strenthen-expr prec (ref e) = ref typeprecise-strenthen-expr prec e
typeprecise-strenthen-expr prec (e `× e₁) =
  typeprecise-strenthen-expr prec e `× typeprecise-strenthen-expr prec e₁
typeprecise-strenthen-expr prec (π₁ e) = π₁ typeprecise-strenthen-expr prec e
typeprecise-strenthen-expr prec (π₂ e) = π₂ typeprecise-strenthen-expr prec e
typeprecise-strenthen-expr prec (addr mem prec') with ∈⇒⊑ₕ∈ prec mem
... | ⟨ _ ,  tt'∈prec ⟩ = addr (⊑ₕ∈⇒∈ tt'∈prec) (⊑-trans (⊒-⊒ₕ tt'∈prec) prec')
typeprecise-strenthen-expr prec ((!ₛ e) x) =
  (!ₛ typeprecise-strenthen-expr prec e) x
typeprecise-strenthen-expr prec ((e :=ₛ e₁) x) =
  (typeprecise-strenthen-expr prec e :=ₛ typeprecise-strenthen-expr prec e₁) x
typeprecise-strenthen-expr prec (! e) = ! typeprecise-strenthen-expr prec e
typeprecise-strenthen-expr prec (e := e₁) =
  typeprecise-strenthen-expr prec e := typeprecise-strenthen-expr prec e₁
typeprecise-strenthen-expr _    unit = unit
typeprecise-strenthen-expr prec (e < x >) = typeprecise-strenthen-expr prec e < x >
typeprecise-strenthen-expr _    error = error
