{-

  Casted values are special kind of values that can be written to the heap.
  MonoRef.Dynamics.Store.Efficient.CastedValue provides definitions for
  efficient casted values and strong casted values. Strong casted values are
  casted values that are guaranteed to be productive i.e. have at least one
  active cast.

-}

open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Efficient.CastedValue
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  (Active : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)

open import MonoRef.Dynamics.Efficient.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert


infix 5 v⇑_


data CastedValue       {Σ Γ} : ∀ {A} →    Σ ∣ Γ ⊢ A                  → Set
data StrongCastedValue {Σ Γ} : ∀ {A} {e : Σ ∣ Γ ⊢ A} → CastedValue e → Set

data CastedValue {Σ Γ} where

  v⇑_ : ∀ {A} {e : Σ ∣ Γ ⊢ A}
    → Value e
      -------------
    → CastedValue e

  cast-val : ∀ {A B} {e : Σ ∣ Γ ⊢ A} {c : A ⟹ B}
    → SimpleValue e
    → Active c
      ---------------------
    → CastedValue (e < c >)

  cast-cval : ∀ {A B C} {e : Σ ∣ Γ ⊢ A}
    → SimpleValue e
    → (c : A ⟹ B)
    → (d : B ⟹ C)
      ---------------------------
    → CastedValue (e < c > < d >)

  cv-pair : ∀ {A B} {e₁ : Σ ∣ Γ ⊢ A} {e₂ : Σ ∣ Γ ⊢ B}
    → (cv₁ : CastedValue e₁)
    → (cv₂ : CastedValue e₂)
    → (p : (StrongCastedValue cv₁ × Value e₂)
         ⊎ (Value e₁ × StrongCastedValue cv₂)
         ⊎ (StrongCastedValue cv₁ × StrongCastedValue cv₂ ))
      -----------------------------------------------------
    → CastedValue (e₁ `× e₂)

data StrongCastedValue {Σ Γ} where

  SCV-cast : ∀ {A B} {e : Σ ∣ Γ ⊢ A} {c : A ⟹ B}
    → (v : SimpleValue e)
    → (ac : Active c)
      ---------------------------------
    → StrongCastedValue (cast-val v ac)

  SCV-ccast : ∀ {A B C} {e : Σ ∣ Γ ⊢ A}
    → (v : SimpleValue e)
    → (c : A ⟹ B)
    → (d : B ⟹ C)
      -----------------------------------
    → StrongCastedValue (cast-cval v c d)

  SCV-pair : ∀ {A B} {e₁ : Σ ∣ Γ ⊢ A} {e₂ : Σ ∣ Γ ⊢ B}
    → (cv₁ : CastedValue e₁) → (cv₂ : CastedValue e₂)
    → (p : (StrongCastedValue cv₁ × Value e₂)
         ⊎ (Value e₁ × StrongCastedValue cv₂)
         ⊎ (StrongCastedValue cv₁ × StrongCastedValue cv₂ ))
      ------------------------------------------------------
    → StrongCastedValue (cv-pair cv₁ cv₂ p)


scv-decidable : ∀ {Γ Σ A} {e : Σ ∣ Γ ⊢ A}
  → (cv : CastedValue e) → Dec (StrongCastedValue cv)
scv-decidable (v⇑ _) = no (λ ())
scv-decidable (cast-val v c) = yes (SCV-cast v c)
scv-decidable (cast-cval v c d) = yes (SCV-ccast v c d)
scv-decidable (cv-pair cv₁ cv₂ p) = yes (SCV-pair cv₁ cv₂ p)

¬scv⇒Value : ∀ {Γ Σ A} {e : Σ ∣ Γ ⊢ A} {cv : CastedValue e}
  → ¬ StrongCastedValue cv → Value e
¬scv⇒Value {cv = v⇑ x} _ = x
¬scv⇒Value {cv = cast-val x c} ¬scv = ⊥-elim (¬scv (SCV-cast x c))
¬scv⇒Value {cv = cast-cval x c d} ¬scv = ⊥-elim (¬scv (SCV-ccast x c d))
¬scv⇒Value {cv = cv-pair cv cv₁ p} ¬scv = ⊥-elim (¬scv (SCV-pair cv cv₁ p))
