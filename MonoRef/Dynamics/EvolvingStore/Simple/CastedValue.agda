{-

  Casted values are special kind of values that can be written to the heap.
  MonoRef.Dynamics.EvolvingStore.Simple.CastedValue provides definitions for simple
  (space-inefficient) casted values and strong casted values. Strong casted
  values are casted values that are guaranteed to be productive i.e. have at
  least one active cast.

-}

open import MonoRef.Static.Types

module MonoRef.Dynamics.EvolvingStore.Simple.CastedValue
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  (Active : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)

open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Dynamics.Simple.Value
  _⟹_ Inert


infix 5 v⇑_

data CastedValue       {Σ Γ} : ∀ {A} →    Σ ∣ Γ ⊢ A                  → Set
data StrongCastedValue {Σ Γ} : ∀ {A} {e : Σ ∣ Γ ⊢ A} → CastedValue e → Set

data CastedValue {Σ Γ} where

  v⇑_ : ∀ {A} {t : Σ ∣ Γ ⊢ A}
    → Value t
      -------------
    → CastedValue t

  {-

    It is important to clarify why there is no constraint here that B ⊑ A. To
    prove progress when a casted value exists in the heap, we need to prove that
    when a casted value takes a step, the result is also a casted value. In the
    case when the casted value is ⋆ with a projection on it, it can be the case
    that the type projected to is less preciss than the type injected at and B ⊑
    A does not hold.

  -}

  cast-val : ∀ {A B} {t : Σ ∣ Γ ⊢ A} {c : A ⟹ B}
    → Value t
    → Active c
      ---------------------
    → CastedValue (t < c >)

  cast-cval : ∀ {A B} {t : Σ ∣ Γ ⊢ A}
    → (cv : CastedValue t)
    → StrongCastedValue cv
    → (c : A ⟹ B)
      ---------------------
    → CastedValue (t < c >)

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
           → (v : Value e) → (ac : Active c)
           -----------------------------------
           → StrongCastedValue (cast-val v ac)

  SCV-ccast : ∀ {A B} {e : Σ ∣ Γ ⊢ A}
            → (cv : CastedValue e)
            → (scv : StrongCastedValue cv)
            → (c : A ⟹ B)
            ----------------------------------------
            → StrongCastedValue (cast-cval cv scv c)

  SCV-pair : ∀ {A B} {e₁ : Σ ∣ Γ ⊢ A} {e₂ : Σ ∣ Γ ⊢ B}
           → (cv₁ : CastedValue e₁) → (cv₂ : CastedValue e₂)
           → (p : (StrongCastedValue cv₁ × Value e₂)
                ⊎ (Value e₁ × StrongCastedValue cv₂)
                ⊎ (StrongCastedValue cv₁ × StrongCastedValue cv₂ ))
           -------------------------------------------------------
           → StrongCastedValue (cv-pair cv₁ cv₂ p)


scv-decidable : ∀ {Γ Σ A} {e : Σ ∣ Γ ⊢ A}
  → (cv : CastedValue e) → Dec (StrongCastedValue cv)
scv-decidable (v⇑ _) = no (λ ())
scv-decidable (cast-val v c) = yes (SCV-cast v c)
scv-decidable (cast-cval cv p c) = yes (SCV-ccast cv p c)
scv-decidable (cv-pair cv₁ cv₂ p) = yes (SCV-pair cv₁ cv₂ p)

¬scv⇒Value : ∀ {Γ Σ A} {e : Σ ∣ Γ ⊢ A} {cv : CastedValue e}
  → ¬ StrongCastedValue cv → Value e
¬scv⇒Value {cv = v⇑ x} _ = x
¬scv⇒Value {cv = cast-val x c} ¬scv = ⊥-elim (¬scv (SCV-cast x c))
¬scv⇒Value {cv = cast-cval cv x c} ¬scv = ⊥-elim (¬scv (SCV-ccast cv x c))
¬scv⇒Value {cv = cv-pair cv cv₁ p} ¬scv = ⊥-elim (¬scv (SCV-pair cv cv₁ p))
