{-

  Casted values are special kind of values that can be written to the heap.
  MonoRef.Dynamics.EvolvingStore.Efficient.DelayedCast provides definitions for
  efficient casted values and strong casted values. Reducible casted values are
  casted values that are guaranteed to be productive i.e. have at least one
  active cast.

-}

open import MonoRef.Static.Types

module MonoRef.Dynamics.EvolvingStore.Efficient.DelayedCast
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


data DelayedCast       {Σ Γ} : ∀ {A} →    Σ ∣ Γ ⊢ A                  → Set
data ReducibleDelayedCast {Σ Γ} : ∀ {A} {e : Σ ∣ Γ ⊢ A} → DelayedCast e → Set

data DelayedCast {Σ Γ} where

  v⇑_ : ∀ {A} {e : Σ ∣ Γ ⊢ A}
    → Value e
      -------------
    → DelayedCast e

  cast-val : ∀ {A B} {e : Σ ∣ Γ ⊢ A} {c : A ⟹ B}
    → SimpleValue e
    → Active c
      ---------------------
    → DelayedCast (e < c >)

  cv-pair : ∀ {A B} {e₁ : Σ ∣ Γ ⊢ A} {e₂ : Σ ∣ Γ ⊢ B}
    → (cv₁ : DelayedCast e₁)
    → (cv₂ : DelayedCast e₂)
    → (p : (ReducibleDelayedCast cv₁ × Value e₂)
         ⊎ (Value e₁ × ReducibleDelayedCast cv₂)
         ⊎ (ReducibleDelayedCast cv₁ × ReducibleDelayedCast cv₂ ))
      -----------------------------------------------------
    → DelayedCast (e₁ `× e₂)

data ReducibleDelayedCast {Σ Γ} where

  SCV-cast : ∀ {A B} {e : Σ ∣ Γ ⊢ A} {c : A ⟹ B}
    → (v : SimpleValue e)
    → (ac : Active c)
      ---------------------------------
    → ReducibleDelayedCast (cast-val v ac)

  SCV-pair : ∀ {A B} {e₁ : Σ ∣ Γ ⊢ A} {e₂ : Σ ∣ Γ ⊢ B}
    → (cv₁ : DelayedCast e₁) → (cv₂ : DelayedCast e₂)
    → (p : (ReducibleDelayedCast cv₁ × Value e₂)
         ⊎ (Value e₁ × ReducibleDelayedCast cv₂)
         ⊎ (ReducibleDelayedCast cv₁ × ReducibleDelayedCast cv₂ ))
      ------------------------------------------------------
    → ReducibleDelayedCast (cv-pair cv₁ cv₂ p)


scv-decidable : ∀ {Γ Σ A} {e : Σ ∣ Γ ⊢ A}
  → (cv : DelayedCast e) → Dec (ReducibleDelayedCast cv)
scv-decidable (v⇑ _) = no (λ ())
scv-decidable (cast-val v c) = yes (SCV-cast v c)
scv-decidable (cv-pair cv₁ cv₂ p) = yes (SCV-pair cv₁ cv₂ p)

¬scv⇒Value : ∀ {Γ Σ A} {e : Σ ∣ Γ ⊢ A} {cv : DelayedCast e}
  → ¬ ReducibleDelayedCast cv → Value e
¬scv⇒Value {cv = v⇑ x} _ = x
¬scv⇒Value {cv = cast-val x c} ¬scv = ⊥-elim (¬scv (SCV-cast x c))
¬scv⇒Value {cv = cv-pair cv cv₁ p} ¬scv = ⊥-elim (¬scv (SCV-pair cv cv₁ p))
