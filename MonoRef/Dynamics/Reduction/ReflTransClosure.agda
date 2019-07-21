{-

  MonoRef.Dynamics.Reduction.ReflTransClosure provides the reflexive transitive
  closure of the reduction relation.

-}

open import MonoRef.Static.Types

module MonoRef.Dynamics.Reduction.ReflTransClosure
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import MonoRef.Dynamics.EvolvingStore.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.EvolvingStore.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context


module ParamReflTransClosure
  (Value             : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (CastedValue       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (StrongCastedValue : ∀ {Σ Γ A} {e : Σ ∣ Γ ⊢ A} → CastedValue e → Set)
  where

  open ParamStoreValue Value CastedValue StrongCastedValue
  open ParamStoreDef StoreValue

  module ParamReflTransClosure/⟶ₛ
    (_,_⟶ₛ_,_ : ∀ {Σ A}
      → (M  : Σ  ∣ ∅ ⊢ A)   (ν  : Store Σ ) → ∀ {Σ'}
      → (M' : Σ' ∣ ∅ ⊢ A) → (ν' : Store Σ')
      → Set) where

    data _,_↠_,_ {Σ A}
            (M  : Σ  ∣ ∅ ⊢ A)   (ν  : Store Σ ) : ∀ {Σ'}
          → (M' : Σ' ∣ ∅ ⊢ A) → (ν' : Store Σ')
          → Set where

       ↠-refl :
          -------------
          M , ν ↠ M , ν

       ↠-trans : ∀ {Σ' Σ''} {ν' : Store Σ'} {N : Σ' ∣ ∅ ⊢ A} {ν'' : Store Σ''} {L : Σ'' ∣ ∅ ⊢ A}
        → M , ν ⟶ₛ N , ν'
        → N , ν' ↠ L , ν''
          ----------------
        → M , ν ↠ L , ν''
