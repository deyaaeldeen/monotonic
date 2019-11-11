{-

  MonoRef.Dynamics.Reduction.ReflTransClosure provides the reflexive transitive
  closure of the reduction relation.

-}

open import MonoRef.Static.Types

module MonoRef.Dynamics.Reduction.EvolvingStore.ReflTransClosure
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import MonoRef.Dynamics.Store.Evolving.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context


module ParamReflTransClosure
  (Value             : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (DelayedCast       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  where

  open ParamStoreValue DelayedCast
  open ParamStoreDef StoreValue

  module ParamReflTransClosure/⟶
    (_,_⟶_,_ : ∀ {Σ A}
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
        → M , ν ⟶ N , ν'
        → N , ν' ↠ L , ν''
          ----------------
        → M , ν ↠ L , ν''
