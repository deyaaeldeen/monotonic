{-

  MonoRef.Dynamics.Reduction.ReflTransClosure provides the reflexive transitive
  closure of the reduction relation.

-}

open import MonoRef.Static.Types

module MonoRef.Dynamics.Reduction.StdStore.ReflTransClosure
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.List using (List)

open import MonoRef.Dynamics.Reduction.StdStore.SuspendedCast
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Std.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Std.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context


module ParamReflTransClosure
  (Value : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  where

  open ParamStoreValue Value
  open ParamStoreDef StoreValue

  module ParamReflTransClosure/⟶
    (_,_,_⟶_,_,_ : ∀ {Σ Σ₂ Σ₃ Σ₄ Σ₅ A}
      → List (SuspendedCast Σ) → (M  : Σ₃  ∣ ∅ ⊢ A) → (μ  : Store Σ₃ Σ₂)
      → List (SuspendedCast Σ) → (M' : Σ₅ ∣ ∅ ⊢ A) → (μ' : Store Σ₅ Σ₄)
      → Set) where

    data _,_,_↠_,_,_ {Σ Σ₂ Σ₃ A}
            (Q : List (SuspendedCast Σ)) (M  : Σ₃ ∣ ∅ ⊢ A) (μ : Store Σ₃ Σ₂) : ∀ {Σ₄ Σ₅}
          → List (SuspendedCast Σ) → (M' : Σ₅ ∣ ∅ ⊢ A) → (μ' : Store Σ₅ Σ₄)
          → Set where

       ↠-refl :
          ---------------------
          Q , M , μ ↠ Q , M , μ

       ↠-trans : ∀ {Σ₄ Σ₅ Σ₆ Σ₇} {μ' : Store Σ₅ Σ₄} {N : Σ₅ ∣ ∅ ⊢ A} {μ'' : Store Σ₇ Σ₆} {L : Σ₇ ∣ ∅ ⊢ A}
         {Q' : List (SuspendedCast Σ)} {Q'' :  List (SuspendedCast Σ)}
        → Q , M , μ ⟶ Q' , N , μ'
        → Q' , N , μ' ↠ Q'' , L , μ''
          ---------------------------
        → Q , M , μ ↠ Q'' , L , μ''
