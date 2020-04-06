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
open import Data.Product using (proj₁)

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
    (_,_,_⟶_,_,_ : ∀ {Σ T Σ₁ Σ₂ Σ₃} {Σ₁⊑ₕΣ : Σ₁ ⊑ₕ Σ} {Σ₃⊑ₕΣ₂ : Σ₃ ⊑ₕ Σ₂} →
    (Q  : List (SuspendedCast Σ)) →
    (M  : proj₁ (merge' Σ₁⊑ₕΣ Q) ∣ ∅ ⊢ T) →
    (μ  : Store (proj₁ (merge' Σ₁⊑ₕΣ Q)) Σ₁) → 
    (Q' : List (SuspendedCast Σ₂)) →
    (M' : proj₁ (merge' Σ₃⊑ₕΣ₂ Q') ∣ ∅ ⊢ T) →
    (μ' : Store (proj₁ (merge' Σ₃⊑ₕΣ₂ Q')) Σ₃) → Set) where

    data _,_,_↠_,_,_ {Σ Σ₁ A} {Σ₁⊑ₕΣ : Σ₁ ⊑ₕ Σ}
            (Q : List (SuspendedCast Σ))
            (M  : proj₁ (merge' Σ₁⊑ₕΣ Q) ∣ ∅ ⊢ A)
            (μ : Store (proj₁ (merge' Σ₁⊑ₕΣ Q)) Σ₁) : ∀ {Σ₂ Σ₃} {Σ₃⊑ₕΣ₂ : Σ₃ ⊑ₕ Σ₂}
          → (Q' : List (SuspendedCast Σ₂)) → (M' : proj₁ (merge' Σ₃⊑ₕΣ₂ Q') ∣ ∅ ⊢ A) → (μ' : Store (proj₁ (merge' Σ₃⊑ₕΣ₂ Q')) Σ₃)
          → Set where

       ↠-refl :
          ---------------------
          Q , M , μ ↠ Q , M , μ

       ↠-trans : ∀ {Σ₂ Σ₃ Σ₄ Σ₅} {Σ₃⊑ₕΣ₂ : Σ₃ ⊑ₕ Σ₂} {Σ₅⊑ₕΣ₄ : Σ₅ ⊑ₕ Σ₄}
                   {Q' : List (SuspendedCast Σ₂)} {Q'' :  List (SuspendedCast Σ₄)}
                   {μ' : Store (proj₁ (merge' Σ₃⊑ₕΣ₂ Q')) Σ₃}
                   {N : proj₁ (merge' Σ₃⊑ₕΣ₂ Q') ∣ ∅ ⊢ A}
                   {μ'' : Store (proj₁ (merge' Σ₅⊑ₕΣ₄ Q'')) Σ₅} {L : proj₁ (merge' Σ₅⊑ₕΣ₄ Q'') ∣ ∅ ⊢ A}
        → Q , M , μ ⟶ Q' , N , μ'
        → Q' , N , μ' ↠ Q'' , L , μ''
          ---------------------------
        → Q , M , μ ↠ Q'' , L , μ''
