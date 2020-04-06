open import MonoRef.Static.Types

module MonoRef.Dynamics.Progress.StdStore
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set) where

open import Data.List using (List ; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (proj₁ ; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Nullary using (¬_ ; yes ; no)

open import MonoRef.Dynamics.Reduction.StdStore.StateReduction
  _⟹_ Inert
open import MonoRef.Dynamics.Reduction.StdStore.SuspendedCast
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Std.Precision.StoreValStrenthening
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Std.Store
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Std.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Std.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


module ParamStdStoreProgress/Pre
  (Value : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set) where

  open ParamSuspendedCast Value
  open ParamStateReduction/Pre Value

  module ParamStdStoreProgress
    (make-coercion : ∀ A B → A ⟹ B)
    (SimpleValue : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
    (ref⟹T : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → Type)
    (ref⟹∈ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ∈ Σ)
    (ref⟹⊑ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ⊑ A)
    (typeprecise-strenthen-val : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A} → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
      → Value v
      → Value (typeprecise-strenthen-expr Σ'⊑ₕΣ v))
    (apply-cast : ∀ {A B Σ Σ'}
      → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
      → (Q : List (SuspendedCast Σ))
      → ∀ {e : proj₁ (merge' Σ'⊑ₕΣ Q) ∣ ∅ ⊢ A} → (v : Value e)
      → A ⟹ B
      → CastResult Σ'⊑ₕΣ Q B) where

    open ParamStoreValue Value
    open ParamStoreDef StoreValue
    open ParamStore SimpleValue Value ref⟹T ref⟹∈ ref⟹⊑
    open ParamStateReduction make-coercion SimpleValue ref⟹T ref⟹∈ ref⟹⊑
      typeprecise-strenthen-val apply-cast

    data Progress {Σ Σ₁ T A}
      (Σ₁⊑ₕΣ : Σ₁ ⊑ₕ Σ)
      (A∈Σ : A ∈ Σ)
      (B : Type)
      (Q : List (SuspendedCast Σ))
      (M : proj₁ (merge' Σ₁⊑ₕΣ (cast A∈Σ B ∷ Q)) ∣ ∅ ⊢ T)
      (μ : Store (proj₁ (merge' Σ₁⊑ₕΣ (cast A∈Σ B ∷ Q))) Σ₁) : Set where

      step : ∀ {Σ₂} {Σ₂⊑ₕΣ₁ : Σ₂ ⊑ₕ Σ₁} {Q' : List (SuspendedCast Σ)}
               {N : (proj₁ (merge' (⊑ₕ-trans Σ₂⊑ₕΣ₁ Σ₁⊑ₕΣ) Q')) ∣ ∅ ⊢ T}
               {μ' : Store (proj₁ (merge' (⊑ₕ-trans Σ₂⊑ₕΣ₁ Σ₁⊑ₕΣ) Q')) Σ₂}
        → _,_,_⟶_,_,_ {A∈Σ = A∈Σ} {Σ₁⊑ₕΣ = Σ₁⊑ₕΣ} Q M μ {Σ₂⊑ₕΣ₁ = Σ₂⊑ₕΣ₁} Q' N μ'
          -----------------------------------------------------------------------
        → Progress Σ₁⊑ₕΣ A∈Σ B Q M μ

    suspended-cast-progress : ∀ {Σ Σ₁ T A}
      → (Σ₁⊑ₕΣ : Σ₁ ⊑ₕ Σ)
      → (A∈Σ : A ∈ Σ)
      → (B : Type)
      → (Q : List (SuspendedCast Σ))
      → ∀ {M : proj₁ (merge' Σ₁⊑ₕΣ (cast A∈Σ B ∷ Q)) ∣ ∅ ⊢ T}
      → (μ : Store (proj₁ (merge' Σ₁⊑ₕΣ (cast A∈Σ B ∷ Q))) Σ₁)
      → Progress Σ₁⊑ₕΣ A∈Σ B Q M μ
    suspended-cast-progress Σ₁⊑ₕΣ A∈Σ B Q μ
      with ∼-decidable (store-lookup-rtti (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ)) μ) B
    ... | no ¬rtti∼B = step (state/error2 ¬rtti∼B)
    ... | yes rtti∼B
        with ≡Type-decidable (⊓ rtti∼B) (store-lookup-rtti (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ)) μ)
    ...   | yes p = step (state/discard rtti∼B p)
    ...   | no ¬p
          with successful-μ-cast? (μ-cast Q A∈Σ B Σ₁⊑ₕΣ μ rtti∼B)
    ...     | inj₁ c = step (state/update-store rtti∼B ¬p c)
    ...     | inj₂ ¬c = step (state/error1 rtti∼B ¬p ¬c)
