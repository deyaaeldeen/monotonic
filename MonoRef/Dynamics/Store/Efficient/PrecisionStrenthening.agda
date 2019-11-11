open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Efficient.PrecisionStrenthening
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.Product renaming (_,_ to ⟨_,_⟩)

open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Dynamics.Efficient.Common.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Types.Relations


typeprecise-strenthen-val : ∀ {Σ Σ' Γ A} {e : Σ ∣ Γ ⊢ A} → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
  → Value e
  → Value (typeprecise-strenthen-expr Σ'⊑ₕΣ e)

typeprecise-strenthen-sval : ∀ {Σ Σ' Γ A} {e : Σ ∣ Γ ⊢ A} → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
  → SimpleValue e
  → SimpleValue (typeprecise-strenthen-expr Σ'⊑ₕΣ e)
typeprecise-strenthen-sval Σ'⊑ₕΣ (V-ƛ N) =
  V-ƛ (typeprecise-strenthen-expr Σ'⊑ₕΣ N)
typeprecise-strenthen-sval _    V-zero = V-zero
typeprecise-strenthen-sval Σ'⊑ₕΣ (V-suc v) =
  V-suc (typeprecise-strenthen-val Σ'⊑ₕΣ v)
typeprecise-strenthen-sval _    V-unit = V-unit
typeprecise-strenthen-sval Σ'⊑ₕΣ (V-addr mem prec') with ∈⇒⊑ₕ∈ Σ'⊑ₕΣ mem
... | ⟨ _ ,  tt'∈prec ⟩ = V-addr (⊑ₕ∈⇒∈ tt'∈prec) (⊑-trans (⊒-⊒ₕ tt'∈prec) prec')
typeprecise-strenthen-sval Σ'⊑ₕΣ (V-pair v v₁) =
  V-pair (typeprecise-strenthen-val Σ'⊑ₕΣ v)
         (typeprecise-strenthen-val Σ'⊑ₕΣ v₁)

typeprecise-strenthen-val Σ'⊑ₕΣ (S-Val sv) =
  S-Val (typeprecise-strenthen-sval Σ'⊑ₕΣ sv)
typeprecise-strenthen-val Σ'⊑ₕΣ (V-cast e c) =
  V-cast (typeprecise-strenthen-sval Σ'⊑ₕΣ e) c
