open import MonoRef.Static.Types

module MonoRef.Dynamics.EvolvingStore.Simple.PrecisionStrenthening
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  (Active : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.Product renaming (_,_ to ⟨_,_⟩ ; map to prod-map)
open import Data.Sum renaming (map to sum-map)

open import MonoRef.Dynamics.EvolvingStore.Simple.DelayedCast
  _⟹_ Inert Active
open import MonoRef.Dynamics.EvolvingStore.Precision
  _⟹_ Inert
open import MonoRef.Dynamics.Simple.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Types.Relations


typeprecise-strenthen-val : ∀ {Σ Σ' Γ A} {e : Σ ∣ Γ ⊢ A}
  → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ) → Value e → Value (typeprecise-strenthen-expr Σ'⊑ₕΣ e)
typeprecise-strenthen-val Σ'⊑ₕΣ (V-ƛ N) =
  V-ƛ (typeprecise-strenthen-expr Σ'⊑ₕΣ N)
typeprecise-strenthen-val Σ'⊑ₕΣ (V-cast e c) =
  V-cast (typeprecise-strenthen-val Σ'⊑ₕΣ e) c
typeprecise-strenthen-val _     V-zero = V-zero
typeprecise-strenthen-val Σ'⊑ₕΣ (V-suc v) =
  V-suc (typeprecise-strenthen-val Σ'⊑ₕΣ v)
typeprecise-strenthen-val _     V-unit = V-unit
typeprecise-strenthen-val Σ'⊑ₕΣ (V-addr mem prec') with ∈⇒⊑ₕ∈ Σ'⊑ₕΣ mem
... | ⟨ _ ,  tt'∈prec ⟩ = V-addr (⊑ₕ∈⇒∈ tt'∈prec) (⊑-trans (⊒-⊒ₕ tt'∈prec) prec')
typeprecise-strenthen-val Σ'⊑ₕΣ (V-pair v v₁) =
  V-pair (typeprecise-strenthen-val Σ'⊑ₕΣ v)
         (typeprecise-strenthen-val Σ'⊑ₕΣ v₁)


typeprecise-strenthen-cv : ∀ {Σ Σ' Γ A} {e : Σ ∣ Γ ⊢ A}
  → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
  → DelayedCast e
  → DelayedCast (typeprecise-strenthen-expr Σ'⊑ₕΣ e)

typeprecise-strenthen-scv : ∀ {Σ Σ' Γ A} {e : Σ ∣ Γ ⊢ A} {cv : DelayedCast e}
  → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
  → ReducibleDelayedCast cv
  → ReducibleDelayedCast (typeprecise-strenthen-cv Σ'⊑ₕΣ cv)

typeprecise-strenthen-cv Σ'⊑ₕΣ (v⇑ x) = v⇑ typeprecise-strenthen-val Σ'⊑ₕΣ x
typeprecise-strenthen-cv Σ'⊑ₕΣ (cast-val v c) =
  cast-val (typeprecise-strenthen-val Σ'⊑ₕΣ v) c
typeprecise-strenthen-cv Σ'⊑ₕΣ (cast-cval cv p c) =
  cast-cval (typeprecise-strenthen-cv Σ'⊑ₕΣ cv) (typeprecise-strenthen-scv Σ'⊑ₕΣ p) c
typeprecise-strenthen-cv Σ'⊑ₕΣ (cv-pair cv cv₁ p) =
  cv-pair (typeprecise-strenthen-cv Σ'⊑ₕΣ cv)
          (typeprecise-strenthen-cv Σ'⊑ₕΣ cv₁)
          (sum-map (prod-map (typeprecise-strenthen-scv Σ'⊑ₕΣ) (typeprecise-strenthen-val Σ'⊑ₕΣ))
             (sum-map (prod-map (typeprecise-strenthen-val Σ'⊑ₕΣ) (typeprecise-strenthen-scv Σ'⊑ₕΣ))
                      (prod-map (typeprecise-strenthen-scv Σ'⊑ₕΣ) (typeprecise-strenthen-scv Σ'⊑ₕΣ))) p)

typeprecise-strenthen-scv Σ'⊑ₕΣ (SCV-cast v ac) =
  SCV-cast (typeprecise-strenthen-val Σ'⊑ₕΣ v) ac
typeprecise-strenthen-scv Σ'⊑ₕΣ (SCV-ccast cv p c) =
  SCV-ccast (typeprecise-strenthen-cv Σ'⊑ₕΣ cv) (typeprecise-strenthen-scv Σ'⊑ₕΣ p) c
typeprecise-strenthen-scv Σ'⊑ₕΣ (SCV-pair cv₁ cv₂ p) =
  SCV-pair (typeprecise-strenthen-cv Σ'⊑ₕΣ cv₁)
           (typeprecise-strenthen-cv Σ'⊑ₕΣ cv₂)
           (sum-map (prod-map (typeprecise-strenthen-scv Σ'⊑ₕΣ) (typeprecise-strenthen-val Σ'⊑ₕΣ))
             (sum-map (prod-map (typeprecise-strenthen-val Σ'⊑ₕΣ) (typeprecise-strenthen-scv Σ'⊑ₕΣ))
                      (prod-map (typeprecise-strenthen-scv Σ'⊑ₕΣ) (typeprecise-strenthen-scv Σ'⊑ₕΣ))) p)
