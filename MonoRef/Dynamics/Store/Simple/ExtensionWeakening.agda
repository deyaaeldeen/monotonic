open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Simple.ExtensionWeakening
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  (Active : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.Product renaming (map to prod-map)
open import Data.Sum renaming (map to sum-map)

-- standard library++
open import Data.List.Prefix using (_⊑_ ; ∈-⊒)

open import MonoRef.Dynamics.Store.Simple.CastedValue
  _⟹_ Inert Active
open import MonoRef.Dynamics.Store.Extension
  _⟹_ Inert
open import MonoRef.Dynamics.Simple.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert


prefix-weaken-val : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A}
  → (Σ⊑Σ' : Σ ⊑ Σ') → Value v → Value (prefix-weaken-expr Σ⊑Σ' v)
prefix-weaken-val Σ⊑Σ' (V-ƛ N) = V-ƛ (prefix-weaken-expr Σ⊑Σ' N)
prefix-weaken-val Σ⊑Σ' (V-cast e c) = V-cast (prefix-weaken-val Σ⊑Σ' e) c
prefix-weaken-val _    V-zero = V-zero
prefix-weaken-val Σ⊑Σ' (V-suc v) = V-suc (prefix-weaken-val Σ⊑Σ' v)
prefix-weaken-val _    V-unit = V-unit
prefix-weaken-val Σ⊑Σ' (V-addr mem p) = V-addr (∈-⊒ mem Σ⊑Σ') p
prefix-weaken-val Σ⊑Σ' (V-pair v v₁) =
  V-pair (prefix-weaken-val Σ⊑Σ' v) (prefix-weaken-val Σ⊑Σ' v₁)

prefix-weaken-cv : ∀ {Σ Σ' Γ A} {e : Σ ∣ Γ ⊢ A}
  → (Σ⊑Σ' : Σ ⊑ Σ') → CastedValue e → CastedValue (prefix-weaken-expr Σ⊑Σ' e)

prefix-weaken-scv : ∀ {Σ Σ' Γ A} {e : Σ ∣ Γ ⊢ A} {cv : CastedValue e}
  → (Σ⊑Σ' : Σ ⊑ Σ')
  → StrongCastedValue cv
  → StrongCastedValue (prefix-weaken-cv Σ⊑Σ' cv)

prefix-weaken-cv Σ⊑Σ' (v⇑ x) = v⇑ (prefix-weaken-val Σ⊑Σ' x)
prefix-weaken-cv Σ⊑Σ' (cast-val v c) = cast-val (prefix-weaken-val Σ⊑Σ' v) c
prefix-weaken-cv Σ⊑Σ' (cast-cval cv p c) =
  cast-cval (prefix-weaken-cv Σ⊑Σ' cv) (prefix-weaken-scv Σ⊑Σ' p) c
prefix-weaken-cv Σ⊑Σ' (cv-pair cv cv₁ p) =
  cv-pair (prefix-weaken-cv Σ⊑Σ' cv) (prefix-weaken-cv Σ⊑Σ' cv₁)
    (sum-map (prod-map (prefix-weaken-scv Σ⊑Σ') (prefix-weaken-val Σ⊑Σ'))
             (sum-map (prod-map (prefix-weaken-val Σ⊑Σ') (prefix-weaken-scv Σ⊑Σ'))
                      (prod-map (prefix-weaken-scv Σ⊑Σ') (prefix-weaken-scv Σ⊑Σ'))) p)

prefix-weaken-scv Σ⊑Σ' (SCV-cast v ac) =
  SCV-cast (prefix-weaken-val Σ⊑Σ' v) ac
prefix-weaken-scv Σ⊑Σ' (SCV-ccast cv p ac) =
  SCV-ccast (prefix-weaken-cv Σ⊑Σ' cv) (prefix-weaken-scv Σ⊑Σ' p) ac
prefix-weaken-scv Σ⊑Σ' (SCV-pair cv₁ cv₂ p) =
  SCV-pair (prefix-weaken-cv Σ⊑Σ' cv₁) (prefix-weaken-cv Σ⊑Σ' cv₂)
    (sum-map (prod-map (prefix-weaken-scv Σ⊑Σ') (prefix-weaken-val Σ⊑Σ'))
             (sum-map (prod-map (prefix-weaken-val Σ⊑Σ') (prefix-weaken-scv Σ⊑Σ'))
                      (prod-map (prefix-weaken-scv Σ⊑Σ') (prefix-weaken-scv Σ⊑Σ'))) p)
