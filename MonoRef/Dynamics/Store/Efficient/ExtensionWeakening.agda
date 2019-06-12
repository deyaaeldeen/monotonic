open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Efficient.ExtensionWeakening
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  (Active : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.Product renaming (map to prod-map)
open import Data.Sum renaming (map to sum-map)

-- standard library++
open import Data.List.Prefix using (_⊑_ ; ∈-⊒)

open import MonoRef.Dynamics.Store.Efficient.CastedValue
  _⟹_ Inert Active
open import MonoRef.Dynamics.Store.Extension
  _⟹_ Inert
open import MonoRef.Dynamics.Efficient.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert


prefix-weaken-val : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A} → (ext : Σ ⊑ Σ')
  → Value v → Value (prefix-weaken-expr ext v)

prefix-weaken-sval : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A} → (ext : Σ ⊑ Σ')
  → SimpleValue v → SimpleValue (prefix-weaken-expr ext v)
prefix-weaken-sval ext (V-ƛ N) = V-ƛ (prefix-weaken-expr ext N)
prefix-weaken-sval _   V-zero = V-zero
prefix-weaken-sval ext (V-suc v) = V-suc (prefix-weaken-val ext v)
prefix-weaken-sval _   V-unit = V-unit
prefix-weaken-sval ext (V-addr mem prec) = V-addr (∈-⊒ mem ext) prec 
prefix-weaken-sval ext (V-pair v v₁) =
  V-pair (prefix-weaken-val ext v) (prefix-weaken-val ext v₁)

prefix-weaken-val ext (S-Val sv) = S-Val (prefix-weaken-sval ext sv)
prefix-weaken-val ext (V-cast e c) = V-cast (prefix-weaken-sval ext e) c

prefix-weaken-cv : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A} → (ext : Σ ⊑ Σ')
  → CastedValue v
  → CastedValue (prefix-weaken-expr ext v)

prefix-weaken-scv : ∀ {Σ Σ' Γ A} {e : Σ ∣ Γ ⊢ A} {cv : CastedValue e}
  → (ext : Σ ⊑ Σ')
  → StrongCastedValue cv
  → StrongCastedValue (prefix-weaken-cv ext cv)

prefix-weaken-cv ext (v⇑ x) = v⇑ (prefix-weaken-val ext x)
prefix-weaken-cv ext (cast-val v c) = cast-val (prefix-weaken-sval ext v) c
prefix-weaken-cv ext (cast-cval v c d) = cast-cval (prefix-weaken-sval ext v) c d
prefix-weaken-cv ext (cv-pair cv cv₁ p) =
  cv-pair (prefix-weaken-cv ext cv) (prefix-weaken-cv ext cv₁)
    (sum-map (prod-map (prefix-weaken-scv ext) (prefix-weaken-val ext))
             (sum-map (prod-map (prefix-weaken-val ext) (prefix-weaken-scv ext))
                      (prod-map (prefix-weaken-scv ext) (prefix-weaken-scv ext))) p)

prefix-weaken-scv ext (SCV-cast v ac) =
  SCV-cast (prefix-weaken-sval ext v) ac
prefix-weaken-scv ext (SCV-ccast v c d) =
  SCV-ccast (prefix-weaken-sval ext v) c d
prefix-weaken-scv ext (SCV-pair cv₁ cv₂ p) =
  SCV-pair (prefix-weaken-cv ext cv₁) (prefix-weaken-cv ext cv₂)
    (sum-map (prod-map (prefix-weaken-scv ext) (prefix-weaken-val ext))
             (sum-map (prod-map (prefix-weaken-val ext) (prefix-weaken-scv ext))
                      (prod-map (prefix-weaken-scv ext) (prefix-weaken-scv ext))) p)
