module MonoRef.Dynamics.Efficient.Faithful.CastedValueProgress where

open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁ ; inj₂)

open import MonoRef.Dynamics.Efficient.Faithful.Coercions
open import MonoRef.Dynamics.Efficient.Faithful.Reduction
open import MonoRef.Dynamics.Efficient.Faithful.Store
open import MonoRef.Dynamics.Efficient.Faithful.TargetWithoutBlame
open import MonoRef.Dynamics.Efficient.Faithful.ActiveCastProgress


data StrongCastedValueProgress {Γ Σ A} (M : Σ ∣ Γ ⊢ A) (ν : Store Σ) : Set where

  step : ∀ {Σ'} {ν' : Store Σ'} {N : Σ' ∣ Γ ⊢ A}
    → M , ν ⟶ᵤᵣ N , ν'
      -----------------------------
    → StrongCastedValueProgress M ν

⟶ᵤᵣprogress-scv : ∀ {Γ Σ A} {e : Σ ∣ Γ ⊢ A} {cv : CastedValue e}
  → StrongCastedValue cv → (ν : Store Σ) → StrongCastedValueProgress e ν
⟶ᵤᵣprogress-scv (SCV-cast v ac) ν
  with ⟶ᵤᵣprogress-active/sv v ac ν
... | step-pure R = step (pure R)
... | step-mono R = step (mono R)
⟶ᵤᵣprogress-scv (SCV-pair _ _ p) ν
  with p
... | inj₂ (inj₁ ⟨ v₁ , scv₂ ⟩)
   with ⟶ᵤᵣprogress-scv scv₂ ν
...  | step scv₂⟶scv₂' = step (ξ-×ᵣ scv₂⟶scv₂')
⟶ᵤᵣprogress-scv (SCV-pair {e₂ = e₂} _ _ _) ν | inj₂ (inj₂ ⟨ scv₁ , _ ⟩)
   with ⟶ᵤᵣprogress-scv scv₁ ν
...  | step scv₁⟶scv₁' = step (ξ-×ₗ scv₁⟶scv₁')
⟶ᵤᵣprogress-scv (SCV-pair {e₂ = e₂} _ _ _) ν | inj₁ ⟨ scv₁ , _ ⟩
   with ⟶ᵤᵣprogress-scv scv₁ ν
...  | step scv₁⟶scv₁' = step (ξ-×ₗ scv₁⟶scv₁')
