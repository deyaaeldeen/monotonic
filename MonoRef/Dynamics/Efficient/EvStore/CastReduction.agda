module MonoRef.Dynamics.Efficient.EvStore.CastReduction where

open import MonoRef.Dynamics.Efficient.Coercions
open import MonoRef.Dynamics.Efficient.EvStore.Store
open import MonoRef.Dynamics.Efficient.EvStore.MonoCastReduction public
open import MonoRef.Dynamics.Efficient.TargetWithoutBlame


infix 3  _,_⟶_,_

{- Cast Reduction Rules -}

data _,_⟶_,_ {Γ Σ} : ∀ {Σ' A}
  → Σ  ∣ Γ ⊢ A → (ν  : Store Σ )
  → Σ' ∣ Γ ⊢ A → (ν' : Store Σ')
  → Set

⟶⟹⊑ₕ : ∀ {Γ Σ Σ' A} {M : Σ ∣ Γ ⊢ A} {ν : Store Σ} {M' : Σ' ∣ Γ ⊢ A} {ν' : Store Σ'}
  → M , ν ⟶ M' , ν'
  → Σ' ⊑ₕ Σ

data _,_⟶_,_ {Γ Σ} where

  pure : ∀ {A} {ν : Store Σ} {M' M : Σ ∣ Γ ⊢ A}
    → M ⟶ᵤᶜᵛ M'
      ----------------
    → M , ν ⟶ M' , ν

  mono : ∀ {Σ' A} {ν : Store Σ} {ν' : Store Σ'} {M : Σ ∣ Γ ⊢ A} {M' : Σ' ∣ Γ ⊢ A}
    → M , ν ⟶ₘ M' , ν'
      -----------------
    → M , ν ⟶ M' , ν'

  ξ-×ₗ : ∀ {Σ' A B} {ν : Store Σ} {ν' : Store Σ'} {e₁ : Σ ∣ Γ ⊢ A} {e₁' : Σ' ∣ Γ ⊢ A} {e₂ : Σ ∣ Γ ⊢ B}
    → (red : e₁ , ν ⟶ e₁' , ν')
      ----------------------------------------------------------------------------
    → _`×_ e₁ e₂ , ν ⟶ _`×_ e₁' (typeprecise-strenthen-expr (⟶⟹⊑ₕ red) e₂) , ν'

  ξ-×ᵣ : ∀ {Σ' A B} {ν : Store Σ} {ν' : Store Σ'} {e₁ : Σ ∣ Γ ⊢ A} {e₂ : Σ ∣ Γ ⊢ B} {e₂' : Σ' ∣ Γ ⊢ B}
    → (red : e₂ , ν ⟶ e₂' , ν')
      ----------------------------------------------------------------------------
    → _`×_ e₁ e₂ , ν ⟶ _`×_ (typeprecise-strenthen-expr (⟶⟹⊑ₕ red) e₁) e₂' , ν'

⟶⟹⊑ₕ (pure _) = ⊑ₕ-refl
⟶⟹⊑ₕ (mono red) = ⟶ₘ⟹⊑ₕ red
⟶⟹⊑ₕ (ξ-×ₗ red) = ⟶⟹⊑ₕ red
⟶⟹⊑ₕ (ξ-×ᵣ red) = ⟶⟹⊑ₕ red
