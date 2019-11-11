{-

  MonoRef.Dynamics.Store.Evolving.Normal provides a definition for a normal store.

-}

open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Evolving.Normal
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.Empty using (⊥-elim)
open import Data.List.All using ([] ; _∷_)
open import Data.List.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product
  using (∃-syntax ; Σ ; Σ-syntax ; _×_ ; -,_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
open import Relation.Binary.PropositionalEquality using (refl)

open import MonoRef.Dynamics.Store.Evolving.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context


module ParamNormal
  (Value : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (valueP : ∀ {Σ A} → (e : Σ ∣ ∅ ⊢ A) → Dec (Value e))
  (DelayedCast : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  where

  open ParamStoreValue DelayedCast
  open ParamStoreDef StoreValue

  {- an evidence that a store does not contain any delayed casts i.e. a normal
  store -}
  
  data NormalStore {Σ} : ∀ {Σ'} → GenStore Σ Σ' → Set where
  
    NS-Z : NormalStore []
  
    NS-S : ∀ {Σ' A} {ν : GenStore Σ Σ'} {e : Σ ∣ ∅ ⊢ A} {t : Ty A}
      → NormalStore ν
      → (cv : DelayedCast e)
      → (V : Value e)
      → NormalStore (fromDelayedCast (intro cv t) ∷ ν)

  normalStoreP : ∀ {Σ Σ'} → (ν : GenStore Σ Σ') → Dec (NormalStore ν)
  normalStoreP [] = yes NS-Z
  normalStoreP (px ∷ ν)
    with normalStoreP ν
  normalStoreP (fromDelayedCast (intro {e = e} cv _) ∷ _) | yes p
      with valueP e
  ...   | yes p₁ = yes (NS-S p cv p₁)
  ...   | no ¬p = no (λ { (NS-S x cv V) → ¬p V})
  normalStoreP ν@(_ ∷ _) | no ¬p = no λ{ (NS-S x cv V) → ¬p x}

  ¬NormalStore⇒∃¬v : ∀ {Σ Σ'} {ν : GenStore Σ Σ'}
    → ¬ NormalStore ν
    → ∃[ A ] (A ∈ Σ' × (Σ[ e ∈ Σ ∣ ∅ ⊢ A ] ¬ Value e × DelayedCast e))
  ¬NormalStore⇒∃¬v {ν = []} x = ⊥-elim (x NS-Z)
  ¬NormalStore⇒∃¬v {ν = fromDelayedCast (intro {e = e} cv _) ∷ ν} x
    with valueP e
  ... | no ¬p = -, ⟨ here refl , -, ⟨ ¬p , cv ⟩ ⟩
  ... | yes v
      with normalStoreP ν
  ...   | yes p = ⊥-elim (x (NS-S p cv v))
  ...   | no ¬p
        with ¬NormalStore⇒∃¬v ¬p
  ...     | ⟨ _ , ⟨ A∈Σ , w ⟩ ⟩ = -, ⟨ there A∈Σ , w ⟩
