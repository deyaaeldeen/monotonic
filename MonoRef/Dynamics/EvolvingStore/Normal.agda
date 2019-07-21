{-

  MonoRef.Dynamics.EvolvingStore.Normal provides a definition for a normal store.

-}

open import MonoRef.Static.Types

module MonoRef.Dynamics.EvolvingStore.Normal
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.Empty using (⊥)
open import Data.List.All using (All)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)

open import MonoRef.Dynamics.EvolvingStore.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.EvolvingStore.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context


module ParamNormal
  (Value             : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (CastedValue       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (StrongCastedValue : ∀ {Σ Γ A} {e : Σ ∣ Γ ⊢ A} → CastedValue e → Set)
  where

  open ParamStoreValue Value CastedValue StrongCastedValue
  open ParamStoreDef StoreValue

  {- an evidence that a store does not contain any casted values i.e. a normal
  store -}
  
  data NormalStore {Σ} : ∀ {Σ'} → StoreUnder Σ Σ' → Set where
  
    NS-Z : NormalStore All.[]
  
    NS-S : ∀ {Σ' A} {ν : StoreUnder Σ Σ'} {v : Σ ∣ ∅ ⊢ A} {t : Ty A}
      → NormalStore ν
      → (V : Value v)
      → NormalStore (fromNormalValue (intro V t) All.∷ ν)
  
    NS-S' : ∀ {Σ' A} {ν : StoreUnder Σ Σ'} {cv : Σ ∣ ∅ ⊢ A} {CV : CastedValue cv} {t : Ty A}
      → NormalStore ν
      → ¬ StrongCastedValue CV
      → NormalStore (fromCastedValue (intro CV t) All.∷ ν)

  module ParamNormalDecidable
    (scv-decidable : ∀ {Σ A} {e : Σ ∣ ∅ ⊢ A}
      → (cv : CastedValue e) → Dec (StrongCastedValue cv))
    where

    normalStoreP : ∀ {Σ Σ'} → (ν : StoreUnder Σ Σ') → Dec (NormalStore ν)
    normalStoreP All.[] = yes NS-Z
    normalStoreP (px All.∷ ν)
      with normalStoreP ν
    normalStoreP (fromNormalValue (intro x _) All.∷ _) | yes p = yes (NS-S p x)
    normalStoreP (fromCastedValue (intro cv _) All.∷ _) | yes p
      with scv-decidable cv
    ... | yes SCV = no (λ { (NS-S' x ¬SCV) → ¬SCV SCV})
    ... | no ¬SCV = yes (NS-S' p ¬SCV)
    normalStoreP ν@(_ All.∷ _) | no ¬p = no helper
      where helper : NormalStore ν → ⊥
            helper (NS-S x _) = ¬p x
            helper (NS-S' x _) = ¬p x
