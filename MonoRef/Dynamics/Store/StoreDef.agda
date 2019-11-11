{-

  MonoRef.Dynamics.Store.StoreDef exports the definition of the store.

-}

open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.StoreDef
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.List.All using (All)
open import Data.List.Relation.Pointwise using (Pointwise ; _∷_)
open import Relation.Binary using (Rel)

open import MonoRef.Static.Types.Relations using (StoreTyping)


module ParamGenStoreDef
  (StoreValue : (A : Type) → (Σ : StoreTyping) → Set)
  where

  {- A more general version of the Store type. -}
  GenStore : (Σ Σ' : StoreTyping) → Set
  GenStore Σ Σ' = All (λ ty → StoreValue ty Σ) Σ'

  -- a modified version of pw-map where the relation is anti-symmetric and
  -- points left
  pw-map' : ∀ {a ℓ}{A : Set a}{_∼_ : Rel A ℓ} {l m p}{P : A → Set p}
    → (∀ {a b} → a ∼ b → P b → P a) → Pointwise _∼_ m l → All P l → All P m
  pw-map' f Pointwise.[] All.[] = All.[]
  pw-map' f (x∼y ∷ r) (px All.∷ xs) = f x∼y px All.∷ pw-map' f r xs
