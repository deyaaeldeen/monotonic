{-

  MonoRef.Dynamics.Store.Evolving.Simple instantiates
  MonoRef.Dynamics.Store.Evolving.Base with the right simple (space-inefficient)
  definitions and re-exports all store definitions. It is paramaterized by the
  semantics of coercions.

-}

open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)

open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Evolving.Simple
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  (inertP : ∀ {A B} → (c : A ⟹ B) → Dec (Inert c))
  (make-coercion : ∀ A B → A ⟹ B)
  (Inert⇒¬Ref : ∀ {A B} {c : A ⟹ Ref B} → Inert c → ⊥)
  where

open import MonoRef.Dynamics.Simple.Common.Value
  _⟹_ Inert
open import MonoRef.Dynamics.Simple.Common.Value.Properties
  _⟹_ Inert inertP
open import MonoRef.Dynamics.Store.Evolving.Base
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.Normal
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert public
open import MonoRef.Dynamics.Store.Ptr public
open import MonoRef.Dynamics.Store.Evolving.Simple.DelayedCast
  _⟹_ Inert public
open import MonoRef.Dynamics.Store.Evolving.Simple.ExtensionWeakening
  _⟹_ Inert public
open import MonoRef.Dynamics.Store.Evolving.Simple.PrecisionStrenthening
  _⟹_ Inert public
open import MonoRef.Dynamics.Store.Evolving.Store
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Simple.Utilities
  _⟹_ Inert Inert⇒¬Ref public
open import MonoRef.Dynamics.Store.Evolving.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


open ParamStoreValue DelayedCast public
open ParamStoreDef StoreValue public
open ParamStore Value Value DelayedCast v⇑_ ref⟹T ref⟹∈ ref⟹⊑ public
open ParamNormal Value valueP DelayedCast public


ν-update/ref : ∀ {Σ Γ}
  → (A : Type) → {r : Σ ∣ Γ ⊢ Ref A} → (R : Value r) → Store Σ → ∀ {e : Σ ∣ ∅ ⊢ A} → Value e → Store Σ
ν-update/ref T R ν v =
  ν-update (ref-ν⟹∈ R ν) ν (cast-val (v⇑_ v) (make-coercion T (store-lookup-rtti/ref R ν)))

private

  {-

    all-⊑ₕ does the second step in the process of casting a store. It strenthens
    the store typing given that all elements are already strenthened.

  -}

  all-⊑ₕ : ∀ {Σ Σ' : StoreTyping} → GenStore Σ' Σ → Σ' ⊑ₕ Σ → GenStore Σ' Σ'
  all-⊑ₕ ν prec = pw-map' update-type prec ν
    where

      update-type : ∀ {A B Σ} → B ⊑ A → StoreValue A Σ → StoreValue B Σ
      update-type {A}{B} B⊑A (fromDelayedCast (intro cv _)) =
        fromDelayedCast (intro (cast-val cv (make-coercion A B)) (Type⇑ _))

{- Re-exported concrete definitions -}

open ParamBase Value Value DelayedCast v⇑_ ref⟹T ref⟹∈ ref⟹⊑
open StoreExtend prefix-weaken-cv public
open Corollary1 typeprecise-strenthen-cv all-⊑ₕ public

open import MonoRef.Dynamics.Store.TypingProgress
  _⟹_ Inert public
