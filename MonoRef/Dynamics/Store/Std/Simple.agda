{-

  MonoRef.Dynamics.Store.Std.Simple instantiates MonoRef.Dynamics.Store.Std.Base with
  the right efficient definitions and re-exports all store definitions. It is
  paramaterized by the semantics of coercions and requires a compose operator.

-}

open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec ; ¬_)

open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations

module MonoRef.Dynamics.Store.Std.Simple
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  (Inert⇒¬Ref : ∀ {A B} {c : A ⟹ Ref B} → Inert c → ⊥)
  where

open import MonoRef.Dynamics.Simple.Common.Value
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Std.Base
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Simple.Utilities
  _⟹_ Inert Inert⇒¬Ref public
open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert public
open import MonoRef.Dynamics.Store.Simple.ExtensionWeakening
  _⟹_ Inert public
open import MonoRef.Dynamics.Store.Simple.PrecisionStrenthening
  _⟹_ Inert public
open import MonoRef.Dynamics.Store.Std.Precision.StoreValStrenthening
  _⟹_ Inert public
open import MonoRef.Dynamics.Store.Ptr public
open import MonoRef.Dynamics.Store.Std.Store
  _⟹_ Inert public
open import MonoRef.Dynamics.Store.Std.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Std.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert


open ParamStoreValue Value public
open ParamStoreDef StoreValue public
open ParamStore Value Value ref⟹T ref⟹∈ ref⟹⊑ public

{- Re-exported concrete definitions -}

open ParamBase Value Value ref⟹T ref⟹∈ ref⟹⊑
open StoreExtend prefix-weaken-val public
open ParamPrecisionStoreValStrenthening Value typeprecise-strenthen-val public

open import MonoRef.Dynamics.Store.TypingProgress
  _⟹_ Inert public
