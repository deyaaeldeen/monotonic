{-

  MonoRef.Dynamics.Store.Evolving.Efficient instantiates MonoRef.Dynamics.Store.Evolving.Base with
  the right efficient definitions and re-exports all store definitions. It is
  paramaterized by the semantics of coercions and requires a compose operator.

-}

open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)

open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations

module MonoRef.Dynamics.Store.Evolving.Efficient
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  (inertP : ∀ {A B} → (c : A ⟹ B) → Dec (Inert c))
  (make-coercion : ∀ A B → A ⟹ B)
  (compose : ∀ {A B C} → A ⟹ B → B ⟹ C → A ⟹ C)
  where

open import Data.Product
  using (Σ ; Σ-syntax ; -,_) renaming (_,_ to ⟨_,_⟩)

open import MonoRef.Dynamics.Efficient.Common.Value
  _⟹_ Inert
open import MonoRef.Dynamics.Efficient.Common.Value.Properties
  _⟹_ Inert inertP
open import MonoRef.Dynamics.Store.Evolving.Base
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Efficient.Utilities
  _⟹_ Inert public
open import MonoRef.Dynamics.Store.Evolving.Normal
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert public
open import MonoRef.Dynamics.Store.Evolving.Efficient.DelayedCast
  _⟹_ Inert public
open import MonoRef.Dynamics.Store.Evolving.Efficient.ExtensionWeakening
  _⟹_ Inert public
open import MonoRef.Dynamics.Store.Evolving.Efficient.PrecisionStrenthening
  _⟹_ Inert public
open import MonoRef.Dynamics.Store.Ptr public
open import MonoRef.Dynamics.Store.Evolving.Store
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Evolving.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context


open ParamStoreValue DelayedCast public
open ParamStoreDef StoreValue public
open ParamStore
  SimpleValue Value DelayedCast v⇑_ ref⟹T ref⟹∈ ref⟹⊑ public
open ParamNormal Value valueP DelayedCast public

private

  {-

    all-⊑ₕ does the second step in the process of casting a store. It strenthens
    the store typing given that all elements are already strenthened.

  -}

  all-⊑ₕ : ∀ {Σ Σ'} → GenStore Σ' Σ → Σ' ⊑ₕ Σ → Store Σ'
  all-⊑ₕ ν Σ'⊑ₕΣ = pw-map' update-type Σ'⊑ₕΣ ν
    where
      cast-casted-value : ∀ {A B Σ} {e : Σ ∣ ∅ ⊢ A}
        → B ⊑ A → DelayedCast e → Σ[ e' ∈ Σ ∣ ∅ ⊢ B ] DelayedCast e'
      cast-casted-value {A}{B} _ (v⇑ v)
        with v
      ... | V-cast {c = c} sv _
         with inertP (compose c (make-coercion A B))
      ...  | yes c-inert = -, v⇑ (V-cast sv c-inert)
      ...  | no c-¬inert = -, cast-val sv (compose c (make-coercion A B))
      cast-casted-value {A}{B} _ _ | S-Val sv
         with inertP (make-coercion A B)
      ...  | yes c-inert = -, v⇑ (V-cast sv c-inert)
      ...  | no c-¬inert = -, cast-val sv (make-coercion A B)
      cast-casted-value {A}{B} _ (cast-val sv c)
        with inertP (compose c (make-coercion A B))
      ...  | yes c-inert = -, v⇑ (V-cast sv c-inert)
      ...  | no c-¬inert = -, cast-val sv (compose c (make-coercion A B))
      cast-casted-value (⊑-refl _) cv@(cv-pair _ _) = -, cv
      cast-casted-value (⊑-× ext1 ext2) (cv-pair cv₁ cv₂)
        with cast-casted-value ext1 cv₁ | cast-casted-value ext2 cv₂
      ... | ⟨ _ , a ⟩ | ⟨ _ , b ⟩ = -, cv-pair a b

      update-type : ∀ {A B Σ} → B ⊑ A → StoreValue A Σ → StoreValue B Σ
      update-type B⊑A (fromDelayedCast (intro cv _))
        with cast-casted-value B⊑A cv
      ... | ⟨ _ , cv' ⟩ = fromDelayedCast (intro cv' (Type⇑ _))

ν-update/ref : ∀ {Σ Γ}
  → (A : Type) → {r : Σ ∣ Γ ⊢ Ref A} → (R : SimpleValue r) → Store Σ → ∀ {e : Σ ∣ ∅ ⊢ A} → Value e → Store Σ
ν-update/ref T R ν v
  with v
... | V-cast {c = c} sv _
   with inertP (compose c (make-coercion T (store-lookup-rtti/ref R ν)))
...  | yes c-inert = μ-update (ref-ν⟹∈ R ν) ν (V-cast sv c-inert)
...  | no c-¬inert = ν-update (ref-ν⟹∈ R ν) ν (cast-val sv (compose c (make-coercion T (store-lookup-rtti/ref R ν))))
ν-update/ref T R ν v | S-Val sv
   with inertP (make-coercion T (store-lookup-rtti/ref R ν))
...  | yes c-inert = μ-update (ref-ν⟹∈ R ν) ν (V-cast sv c-inert)
...  | no c-¬inert = ν-update (ref-ν⟹∈ R ν) ν (cast-val sv (make-coercion T (store-lookup-rtti/ref R ν)))

{- Re-exported concrete definitions -}

open ParamBase SimpleValue Value DelayedCast v⇑_ ref⟹T ref⟹∈ ref⟹⊑
open StoreExtend prefix-weaken-cv public
open Corollary1 typeprecise-strenthen-cv all-⊑ₕ public

open import MonoRef.Dynamics.Store.TypingProgress
  _⟹_ Inert public
