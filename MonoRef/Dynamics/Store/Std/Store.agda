{-

  MonoRef.Dynamics.Store.Std.Store exports various tools to work stores
  parameterized over the representation of values and casted values.

-}

open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Std.Store
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.AVL.IndexedMap using ()
open import Data.List using (List)
open import Data.List.Any using (here; there)
open import Data.List.All using (All ; lookup ; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (∃-syntax ; Σ-syntax ; _×_ ; -,_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; subst)

-- stdlib++
open import Data.List.All.Properties.Extra using (_All[_]≔'_)

open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Std.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Std.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


module ParamStore
  (SimpleValue : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (Value : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)

  {- These utilities depend on the definition of Value -}
  (ref⟹T : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → Type)
  (ref⟹∈ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ∈ Σ)
  (ref⟹⊑ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ⊑ A)
  where

  open ParamStoreValue Value
  open ParamStoreDef StoreValue

  ref-static-type : ∀ {Σ Γ A} {r : Σ ∣ Γ ⊢ Ref A}
    → (R : SimpleValue r) → static A → ref⟹T R ≡ A
  ref-static-type R static-A = ⊑-respect-static (ref⟹⊑ R) static-A

  lookup-store : ∀ {Σ Σ' A} → A ∈ Σ → Store Σ' Σ → StoreValue A Σ'
  lookup-store A∈Σ μ = lookup μ A∈Σ

  update-store : ∀ {Σ Σ' A} → A ∈ Σ → StoreValue A Σ' → Store Σ' Σ → Store Σ' Σ
  update-store ptr v μ = μ All[ ptr ]≔' v

  store-lookup-v : ∀ {Σ Σ' A} → A ∈ Σ → Store Σ' Σ → Σ' ∣ ∅ ⊢ A
  store-lookup-v A∈Σ ν with lookup-store A∈Σ ν
  ... | intro {V = V} _ _ = V

  store-lookup-val : ∀ {Σ Σ' A} → A ∈ Σ → Store Σ' Σ → Σ[ e ∈ Σ' ∣ ∅ ⊢ A ] Value e
  store-lookup-val A∈Σ ν with lookup-store A∈Σ ν
  ... | intro v _ = -, v

  store-lookup-v/ref : ∀ {Σ Σ' Γ A} {r : Σ ∣ Γ ⊢ Ref A}
    → (R : SimpleValue r) → Store Σ' Σ → Σ' ∣ ∅ ⊢ ref⟹T R
  store-lookup-v/ref R ν = store-lookup-v (ref⟹∈ R) ν

  store-lookup-rtti : ∀ {Σ Σ' A} → A ∈ Σ → Store Σ' Σ → Type
  store-lookup-rtti A∈Σ ν with lookup-store A∈Σ ν
  ... | intro _ ty = Ty⇓ ty

  store-lookup-rtti/ref : ∀ {Σ Σ' Γ T} {r : Σ ∣ Γ ⊢ Ref T}
    → (R : SimpleValue r) → Store Σ' Σ → Type
  store-lookup-rtti/ref R ν = store-lookup-rtti (ref⟹∈ R) ν

  μ-static-lookup : ∀ {Σ Σ' Γ A} {r : Σ ∣ Γ ⊢ Ref A}
    → (R : SimpleValue r) → static A → Store Σ' Σ → Σ' ∣ ∅ ⊢ A
  μ-static-lookup r x ν
    with ref⟹T r | ref-static-type r x | store-lookup-v/ref r ν
  ... | _ | refl | res = res

  μ-static-update : ∀ {Σ A} {r : Σ ∣ ∅ ⊢ Ref A}
    → (R : SimpleValue r)
    → static A
    → Store Σ Σ
    → ∀ {v : Σ ∣ ∅ ⊢ A}
    → Value v
    → Store Σ Σ
  μ-static-update R x μ v =
    update-store (ref⟹∈ R) (subst (λ x₁ → x₁) (helper R x) (intro v (Type⇑ _))) μ
     where
       helper : ∀ {Σ Γ B} {r : Σ ∣ Γ ⊢ Ref B}
         → (R : SimpleValue r)
         → static B
         → StoreValue B Σ ≡ StoreValue (ref⟹T R) Σ
       helper r x rewrite ref-static-type r x = refl

  μ-update : ∀ {Σ Σ' A} 
    → A ∈ Σ 
    → Store Σ' Σ
    → ∀ {e : Σ' ∣ ∅ ⊢ A}
    → Value e
    → Store Σ' Σ
  μ-update A∈Σ ν v = update-store A∈Σ (intro v (Type⇑ _)) ν

  mem-rtti-preserves-Σ : ∀ {Σ Σ' A}
    → (A∈Σ : A ∈ Σ)
    → (ν : Store Σ' Σ)
    → (store-lookup-rtti A∈Σ ν) ≡ A
  mem-rtti-preserves-Σ A∈Σ ν
    with lookup-store A∈Σ ν
  ... | intro _ _ = refl

  ref-rtti-preserves-Σ : ∀ {Σ Σ' Γ A} {r : Σ ∣ Γ ⊢ Ref A}
    → (R : SimpleValue r)
    → (ν : Store Σ' Σ)
    → (store-lookup-rtti/ref R ν) ≡ (ref⟹T R)
  ref-rtti-preserves-Σ R ν = mem-rtti-preserves-Σ (ref⟹∈ R) ν

  ref-ν⟹∈ : ∀ {Σ Σ' Γ T} {v : Σ ∣ Γ ⊢ Ref T}
    → (R : SimpleValue v) → (ν : Store Σ' Σ) → store-lookup-rtti/ref R ν ∈ Σ
  ref-ν⟹∈ R ν rewrite (ref-rtti-preserves-Σ R ν) = ref⟹∈ R

  rtti∈ : ∀ {Σ Σ' A} → (A∈Σ : A ∈ Σ) → (ν : Store Σ' Σ) → store-lookup-rtti A∈Σ ν ∈ Σ
  rtti∈ A∈Σ ν rewrite mem-rtti-preserves-Σ A∈Σ ν = A∈Σ

  ref-ν⟹⊑ : ∀ {Σ Σ' Γ T} {v : Σ ∣ Γ ⊢ Ref T}
    → (R : SimpleValue v) → (ν : Store Σ' Σ) → store-lookup-rtti/ref R ν ⊑ T
  ref-ν⟹⊑ R ν rewrite (ref-rtti-preserves-Σ R ν) = ref⟹⊑ R

  insert/cast-μ : ∀ {Σ Σ' A B} {e : Σ' ∣ ∅ ⊢ B}
    → (A∈Σ : A ∈ Σ) → Value e → Store Σ' Σ → Store Σ' (Σ-cast A∈Σ B)
  insert/cast-μ (here refl) v' (_ ∷ μ) = intro v' (Type⇑ _) ∷ μ
  insert/cast-μ (there A∈Σ) v' (px ∷ μ) = px ∷ insert/cast-μ A∈Σ v' μ

  rtti≡Σ/∼ : ∀ {Σ Σ' A B}
    → (A∈Σ : A ∈ Σ) → (μ : Store Σ' Σ) → store-lookup-rtti A∈Σ μ ∼ B → A ∼ B
  rtti≡Σ/∼ A∈Σ μ rtti∼B rewrite mem-rtti-preserves-Σ A∈Σ μ = rtti∼B
