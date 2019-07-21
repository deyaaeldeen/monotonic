{-

  MonoRef.Dynamics.EvolvingStore.Store exports various tools to work stores
  parameterized over the representation of values and casted values.

-}

open import MonoRef.Static.Types

module MonoRef.Dynamics.EvolvingStore.Store
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.List.Any using (here; there)
open import Data.List.All using (All ; lookup)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; subst)

-- stdlib++
open import Data.List.All.Properties.Extra using (_All[_]≔'_)

open import MonoRef.Dynamics.EvolvingStore.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.EvolvingStore.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


module ParamStore
  (SimpleValue : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (Value : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (DelayedCast       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (ReducibleDelayedCast : ∀ {Σ Γ A} {e : Σ ∣ Γ ⊢ A} → DelayedCast e → Set)

  {- These utilities depend on the definition of Value -}
  (ref⟹T : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → Type)
  (ref⟹∈ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ∈ Σ)
  (ref⟹⊑ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ⊑ A)
  where

  open ParamStoreValue Value DelayedCast ReducibleDelayedCast
  open ParamStoreDef StoreValue

  ref-static-type : ∀ {Σ Γ A} {r : Σ ∣ Γ ⊢ Ref A}
    → (R : SimpleValue r) → static A → ref⟹T R ≡ A
  ref-static-type R static-A = ⊑-respect-static (ref⟹⊑ R) static-A

  lookup-store : ∀ {Σ A} → A ∈ Σ → Store Σ → StoreValue A Σ
  lookup-store A∈Σ ν = lookup ν A∈Σ

  update-store : ∀ {Σ A} → A ∈ Σ → NormalStoreValue A Σ → Store Σ → Store Σ
  update-store ptr v μ = μ All[ ptr ]≔' fromNormalValue v

  store-lookup-v : ∀ {Σ A} → A ∈ Σ → Store Σ → Σ ∣ ∅ ⊢ A
  store-lookup-v A∈Σ ν with lookup-store A∈Σ ν
  ... | fromNormalValue (intro {V = V} _ _) = V
  ... | fromDelayedCast (intro {V = V} _ _) = V

  store-lookup-v/ref : ∀ {Σ Γ A} {r : Σ ∣ Γ ⊢ Ref A}
    → (R : SimpleValue r) → Store Σ → Σ ∣ ∅ ⊢ ref⟹T R
  store-lookup-v/ref R ν = store-lookup-v (ref⟹∈ R) ν

  store-lookup-rtti : ∀ {Σ A} → A ∈ Σ → Store Σ → Type
  store-lookup-rtti A∈Σ ν with lookup-store A∈Σ ν
  ... | fromNormalValue (intro _ ty) = Ty⇓ ty
  ... | fromDelayedCast (intro _ ty) = Ty⇓ ty

  store-lookup-rtti/ref : ∀ {Σ Γ T} {r : Σ ∣ Γ ⊢ Ref T}
    → (R : SimpleValue r) → Store Σ → Type
  store-lookup-rtti/ref R ν = store-lookup-rtti (ref⟹∈ R) ν

  μ-static-lookup : ∀ {Σ Γ A} {r : Σ ∣ Γ ⊢ Ref A}
    → (R : SimpleValue r) → static A → Store Σ → Σ ∣ ∅ ⊢ A
  μ-static-lookup r x ν
    with ref⟹T r | ref-static-type r x | store-lookup-v/ref r ν
  ... | _ | refl | res = res

  μ-static-update : ∀ {Σ A} {r : Σ ∣ ∅ ⊢ Ref A}
    → (R : SimpleValue r)
    → static A
    → Store Σ
    → ∀ {v : Σ ∣ ∅ ⊢ A}
    → Value v
    → Store Σ
  μ-static-update R x μ v =
    update-store (ref⟹∈ R) (subst (λ x₁ → x₁) (helper R x) (toNormalStoreValue v)) μ
     where
       helper : ∀ {Σ Γ B} {r : Σ ∣ Γ ⊢ Ref B}
         → (R : SimpleValue r)
         → static B
         → NormalStoreValue B Σ ≡ NormalStoreValue (ref⟹T R) Σ
       helper r x rewrite ref-static-type r x = refl

  update-evolvingstore : ∀ {Σ t} → t ∈ Σ → EvolvingStoreValue t Σ → Store Σ → Store Σ
  update-evolvingstore ptr v μ = μ All[ ptr ]≔' fromDelayedCast v

  toEvolvingStoreValue : ∀ {Σ A} {v : Σ ∣ ∅ ⊢ A} → DelayedCast v → EvolvingStoreValue A Σ
  toEvolvingStoreValue {A = A} v = intro v (Type⇑ A)

  μ-update : ∀ {Σ A}
    → A ∈ Σ
    → Store Σ
    → ∀ {e : Σ ∣ ∅ ⊢ A}
    → Value e
    → Store Σ
  μ-update A∈Σ ν v = update-store A∈Σ (toNormalStoreValue v) ν

  ν-update : ∀ {Σ A}
    → A ∈ Σ
    → Store Σ
    → ∀ {e : Σ ∣ ∅ ⊢ A}
    → DelayedCast e
    → Store Σ
  ν-update A∈Σ ν v = update-evolvingstore A∈Σ (toEvolvingStoreValue v) ν

  mem-rtti-preserves-Σ : ∀ {Σ A}
    → (A∈Σ : A ∈ Σ)
    → (ν : Store Σ)
    → (store-lookup-rtti A∈Σ ν) ≡ A
  mem-rtti-preserves-Σ A∈Σ ν with lookup-store A∈Σ ν
  ... | fromNormalValue (intro _ _) = refl
  ... | fromDelayedCast (intro _ _) = refl

  ref-rtti-preserves-Σ : ∀ {Σ Γ A} {r : Σ ∣ Γ ⊢ Ref A}
    → (R : SimpleValue r)
    → (ν : Store Σ)
    → (store-lookup-rtti/ref R ν) ≡ (ref⟹T R)
  ref-rtti-preserves-Σ R ν = mem-rtti-preserves-Σ (ref⟹∈ R) ν

  ref-ν⟹∈ : ∀ {Σ Γ T} {v : Σ ∣ Γ ⊢ Ref T}
    → (R : SimpleValue v) → (ν : Store Σ) → store-lookup-rtti/ref R ν ∈ Σ
  ref-ν⟹∈ R ν rewrite (ref-rtti-preserves-Σ R ν) = ref⟹∈ R

  ref-ν⟹⊑ : ∀ {Σ Γ T} {v : Σ ∣ Γ ⊢ Ref T}
    → (R : SimpleValue v) → (ν : Store Σ) → store-lookup-rtti/ref R ν ⊑ T
  ref-ν⟹⊑ R ν rewrite (ref-rtti-preserves-Σ R ν) = ref⟹⊑ R
