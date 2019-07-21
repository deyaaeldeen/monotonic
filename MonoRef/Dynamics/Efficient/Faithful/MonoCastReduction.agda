{-

  MonoRef.Dynamics.Efficient.Faithful.MonoCastReduction provides a reduction
  relation for casts on monotonic references with faithful coercions.

-}

module MonoRef.Dynamics.Efficient.Faithful.MonoCastReduction where

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
open import Relation.Nullary using (¬_)

open import MonoRef.Dynamics.Efficient.Faithful.Coercions
open import MonoRef.Dynamics.Efficient.Faithful.Store
open import MonoRef.Dynamics.Efficient.Faithful.TargetWithoutBlame
open import MonoRef.Dynamics.Efficient.Faithful.Value
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


infix 3  _,_⟶ₘ_,_

data _,_⟶ₘ_,_ {Γ Σ} : ∀ {Σ' A}
  → Σ  ∣ Γ ⊢ A → (ν  : Store Σ )
  → Σ' ∣ Γ ⊢ A → (ν' : Store Σ')
  → Set where

  castref1 : ∀ {ν T T₂ A} {v : Σ ∣ Γ ⊢ Ref T} {T₂⊑A : T₂ ⊑ A}
    → (R : SimpleValue v)
    → (rtti∼T₂ : store-lookup-rtti (ref⟹∈ R) ν ∼ T₂)
    → ⊓ rtti∼T₂ ≢ store-lookup-rtti (ref⟹∈ R) ν
      --------------------------------------------------------------------------------------------------------------
    →   v < final (middle (Ref T₂ T₂⊑A)) >                                      , ν
    ⟶ₘ addr (Σ-cast⟹∈ (ref⟹∈ R) (⊓ rtti∼T₂)) (⊑-trans (⊓⟹⊑ᵣ rtti∼T₂) T₂⊑A) , ν-cast (ref⟹∈ R) ν (⊓⟹⊑ₗ rtti∼T₂)

  castref2 : ∀ {ν T T₂ A} {v : Σ ∣ Γ ⊢ Ref T} {T₂⊑A : T₂ ⊑ A}
    → (R : SimpleValue v)
    → (rtti∼T₂ : store-lookup-rtti/ref R ν ∼ T₂)
    → (eq : ⊓ rtti∼T₂ ≡ store-lookup-rtti/ref R ν)
      -------------------------------------------------------------------
    →   v < final (middle (Ref T₂ T₂⊑A)) >                            , ν
    ⟶ₘ addr (ref-ν⟹∈ R ν) (⊑-trans (⊓⟹⊑ᵣ-with-≡ rtti∼T₂ eq) T₂⊑A) , ν

  castref3 : ∀ {ν T T₂ A} {v : Σ ∣ Γ ⊢ Ref T} {T₂⊑A : T₂ ⊑ A}
    → (R : SimpleValue v)
    → ¬ store-lookup-rtti/ref R ν ∼ T₂
      ----------------------------------------------------
    → v < final (middle (Ref T₂ T₂⊑A)) > , ν ⟶ₘ error , ν

⟶ₘ⟹⊑ₕ : ∀ {Γ Σ Σ' A}
              {M : Σ ∣ Γ ⊢ A} {ν : Store Σ}
              {M' : Σ' ∣ Γ ⊢ A} {ν' : Store Σ'}
  → M , ν ⟶ₘ M' , ν'
  → Σ' ⊑ₕ Σ
⟶ₘ⟹⊑ₕ {ν = ν} (castref1 R rtti∼T₂ x)
  rewrite (mem-rtti-preserves-Σ (ref⟹∈ R) ν) =
    build-prec (ref⟹∈ R) (⊓⟹⊑ₗ rtti∼T₂)
⟶ₘ⟹⊑ₕ (castref2 _ _ _) = ⊑ₕ-refl
⟶ₘ⟹⊑ₕ (castref3 _ _) = ⊑ₕ-refl
