module MonoRef.Dynamics.Original.Reduction where

open import Data.List.Membership.Propositional
  using (_∈_)
open import Relation.Binary.PropositionalEquality
  using (_≢_) renaming (_≡_ to _`≡_)
open import Relation.Nullary
  using (¬_)

-- standard library++
open import Data.List.Properties.Extra
  using (∈-∷ʳ)

open import MonoRef.Coercions.NoSpaceEfficiency.Reduction
open import MonoRef.Coercions.NoSpaceEfficiency.Syntax
open import MonoRef.Dynamics.EvalCtx
open import MonoRef.Dynamics.Original.Store
open import MonoRef.Dynamics.PureReduction
open import MonoRef.Language.TargetWithoutBlameNoSE
open import MonoRef.Static.Context
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations

infix 3  _,_,_⟶ₑ_,_
infix 3  _,_⟶ᵤᵣ_,_
infix 3  _,_⟶ₛ_,_


-- cast reduction rules
data _,_⟶ᵤᵣ_,_ {Γ Σ} : ∀ {Σ' A}
  → Σ  ∣ Γ ⊢ A → (ν  : Store Σ )
  → Σ' ∣ Γ ⊢ A → (ν' : Store Σ')
  → Set where

  pure : ∀ {ν A} {M' M : Σ ∣ Γ ⊢ A}
    → M ⟶ᵤ M'
      ----------------
    → M , ν ⟶ᵤᵣ M' , ν

  castref1 : ∀ {ν T T₂} {v : Σ ∣ Γ ⊢ Ref T} {c : Ref T ⟹ Ref T₂}
    → (R : Value v)
    → (rtti∼T₂ : store-lookup-rtti/ref R ν ∼ T₂)
    → ⊓ rtti∼T₂ ≢ store-lookup-rtti/ref R ν
      -----------------------------------------------------------------
    →   v < c >                             , ν
    ⟶ᵤᵣ addr (Σ-cast⟹∈ R) (⊓⟹⊑ᵣ rtti∼T₂) , ν-cast R ν (⊓⟹⊑ₗ rtti∼T₂)

  castref2 : ∀ {ν T T₂} {v : Σ ∣ Γ ⊢ Ref T} {c : Ref T ⟹ Ref T₂}
    → (R : Value v)
    → (rtti∼T₂ : store-lookup-rtti/ref R ν ∼ T₂)
    → (eq : ⊓ rtti∼T₂ `≡ store-lookup-rtti/ref R ν)
      -----------------------------------------------------
    →   v < c >                                         , ν
    ⟶ᵤᵣ addr (ref-ν⟹∈ R ν) (⊓⟹⊑ᵣ-with-≡ rtti∼T₂ eq) , ν

  castref3 : ∀ {ν T T₂} {v : Σ ∣ Γ ⊢ Ref T} {c : Ref T ⟹ Ref T₂}
    → (R : Value v)
    → ¬ store-lookup-rtti/ref R ν ∼ T₂
      --------------------------------
    → v < c > , ν ⟶ᵤᵣ error , ν

  cong : ∀ {Σ' A B} {μ : Store Σ} {ν : Store Σ'}
           {M : Σ ∣ Γ ⊢ B} {M' : Σ' ∣ Γ ⊢ B}
           {t : Σ ∣ Γ ⊢ A} {t' : Σ' ∣ Γ ⊢ A}
           {ξ : ECtx A B} {ξ' : ECtx A B}
    → M  ≡ ξ [ t  ]
    → M' ≡ ξ' [ t' ]
    → t , μ ⟶ᵤᵣ t' , ν
      ----------------
    → M , μ ⟶ᵤᵣ M' , ν

  cong-error : ∀ {A B M} {ν : Store Σ} {ξ : ECtx A B}
    → M  ≡ ξ [ error  ]
      ----------------------------
    → M , ν ⟶ᵤᵣ error {Σ = Σ} , ν

⟶ᵤᵣ⟹⊑ₕ : ∀ {Σ Σ' A}
              {M : Σ ∣ ∅ ⊢ A} {ν : Store Σ}
              {M' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → M , ν ⟶ᵤᵣ M' , ν'
  → Σ' ⊑ₕ Σ
⟶ᵤᵣ⟹⊑ₕ (pure x) = ⊑ₕ-refl
⟶ᵤᵣ⟹⊑ₕ {ν = ν} (castref1 R@(V-addr mem _) meet _)
  rewrite (ref-rtti-preserves-Σ R ν) = build-prec mem (⊓⟹⊑ₗ meet)
⟶ᵤᵣ⟹⊑ₕ (castref2 _ _ _) = ⊑ₕ-refl
⟶ᵤᵣ⟹⊑ₕ (castref3 _ _) = ⊑ₕ-refl
⟶ᵤᵣ⟹⊑ₕ (cong _ _ red) = ⟶ᵤᵣ⟹⊑ₕ red
⟶ᵤᵣ⟹⊑ₕ (cong-error _) = ⊑ₕ-refl

-- program reduction rules
data _,_,_⟶ₑ_,_ {Σ} : ∀ {Σ' A}
  → Σ  ∣ ∅ ⊢ A → (μ : Store Σ ) → NormalStore μ
  → Σ' ∣ ∅ ⊢ A → (ν : Store Σ')
  → Set where

  β-pure : ∀ {A μ μ-evd} {M' M : Σ ∣ ∅ ⊢ A}
    → M ⟶ M'
      ------------------------
    → M , μ , μ-evd ⟶ₑ M' , μ

  β-ref : ∀ {A μ μ-evd} {v : Σ ∣ ∅ ⊢ A}
    → (V : Value v)
      -----------------------------------
    →   ref v                  , μ , μ-evd
    ⟶ₑ addr (∈-∷ʳ Σ A) ⊑-refl , store V μ

  β-!ₛ : ∀ {A x μ μ-evd} {r : Σ ∣ ∅ ⊢ Ref A}
    → (R : Value r)
      -----------------------------------
    →   (!ₛ r) x              , μ , μ-evd
    ⟶ₑ μ-static-lookup R x μ , μ

  β-! : ∀ {B μ μ-evd} {r : Σ ∣ ∅ ⊢ Ref B}
    → (R : Value r)
      -------------------------------------------------------------
    →   ! r                                             , μ , μ-evd
    ⟶ₑ store-lookup-v/ref R μ < coerce (ref⟹T R) B > , μ

  β-:=ₛ : ∀ {A x μ μ-evd} {r : Σ ∣ ∅ ⊢ Ref A} {v : Σ ∣ ∅ ⊢ A}
    → (R : Value r)
    → (V : Value v)
      ----------------------------------------
    →   (r :=ₛ v) x  , μ , μ-evd
    ⟶ₑ unit {Σ = Σ} , μ-static-update R x μ V

  β-:= : ∀ {B μ μ-evd} {r : Σ ∣ ∅ ⊢ Ref B} {v : Σ ∣ ∅ ⊢ B}
    → (R : Value r)
    → (V : Value v)
      ------------------------------------------------------------------
    →   r := v       , μ , μ-evd
    ⟶ₑ unit {Σ = Σ} , ν-update/ref R μ ((v⇑ V) < coerce B (ref⟹T R) >)

  cong : ∀ {Σ' A B} {μ : Store Σ} {ν : Store Σ'} {μ-evd : NormalStore μ}
           {M : Σ ∣ ∅ ⊢ B} {M' : Σ' ∣ ∅ ⊢ B}
           {t : Σ ∣ ∅ ⊢ A} {t' : Σ' ∣ ∅ ⊢ A}
           {ξ : ECtx A B} {ξ' : ECtx A B}
    → M  ≡ ξ [ t  ]
    → M' ≡ ξ' [ t' ]
    → t , μ , μ-evd ⟶ₑ t' , ν
      ------------------------
    → M , μ , μ-evd ⟶ₑ M' , ν

  cong-error : ∀ {A B} {μ : Store Σ} {μ-evd : NormalStore μ}
                 {M : Σ ∣ ∅ ⊢ B}
                 {ξ : ECtx A B}
    → M  ≡ ξ [ error  ]
      -----------------------------------
    → M , μ , μ-evd ⟶ₑ error {Σ = Σ} , μ

-- state reduction rules
data _,_⟶ₛ_,_ {Σ A} : ∀ {Σ'}
  → Σ  ∣ ∅ ⊢ A → (ν  : Store Σ )
  → Σ' ∣ ∅ ⊢ A → (ν' : Store Σ')
  → Set where

  prog-reduce : ∀ {Σ' μ ν} {M : Σ ∣ ∅ ⊢ A} {M' : Σ' ∣ ∅ ⊢ A}
    → (μ-evd : NormalStore μ)
    → M , μ , μ-evd ⟶ₑ M' , ν
      ------------------------
    → M , μ ⟶ₛ M' , ν

-- Is there a bug in the paper related to this rule where it assumes the ⟶ᵤᵣ takes a μ as input?
  cast-reduce :  ∀ {Σ' ν ν'} {M : Σ ∣ ∅ ⊢ A} {M' : Σ' ∣ ∅ ⊢ A}
    → M , ν ⟶ᵤᵣ M' , ν'
      -----------------
    → M , ν ⟶ₛ M' , ν'

  error :  ∀ {Σ' ν t} {ν' : Store Σ'} {M : Σ ∣ ∅ ⊢ A}
    → (mem : t ∈ Σ)
    → store-lookup-v mem ν , ν ⟶ᵤᵣ error {Σ = Σ'} , ν'
      ------------------------------------------------
    → M , ν ⟶ₛ error , ν'

  hcast : ∀ {Σ' t ν ν'} {M : Σ ∣ ∅ ⊢ A} {cv' : Σ' ∣ ∅ ⊢ t} {mem' : t ∈ Σ'}
    → (mem : t ∈ Σ)
    → (red : store-lookup-v mem ν , ν ⟶ᵤᵣ cv' , ν')
    → SameStoreValueType (⟶ᵤᵣ⟹⊑ₕ red) mem mem'
    → store-lookup-rtti mem ν `≡ store-lookup-rtti mem' ν'
    → (CV' : CastedValue cv')
      --------------------------------------------------------------------
    →    M                                            , ν
    ⟶ₛ typeprecise-strenthen-expr (⟶ᵤᵣ⟹⊑ₕ red) M , ν-update mem' ν' CV'

  hdrop : ∀ {Σ' t t' ν ν'} {M : Σ ∣ ∅ ⊢ A} {cv' : Σ' ∣ ∅ ⊢ t} {mem' : t' ∈ Σ'}
    → (mem : t ∈ Σ)
    → (red : store-lookup-v mem ν , ν ⟶ᵤᵣ cv' , ν')
    → DistinctStoreValueTypes (⟶ᵤᵣ⟹⊑ₕ red) mem mem'
    → store-lookup-rtti mem ν ≢ store-lookup-rtti mem' ν'
      --------------------------------------------------
    →    M                                           , ν
    ⟶ₛ typeprecise-strenthen-expr (⟶ᵤᵣ⟹⊑ₕ red) M , ν'
