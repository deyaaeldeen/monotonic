open import MonoRef.Static.Types

module MonoRef.Dynamics.Reduction.StdStore.MonoReduction
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.List using (List ; [] ; _∷ʳ_)
open import Data.List.All using (map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (proj₁ ; proj₂)

-- standard library++
open import Data.List.Prefix using (∷ʳ-⊒) renaming (_⊑_ to _⊑ₗ_)
open import Data.List.Properties.Extra using (∈-∷ʳ)

open import MonoRef.Dynamics.Reduction.StdStore.SuspendedCast
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Std.Precision.StoreValStrenthening
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Std.Store
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Std.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.Store.TypingProgress
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Std.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


module ParamMonoReduction
  (make-coercion : ∀ A B → A ⟹ B)
  (SimpleValue : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (Value       : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  (ref⟹T : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → Type)
  (ref⟹∈ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ∈ Σ)
  (ref⟹⊑ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ⊑ A)
  where

  open ParamStoreValue Value
  open ParamStoreDef StoreValue
  open ParamStore SimpleValue Value ref⟹T ref⟹∈ ref⟹⊑
  open ParamSuspendedCast Value

  module ParamMonoReduction/store/apply-cast
    (store : ∀ {Σ A} {v : Σ ∣ ∅ ⊢ A} → Value v → Store Σ Σ → Store (Σ ∷ʳ A) (Σ ∷ʳ A))
    (apply-cast : ∀ {A B Σ}
      → (Q : List (SuspendedCast Σ))
      → ∀ {e : proj₁ (merge Q) ∣ ∅ ⊢ A}
      → (v : Value e)
      → (c : A ⟹ B)
      → CastResult Q B)
    (typeprecise-strenthen-val : ∀ {Σ Σ' Γ A} {e : Σ ∣ Γ ⊢ A} → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
      → Value e
      → Value (typeprecise-strenthen-expr Σ'⊑ₕΣ e))
    where

    open ParamPrecisionStoreValStrenthening Value typeprecise-strenthen-val

    infix 3  _,_⟶ᵢₘ_,_,_
  
    data _,_⟶ᵢₘ_,_,_ {Σ} : ∀ {Σ' Σ'' A}
      → Σ   ∣ ∅ ⊢ A → (μ : Store Σ Σ)
      → (Q : List (SuspendedCast Σ)) → Σ'' ∣ ∅ ⊢ A → Store Σ'' Σ'
      → Set
  
    ⟶ᵢₘ⟹rtti⊑Σ : ∀ {Σ Σ' Σ'' A} {Q : List (SuspendedCast Σ)} {μ : Store Σ Σ} {μ' : Store Σ'' Σ'}
                   {M : Σ ∣ ∅ ⊢ A} {M' : Σ'' ∣ ∅ ⊢ A}
      → M , μ ⟶ᵢₘ Q , M' , μ'
      → StoreTypingProgress Σ Σ'

    ⟶ᵢₘ⟹Σ'⊑Σ : ∀ {Σ Σ' Σ'' A} {Q : List (SuspendedCast Σ)} {μ : Store Σ Σ} {μ' : Store Σ'' Σ'}
                 {M : Σ ∣ ∅ ⊢ A} {M' : Σ'' ∣ ∅ ⊢ A}
      → M , μ ⟶ᵢₘ Q , M' , μ'
      → StoreTypingProgress Σ Σ''
  
    {- Impure Program Reduction Rules -}
  
    data _,_⟶ᵢₘ_,_,_ {Σ} where
  
      β-ref : ∀ {A μ} {v : Σ ∣ ∅ ⊢ A}
        → (V : Value v)
          ----------------------------------------------
        →   ref A v , μ
        ⟶ᵢₘ [] , addr (∈-∷ʳ Σ A) ⊑-reflexive , store V μ
  
      β-!ₛ : ∀ {A x μ} {r : Σ ∣ ∅ ⊢ Ref A}
        → (R : SimpleValue r)
          ---------------------------------
        →   (!ₛ r) x , μ
        ⟶ᵢₘ [] , μ-static-lookup R x μ , μ
  
      β-! : ∀ {B μ} {r : Σ ∣ ∅ ⊢ Ref B}
        → (R : SimpleValue r)
          -----------------------------------------------------------------------
        →   ! B r , μ
        ⟶ᵢₘ [] , store-lookup-v (ref⟹∈ R) μ < make-coercion (ref⟹T R) B > , μ
  
      β-:=ₛ : ∀ {A x μ} {r : Σ ∣ ∅ ⊢ Ref A} {v : Σ ∣ ∅ ⊢ A}
        → (R : SimpleValue r) → (V : Value v)
          --------------------------------------
        →   (r :=ₛ v) x , μ
        ⟶ᵢₘ [] , unit , μ-static-update R x μ V
  
      β-:= : ∀ {B μ} {r : Σ ∣ ∅ ⊢ Ref B} {v : Σ ∣ ∅ ⊢ B}
        → (R : SimpleValue r)
        → (V : Value v)
        → (c : SuccessfulCast (apply-cast [] V (make-coercion B (store-lookup-rtti/ref R μ))))
          ------------------------------------------------------------------------------------
        → := B r v , μ
        ⟶ᵢₘ proj₁ (get-val-from-successful-cast c)
        , unit
        , μ-update (ref-ν⟹∈ R μ)
                   (map (typeprecise-strenthen-storeval (proj₂ (merge (proj₁ (get-val-from-successful-cast c))))) μ)
                   (proj₂ (proj₂ (get-val-from-successful-cast c)))

      β-:=/failed : ∀ {B μ} {r : Σ ∣ ∅ ⊢ Ref B} {v : Σ ∣ ∅ ⊢ B}
        → (R : SimpleValue r)
        → (V : Value v)
        → (c : FailedCast (apply-cast [] V (make-coercion B (store-lookup-rtti/ref R μ))))
          --------------------------------------------------------------------------------
        → := B r v , μ ⟶ᵢₘ [] , error , μ

    ⟶ᵢₘ⟹rtti⊑Σ (β-!ₛ _) = StoreTypingProgress-refl
    ⟶ᵢₘ⟹rtti⊑Σ (β-! _) = StoreTypingProgress-refl
    ⟶ᵢₘ⟹rtti⊑Σ (β-:=ₛ _ _) = StoreTypingProgress-refl
    ⟶ᵢₘ⟹rtti⊑Σ (β-:= _ _ _) = StoreTypingProgress-refl
    ⟶ᵢₘ⟹rtti⊑Σ (β-:=/failed _ _ _) = StoreTypingProgress-refl
    ⟶ᵢₘ⟹rtti⊑Σ {Σ} {A = Ref A} (β-ref _) = from⊑ₗ (∷ʳ-⊒ A Σ)

    ⟶ᵢₘ⟹Σ'⊑Σ (β-!ₛ _) = StoreTypingProgress-refl
    ⟶ᵢₘ⟹Σ'⊑Σ (β-! _) = StoreTypingProgress-refl
    ⟶ᵢₘ⟹Σ'⊑Σ (β-:=ₛ _ _) = StoreTypingProgress-refl
    ⟶ᵢₘ⟹Σ'⊑Σ (β-:= _ _ c) = from⊑ₕ (proj₂ (merge (proj₁ (get-val-from-successful-cast c))))
    ⟶ᵢₘ⟹Σ'⊑Σ (β-:=/failed _ _ _) = StoreTypingProgress-refl
    ⟶ᵢₘ⟹Σ'⊑Σ {Σ} {A = Ref A} (β-ref _) = from⊑ₗ (∷ʳ-⊒ A Σ)
