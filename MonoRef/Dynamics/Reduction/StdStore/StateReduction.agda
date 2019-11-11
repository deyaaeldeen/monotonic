open import MonoRef.Static.Types

module MonoRef.Dynamics.Reduction.StdStore.StateReduction
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)  where

open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.List.All using () renaming (map to all-map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (proj₁ ; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)

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
open import MonoRef.Dynamics.Store.Std.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


module ParamStateReduction/Pre
  (Value : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set) where

  open ParamSuspendedCast Value

  module ParamStateReduction
    (make-coercion : ∀ A B → A ⟹ B)
    (SimpleValue : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
    (ref⟹T : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → Type)
    (ref⟹∈ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ∈ Σ)
    (ref⟹⊑ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : SimpleValue v) → ref⟹T V ⊑ A)
    (typeprecise-strenthen-val : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A} → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
      → Value v
      → Value (typeprecise-strenthen-expr Σ'⊑ₕΣ v))
    (apply-cast : ∀ {A B Σ}
      → (Q : List (SuspendedCast Σ))
      → ∀ {e : proj₁ (merge Q) ∣ ∅ ⊢ A} → (v : Value e)
      → A ⟹ B
      → CastResult Q B) where

    open ParamStoreValue Value
    open ParamStoreDef StoreValue
    open ParamStore SimpleValue Value ref⟹T ref⟹∈ ref⟹⊑

    open ParamPrecisionStoreValStrenthening Value typeprecise-strenthen-val

    μ-cast : ∀ {Σ A}
      → (Q : List (SuspendedCast Σ))
      → (A∈Σ : A ∈ Σ)
      → (B : Type)
      → (μ : Store (proj₁ (merge (cast A∈Σ B ∷ Q))) Σ)
      → (rtti∼B : store-lookup-rtti A∈Σ μ ∼ B)
      → StorePartialCast Q A∈Σ (⊓⟹⊑ₗ (rtti≡Σ/∼ A∈Σ μ rtti∼B))
    μ-cast Q A∈Σ B μ rtti∼B
      rewrite mem-rtti-preserves-Σ A∈Σ μ
      with apply-cast (cast A∈Σ B ∷ Q) (proj₂ (store-lookup-val (rtti∈ A∈Σ μ) μ)) (make-coercion (store-lookup-rtti A∈Σ μ) (⊓ rtti∼B))
    ... | error = error
    ... | done Q' v' =
      done Q' (insert/cast-μ A∈Σ (typeprecise-strenthen-val sQ v') μ')
      where
        sQ = merge-soundness A∈Σ rtti∼B (Q ++ Q')
        μ' = all-map (typeprecise-strenthen-storeval (⊑ₕ-trans sQ (merge-respects-⊑ₕ (cast A∈Σ B ∷ Q) Q'))) μ
    
    infix 3  _,_,_⟶_,_,_
    
    {- State Reduction Rules -}
    
    data _,_,_⟶_,_,_ {Σ T} : ∀ {Σ₂ Σ₃ Σ₄ Σ₅}
        (Q  : List (SuspendedCast Σ)) → (M  : Σ₃ ∣ ∅ ⊢ T) → (μ  : Store Σ₃ Σ₂)
      → (Q' : List (SuspendedCast Σ)) → (M' : Σ₅ ∣ ∅ ⊢ T) → (μ' : Store Σ₅ Σ₄)
      → Set where
    
      state/update-store : ∀ {A B} {Q : List (SuspendedCast Σ)} {A∈Σ : A ∈ Σ}
                             {μ : Store (proj₁ (merge (cast A∈Σ B ∷ Q))) Σ}
                             {M : proj₁ (merge (cast A∈Σ B ∷ Q)) ∣ ∅ ⊢ T}
        →  (rtti∼B : store-lookup-rtti A∈Σ μ ∼ B)
        → ⊓ rtti∼B ≢ store-lookup-rtti A∈Σ μ
        → (c : SuccessfulStoreCast (μ-cast Q A∈Σ B μ rtti∼B))
          ---------------------------------------------------
        → cast A∈Σ B ∷ Q , M , μ
        ⟶ Q ++ proj₁ (get-μ-from-successful-μ-cast c)
          , typeprecise-strenthen-expr (⊑ₕ-trans (merge-respects-⊑ₕ' (build-prec A∈Σ (⊓⟹⊑ₗ (rtti≡Σ/∼ A∈Σ μ rtti∼B))) Q (proj₁ (get-μ-from-successful-μ-cast c))) (merge-soundness A∈Σ (rtti≡Σ/∼ A∈Σ μ rtti∼B) Q)) M
          , proj₂ (get-μ-from-successful-μ-cast c)
    
      state/error1 : ∀ {A B} {Q : List (SuspendedCast Σ)} {A∈Σ : A ∈ Σ}
                       {μ : Store (proj₁ (merge (cast A∈Σ B ∷ Q))) Σ}
                       {M : proj₁ (merge (cast A∈Σ B ∷ Q)) ∣ ∅ ⊢ T}
        → (rtti∼B : store-lookup-rtti A∈Σ μ ∼ B)
        → ⊓ rtti∼B ≢ store-lookup-rtti A∈Σ μ
        → FailedStoreCast (μ-cast Q A∈Σ B μ rtti∼B)
          -----------------------------------------
        → cast A∈Σ B ∷ Q , M , μ ⟶ Q , error , μ
    
      state/error2 : ∀ {A B} {Q : List (SuspendedCast Σ)} {A∈Σ : A ∈ Σ}
                       {μ : Store (proj₁ (merge (cast A∈Σ B ∷ Q))) Σ}
                       {M : proj₁ (merge (cast A∈Σ B ∷ Q)) ∣ ∅ ⊢ T}
        → ¬ store-lookup-rtti A∈Σ μ ∼ B
          ----------------------------------------
        → cast A∈Σ B ∷ Q , M , μ ⟶ Q , error , μ
    
      state/discard : ∀ {A B} {Q : List (SuspendedCast Σ)} {A∈Σ : A ∈ Σ}
                        {μ : Store (proj₁ (merge (cast A∈Σ B ∷ Q))) Σ}
                        {M : proj₁ (merge (cast A∈Σ B ∷ Q)) ∣ ∅ ⊢ T}
        →  (rtti∼B : store-lookup-rtti A∈Σ μ ∼ B)
        → ⊓ rtti∼B ≡ store-lookup-rtti A∈Σ μ
          ------------------------------------
        → cast A∈Σ B ∷ Q , M , μ ⟶ Q , M , μ
    
    ⟶⟹rtti⊑Σ : ∀ {Σ Σ₂ Σ₃ Σ₄ Σ₅ A} {Q Q' : List (SuspendedCast Σ)}
                     {M : Σ₃ ∣ ∅ ⊢ A} {μ : Store Σ₃ Σ₂}
                     {M' : Σ₅ ∣ ∅ ⊢ A} {μ' : Store Σ₅ Σ₄}
      → Q , M , μ  ⟶ Q' , M' , μ'
      → Σ₄ ⊑ₕ Σ
    ⟶⟹rtti⊑Σ (state/update-store {A∈Σ = A∈Σ} {μ = μ} rtti∼B x c) =
      build-prec A∈Σ (⊓⟹⊑ₗ (rtti≡Σ/∼ A∈Σ μ rtti∼B))
    ⟶⟹rtti⊑Σ (state/error1 _ _ _) = ⊑ₕ-refl
    ⟶⟹rtti⊑Σ (state/error2 x) = ⊑ₕ-refl
    ⟶⟹rtti⊑Σ (state/discard rtti∼B x) = ⊑ₕ-refl
    
    -- ⟶⟹Σ'⊑Σ : ∀ {Σ Σ₂ Σ₃ Σ₄ Σ₅ A} {Q Q' : List (SuspendedCast Σ)}
    --             {M : Σ₃ ∣ ∅ ⊢ A} {μ : Store Σ₃ Σ₂}
    --             {M' : Σ₅ ∣ ∅ ⊢ A} {μ' : Store Σ₅ Σ₄}
    --   → Q , M , μ  ⟶ Q' , M' , μ'
    --   → StoreTypingProgress Σ Σ₅
    -- ⟶⟹Σ'⊑Σ (state/update-store {Q = Q} {A∈Σ = A∈Σ} {μ = μ} rtti∼B x c) =
    --   from⊑ₕ (⊑ₕ-trans (proj₂ (proj₂ r)) (proj₁ (proj₂ r)))
    --   where
    --     r = merge' (build-prec A∈Σ (⊓⟹⊑ₗ (rtti≡Σ/∼ A∈Σ μ rtti∼B))) (Q ++ proj₁ (get-μ-from-successful-μ-cast c))
    -- ⟶⟹Σ'⊑Σ (state/error1 rtti∼B x) = {!!} --StoreTypingProgress-refl
    -- ⟶⟹Σ'⊑Σ (state/error2 x) = {!!} --StoreTypingProgress-refl
    -- ⟶⟹Σ'⊑Σ (state/discard rtti∼B x) = from⊑ₕ {!!} --StoreTypingProgress-refl
