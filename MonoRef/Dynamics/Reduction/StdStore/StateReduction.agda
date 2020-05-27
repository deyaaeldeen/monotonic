open import MonoRef.Static.Types

module MonoRef.Dynamics.Reduction.StdStore.StateReduction
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)  where

open import Data.Empty using (⊥-elim)
open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.List.All using () renaming (map to all-map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (proj₁ ; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_ ; yes ; no)
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
    (apply-cast : ∀ {A B Σ Σ'}
      → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
      → (Q : List (SuspendedCast Σ))
      → ∀ {e : proj₁ (merge' Σ'⊑ₕΣ Q) ∣ ∅ ⊢ A} → (v : Value e)
      → A ⟹ B
      → CastResult Σ'⊑ₕΣ Q B) where

    open ParamStoreValue Value
    open ParamStoreDef StoreValue
    open ParamStore SimpleValue Value ref⟹T ref⟹∈ ref⟹⊑

    open ParamPrecisionStoreValStrenthening Value typeprecise-strenthen-val

    μ-cast : ∀ {Σ Σ' A}
      → (Q : List (SuspendedCast Σ))
      → (A∈Σ : A ∈ Σ)
      → (B : Type)
      → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
      → (μ : Store (proj₁ (merge' Σ'⊑ₕΣ (cast A∈Σ B ∷ Q))) Σ')
      → (rtti∼B : store-lookup-rtti (proj₂ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ)) μ ∼ B)
      → StorePartialCast Σ'⊑ₕΣ Q A∈Σ (⊓⟹⊑ₗ (rtti≡Σ/∼ (proj₂ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ)) μ rtti∼B))
    μ-cast {Σ' = Σ'} Q A∈Σ B Σ'⊑ₕΣ μ rtti∼B
      rewrite mem-rtti-preserves-Σ (proj₂ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ)) μ
      with apply-cast Σ'⊑ₕΣ (cast A∈Σ B ∷ Q) (proj₂ (store-lookup-val (rtti∈ (proj₂ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ)) μ) μ)) (make-coercion (store-lookup-rtti (proj₂ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ)) μ) (⊓ rtti∼B))
    ... | error = error
    ... | done Q' v' =
      done Q' (insert/cast-μ (proj₂ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ)) (typeprecise-strenthen-val sQ v') μ')
      where
        sQ = merge-soundness Σ'⊑ₕΣ A∈Σ rtti∼B (Q ++ Q')
        μ' = all-map (typeprecise-strenthen-storeval (⊑ₕ-trans sQ (merge-respects-⊑ₕ' Σ'⊑ₕΣ (cast A∈Σ B ∷ Q) Q'))) μ

    μ-error1 :
      ∀ {A B Σ Σ₁} {Σ₁⊑ₕΣ : Σ₁ ⊑ₕ Σ} {Q  : List (SuspendedCast Σ)}
      → (A∈Σ : A ∈ Σ)
      → (μ : Store (proj₁ (merge' Σ₁⊑ₕΣ (cast A∈Σ B ∷ Q))) Σ₁)
      → Store (proj₁ (merge' (⊑ₕ-trans ⊑ₕ-refl Σ₁⊑ₕΣ) (cast A∈Σ B ∷ Q))) Σ₁
    μ-error1 {Σ₁⊑ₕΣ = Σ₁⊑ₕΣ} A∈Σ μ rewrite ⊑ₕ-trans-respects-reflˡ Σ₁⊑ₕΣ = μ

    μ-error2 :
      ∀ {A B Σ Σ₁} {Σ₁⊑ₕΣ : Σ₁ ⊑ₕ Σ} {Q  : List (SuspendedCast Σ)}
      → (A∈Σ : A ∈ Σ)
      → (μ : Store (proj₁ (merge' Σ₁⊑ₕΣ (cast A∈Σ B ∷ Q))) Σ₁)
      → (x : ¬ store-lookup-rtti (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ)) μ ∼ B)
      → Store (proj₁ (merge' (⊑ₕ-trans ⊑ₕ-refl Σ₁⊑ₕΣ) Q)) Σ₁
    μ-error2 {B = B} {Σ₁⊑ₕΣ = Σ₁⊑ₕΣ} {Q} A∈Σ μ x
      rewrite ⊑ₕ-trans-respects-reflˡ Σ₁⊑ₕΣ
            | mem-rtti-preserves-Σ (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ)) μ
          with ∼-decidable (proj₁ (∈-⊒ₕ (pw-lift-∈ Σ₁⊑ₕΣ A∈Σ))) B
    ...     | yes p = ⊥-elim (x p)
    ...     | no ¬p = μ

    μ-discard :
      ∀ {A B Σ Σ₁} {Σ₁⊑ₕΣ : Σ₁ ⊑ₕ Σ} {Q  : List (SuspendedCast Σ)}
      → (A∈Σ : A ∈ Σ)
      → (μ : Store (proj₁ (merge' Σ₁⊑ₕΣ (cast A∈Σ B ∷ Q))) Σ₁)
      → (rtti∼B : store-lookup-rtti (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ)) μ ∼ B)
      → ⊓ rtti∼B ≡ store-lookup-rtti (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ)) μ
      → Store (proj₁ (merge' (⊑ₕ-trans ⊑ₕ-refl Σ₁⊑ₕΣ) Q)) Σ₁
    μ-discard {B = B}{Σ₁ = Σ₁} {Σ₁⊑ₕΣ = Σ₁⊑ₕΣ} {Q} A∈Σ μ rtti∼B x
      rewrite ⊑ₕ-trans-respects-reflˡ Σ₁⊑ₕΣ
            | mem-rtti-preserves-Σ (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ)) μ
          with ∼-decidable (proj₁ (∈-⊒ₕ (pw-lift-∈ Σ₁⊑ₕΣ A∈Σ))) B
    ...     | no ¬p = μ
    ...     | yes p rewrite ∼-respects-≡ p rtti∼B
            with ∈-⊒ₕ (pw-lift-∈ Σ₁⊑ₕΣ A∈Σ)
    ...       | ⟨ A' , A'∈Σ' ⟩
              with (⊓⟹⊑ₗ rtti∼B)
    ...         | q
                with (⊓ rtti∼B)
    ...           | _ rewrite x
                  with (build-prec (⊑ₕ∈⇒∈ A'∈Σ') q)
    ...             | q3 rewrite Σ-cast/A∈Σ/A≡Σ (⊑ₕ∈⇒∈ A'∈Σ') | Σ⊑ₕΣ≡⊑ₕ-refl q3 | ⊑ₕ-trans-respects-reflˡ Σ₁⊑ₕΣ = μ

    e-discard :
      ∀ {A B T Σ Σ₁} {Σ₁⊑ₕΣ : Σ₁ ⊑ₕ Σ} {Q  : List (SuspendedCast Σ)}
      → (A∈Σ : A ∈ Σ)
      → (μ : Store (proj₁ (merge' Σ₁⊑ₕΣ (cast A∈Σ B ∷ Q))) Σ₁)
      → proj₁ (merge' Σ₁⊑ₕΣ (cast A∈Σ B ∷ Q)) ∣ ∅ ⊢ T
      → (rtti∼B : store-lookup-rtti (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ)) μ ∼ B)
      → ⊓ rtti∼B ≡ store-lookup-rtti (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ)) μ
      → proj₁ (merge' (⊑ₕ-trans ⊑ₕ-refl Σ₁⊑ₕΣ) Q) ∣ ∅ ⊢ T
    e-discard {B = B}{Σ₁ = Σ₁} {Σ₁⊑ₕΣ = Σ₁⊑ₕΣ} {Q} A∈Σ μ e rtti∼B x
          rewrite ⊑ₕ-trans-respects-reflˡ Σ₁⊑ₕΣ
            | mem-rtti-preserves-Σ (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ)) μ
          with ∼-decidable (proj₁ (∈-⊒ₕ (pw-lift-∈ Σ₁⊑ₕΣ A∈Σ))) B
    ...     | no ¬p = e
    ...     | yes p rewrite ∼-respects-≡ p rtti∼B
            with ∈-⊒ₕ (pw-lift-∈ Σ₁⊑ₕΣ A∈Σ)
    ...       | ⟨ A' , A'∈Σ' ⟩
              with (⊓⟹⊑ₗ rtti∼B)
    ...         | q
                with (⊓ rtti∼B)
    ...           | _ rewrite x
                  with (build-prec (⊑ₕ∈⇒∈ A'∈Σ') q)
    ...             | q3 rewrite Σ-cast/A∈Σ/A≡Σ (⊑ₕ∈⇒∈ A'∈Σ') | Σ⊑ₕΣ≡⊑ₕ-refl q3 | ⊑ₕ-trans-respects-reflˡ Σ₁⊑ₕΣ = e


    infix 3  _,_,_⟶_,_,_
    
    {- State Reduction Rules -}
    
    data _,_,_⟶_,_,_ {Σ Σ₁ T A B} {A∈Σ : A ∈ Σ} {Σ₁⊑ₕΣ : Σ₁ ⊑ₕ Σ}
        (Q  : List (SuspendedCast Σ))
        (M : proj₁ (merge' Σ₁⊑ₕΣ (cast A∈Σ B ∷ Q)) ∣ ∅ ⊢ T)
        (μ  : Store (proj₁ (merge' Σ₁⊑ₕΣ (cast A∈Σ B ∷ Q))) Σ₁)
      : ∀ {Σ₂} {Σ₂⊑ₕΣ₁ : Σ₂ ⊑ₕ Σ₁}
      → (Q' : List (SuspendedCast Σ))
      → (M' : (proj₁ (merge' (⊑ₕ-trans Σ₂⊑ₕΣ₁ Σ₁⊑ₕΣ) Q')) ∣ ∅ ⊢ T)
      → (μ' : Store (proj₁ (merge' (⊑ₕ-trans Σ₂⊑ₕΣ₁ Σ₁⊑ₕΣ) Q')) Σ₂)
      → Set where

      state/update-store :
          (rtti∼B : store-lookup-rtti (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ)) μ ∼ B)
        → ⊓ rtti∼B ≢ store-lookup-rtti (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ)) μ
        → (c : SuccessfulStoreCast (μ-cast Q A∈Σ B Σ₁⊑ₕΣ μ rtti∼B))
          -----------------------------------------------------------------------
        → Q , M , μ
        ⟶ Q ++ proj₁ (get-μ-from-successful-μ-cast c)
          , typeprecise-strenthen-expr
              (⊑ₕ-trans (merge-respects-⊑ₕ' (⊑ₕ-trans (build-prec (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ))
                                                                  (⊓⟹⊑ₗ (rtti≡Σ/∼ (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ)) μ rtti∼B)))
                                                       Σ₁⊑ₕΣ)
                                            Q (proj₁ (get-μ-from-successful-μ-cast c)))
                        (merge-soundness Σ₁⊑ₕΣ A∈Σ (rtti≡Σ/∼ (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ)) μ rtti∼B) Q))
              M
          , proj₂ (get-μ-from-successful-μ-cast c)

      state/error1 :
          (rtti∼B : store-lookup-rtti (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ)) μ ∼ B)
        → (x : ⊓ rtti∼B ≢ store-lookup-rtti (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ)) μ)
        → (y : FailedStoreCast (μ-cast Q A∈Σ B Σ₁⊑ₕΣ μ rtti∼B))
          ------------------------------------------------------------------------
        → Q , M , μ ⟶ (cast A∈Σ B ∷ Q) , error , (μ-error1 A∈Σ μ)

      state/error2 :
          (x : ¬ store-lookup-rtti (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ)) μ ∼ B)
          --------------------------------------------------------------------
        → Q , M , μ ⟶ Q , error , μ-error2 A∈Σ μ x

      state/discard :
          (rtti∼B : store-lookup-rtti (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ)) μ ∼ B)
        → (x : ⊓ rtti∼B ≡ store-lookup-rtti (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ)) μ)
          -------------------------------------------------------------------------
        → Q , M , μ ⟶ Q , e-discard A∈Σ μ M rtti∼B x , μ-discard A∈Σ μ rtti∼B x

    ⟶⟹rtti⊑Σ : ∀ {Σ Σ₁ Σ₂ T A B} {Q Q' : List (SuspendedCast Σ)} {A∈Σ : A ∈ Σ}
                    {Σ₁⊑ₕΣ : Σ₁ ⊑ₕ Σ} {M : proj₁ (merge' Σ₁⊑ₕΣ (cast A∈Σ B ∷ Q)) ∣ ∅ ⊢ T}
                    {μ  : Store (proj₁ (merge' Σ₁⊑ₕΣ (cast A∈Σ B ∷ Q))) Σ₁}
                    {Σ₂⊑ₕΣ₁ : Σ₂ ⊑ₕ Σ₁}
                    {M' : (proj₁ (merge' (⊑ₕ-trans Σ₂⊑ₕΣ₁ Σ₁⊑ₕΣ) Q')) ∣ ∅ ⊢ T}
                    {μ' : Store (proj₁ (merge' (⊑ₕ-trans Σ₂⊑ₕΣ₁ Σ₁⊑ₕΣ) Q')) Σ₂}
      → _,_,_⟶_,_,_ {A∈Σ = A∈Σ} {Σ₁⊑ₕΣ = Σ₁⊑ₕΣ} Q M μ Q' M' μ'
      → Σ₂ ⊑ₕ Σ
    ⟶⟹rtti⊑Σ {A∈Σ = A∈Σ} {Σ₁⊑ₕΣ} {μ = μ} (state/update-store rtti∼B x c) =
      ⊑ₕ-trans (build-prec (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ))
                           (⊓⟹⊑ₗ (rtti≡Σ/∼ (proj₂ (strenthen-ptr/⊑ₕ Σ₁⊑ₕΣ A∈Σ)) μ rtti∼B)))
               Σ₁⊑ₕΣ
    ⟶⟹rtti⊑Σ {Σ₁⊑ₕΣ = Σ₁⊑ₕΣ} (state/error1 _ _ _) = Σ₁⊑ₕΣ
    ⟶⟹rtti⊑Σ {Σ₁⊑ₕΣ = Σ₁⊑ₕΣ} (state/error2 _) = Σ₁⊑ₕΣ
    ⟶⟹rtti⊑Σ {Σ₁⊑ₕΣ = Σ₁⊑ₕΣ} (state/discard _ _) = Σ₁⊑ₕΣ

    ⟶⟹Σ'⊑Σ : ∀ {Σ Σ₁ Σ₂ T A B} {Q Q' : List (SuspendedCast Σ)} {A∈Σ : A ∈ Σ}
                  {Σ₁⊑ₕΣ : Σ₁ ⊑ₕ Σ} {M : proj₁ (merge' Σ₁⊑ₕΣ (cast A∈Σ B ∷ Q)) ∣ ∅ ⊢ T}
                  {μ  : Store (proj₁ (merge' Σ₁⊑ₕΣ (cast A∈Σ B ∷ Q))) Σ₁}
                  {Σ₂⊑ₕΣ₁ : Σ₂ ⊑ₕ Σ₁}
                  {M' : (proj₁ (merge' (⊑ₕ-trans Σ₂⊑ₕΣ₁ Σ₁⊑ₕΣ) Q')) ∣ ∅ ⊢ T}
                  {μ' : Store (proj₁ (merge' (⊑ₕ-trans Σ₂⊑ₕΣ₁ Σ₁⊑ₕΣ) Q')) Σ₂}
      → _,_,_⟶_,_,_ {A∈Σ = A∈Σ} {Σ₁⊑ₕΣ = Σ₁⊑ₕΣ} Q M μ Q' M' μ'
      → proj₁ (merge' (⊑ₕ-trans Σ₂⊑ₕΣ₁ Σ₁⊑ₕΣ) Q') ⊑ₕ Σ
    ⟶⟹Σ'⊑Σ {Q' = Q'} {Σ₁⊑ₕΣ = Σ₁⊑ₕΣ} {Σ₂⊑ₕΣ₁ = Σ₂⊑ₕΣ₁} red =
      ⊑ₕ-trans (proj₂ (proj₂ (merge' Σ'⊑ₕΣ Q'))) (proj₁ (proj₂ (merge' Σ'⊑ₕΣ Q')))
      where Σ'⊑ₕΣ = (⊑ₕ-trans Σ₂⊑ₕΣ₁ Σ₁⊑ₕΣ)
