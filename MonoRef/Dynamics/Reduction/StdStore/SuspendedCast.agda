open import MonoRef.Static.Types

module MonoRef.Dynamics.Reduction.StdStore.SuspendedCast
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.Empty using (⊥-elim)
open import Data.List using (List ; [] ; _∷_ ; _++_ ; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product
  using (∃ ; ∃-syntax ; Σ ; Σ-syntax ; _×_ ; -,_ ; proj₁ ; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Nullary using (yes ; no ; ¬_)
open import Relation.Binary.HeterogeneousEquality using (≅-to-≡)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Ptr
open import MonoRef.Dynamics.Store.Std.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Std.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


data SuspendedCast (Σ : StoreTyping) : Set where
  cast : ∀ {A} → (A∈Σ : A ∈ Σ) → Type → SuspendedCast Σ

data QueueStoreTyping {Σ} : ∀ {Σ'} → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ) → (Q : List (SuspendedCast Σ)) → Set where
  normal : QueueStoreTyping (⊑ₕ-refl {Σ = Σ}) []
  evolving : ∀ {A B Σ'} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ} → (Q : List (SuspendedCast Σ)) → (A∈Σ : A ∈ Σ) → QueueStoreTyping Σ'⊑ₕΣ (cast A∈Σ B ∷ Q)

merge' : ∀ {Σ Σ'}
  → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ) → List (SuspendedCast Σ) → ∃[ Σ'' ] ((Σ' ⊑ₕ Σ) × (Σ'' ⊑ₕ Σ'))
merge' Σ'⊑ₕΣ [] = -, ⟨ Σ'⊑ₕΣ , ⊑ₕ-refl ⟩
merge' Σ'⊑ₕΣ (cast A∈Σ B ∷ l)
  with strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ
... | ⟨ A' , A'∈Σ' ⟩
    with ∼-decidable A' B
...   | no _ = merge' Σ'⊑ₕΣ l
...   | yes A∼B = -, ⟨ Σ'⊑ₕΣ , ⊑ₕ-trans Σ''⊑ₕΣ' (build-prec A'∈Σ' (⊓⟹⊑ₗ A∼B)) ⟩
  where
    Σ''⊑ₕΣ' = proj₂ (proj₂ (merge' (⊑ₕ-trans (build-prec A'∈Σ' (⊓⟹⊑ₗ A∼B)) Σ'⊑ₕΣ) l))

merge : ∀ {Σ} → List (SuspendedCast Σ) → ∃[ Σ' ] (Σ' ⊑ₕ Σ)
merge l = -, ⊑ₕ-trans (proj₂ (proj₂ r)) (proj₁ (proj₂ r))
  where
    r = merge' ⊑ₕ-refl l

merge-respects-⊑ₕ' : ∀ {Σ Σ'}
  → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ) → (Q Q' : List (SuspendedCast Σ))
  → proj₁ (merge' Σ'⊑ₕΣ (Q ++ Q')) ⊑ₕ proj₁ (merge' Σ'⊑ₕΣ Q)
merge-respects-⊑ₕ' Σ'⊑ₕΣ [] Q' = proj₂ (proj₂ (merge' Σ'⊑ₕΣ Q'))
merge-respects-⊑ₕ' Σ'⊑ₕΣ (cast A∈Σ B ∷ Q) Q'
  with ∼-decidable (proj₁ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ)) B
... | no _ = merge-respects-⊑ₕ' Σ'⊑ₕΣ Q Q'
... | yes A∼B =
  merge-respects-⊑ₕ' (⊑ₕ-trans (build-prec (⊑ₕ∈⇒∈ (proj₂ (∈-⊒ₕ (pw-lift-∈ Σ'⊑ₕΣ A∈Σ))))
                                           (⊓⟹⊑ₗ A∼B))
                               Σ'⊑ₕΣ)
                     Q Q'

merge-soundness : ∀ {Σ Σ' A B}
  → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
  → (A∈Σ : A ∈ Σ)
  → (A∼B : proj₁ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ) ∼ B)
  → (Q : List (SuspendedCast Σ))
  → proj₁ (merge' (⊑ₕ-trans (build-prec (proj₂ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ)) (⊓⟹⊑ₗ A∼B)) Σ'⊑ₕΣ) Q) ⊑ₕ proj₁ (merge' Σ'⊑ₕΣ (cast A∈Σ B ∷ Q))
merge-soundness {B = B} Σ'⊑ₕΣ A∈Σ A∼B Q
  with ∼-decidable (proj₁ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ)) B
... | no ¬p = ⊥-elim (¬p A∼B)
... | yes p rewrite ∼-respects-≡ p A∼B = ⊑ₕ-refl

merge'-respects-++' : ∀ {Σ Σ'}
  → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
  → (Q Q' : List (SuspendedCast Σ))
  → proj₁ (merge' Σ'⊑ₕΣ (Q ++ Q'))
  ≡ proj₁ (merge' (⊑ₕ-trans (proj₂ (proj₂ (merge' Σ'⊑ₕΣ Q))) Σ'⊑ₕΣ) Q')
merge'-respects-++' Σ'⊑ₕΣ [] Q' rewrite ⊑ₕ-trans-respects-reflˡ Σ'⊑ₕΣ = refl
merge'-respects-++' Σ'⊑ₕΣ (cast {A} A∈Σ B ∷ Q) Q'
  with (∈-⊒ₕ (pw-lift-∈ Σ'⊑ₕΣ A∈Σ))
...   | ⟨ A' , A'∈Σ' ⟩ rewrite ∈-⊒ₕ-refl A∈Σ
    with ∼-decidable A' B
... | no ¬p = merge'-respects-++' Σ'⊑ₕΣ Q Q'
... | yes p
  rewrite ⊑ₕ-trans-assoc (proj₂ (proj₂ (merge' (⊑ₕ-trans (build-prec (⊑ₕ∈⇒∈ A'∈Σ') (⊓⟹⊑ₗ p)) Σ'⊑ₕΣ) Q)))
                         (build-prec (⊑ₕ∈⇒∈ A'∈Σ') (⊓⟹⊑ₗ p)) Σ'⊑ₕΣ
        | merge'-respects-++' (⊑ₕ-trans (build-prec (⊑ₕ∈⇒∈ A'∈Σ') (⊓⟹⊑ₗ p)) Σ'⊑ₕΣ) Q Q' = refl

merge'-ret-in : ∀ {Σ Σ'}
  → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ) → (Q : List (SuspendedCast Σ)) → (proj₁ (proj₂ (merge' Σ'⊑ₕΣ Q))) ≡ Σ'⊑ₕΣ
merge'-ret-in Σ'⊑ₕΣ [] = refl
merge'-ret-in Σ'⊑ₕΣ (cast A∈Σ B ∷ Q)
  with ∼-decidable (proj₁ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ)) B
... | no _  = merge'-ret-in Σ'⊑ₕΣ Q
... | yes _ = refl

merge-extension-soundness : ∀ {Σ Σ' A B}
  → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
  → (Q : List (SuspendedCast Σ))
  → (A∈mergeQ : A ∈ proj₁ (merge' Σ'⊑ₕΣ Q))
  → (A∼B : A ∼ B)
  → ⊓ A∼B ∈ proj₁ (merge' Σ'⊑ₕΣ (Q ++ [ cast (proj₂ (weaken-ptr/⊑ₕ (⊑ₕ-trans (proj₂ (proj₂ (merge' Σ'⊑ₕΣ Q))) (proj₁ (proj₂ (merge' Σ'⊑ₕΣ Q)))) A∈mergeQ)) B ]))
merge-extension-soundness {B = B} Σ'⊑ₕΣ Q A∈mergeQ A∼B
  rewrite merge'-respects-++' Σ'⊑ₕΣ Q [ cast (proj₂ (weaken-ptr/⊑ₕ (⊑ₕ-trans (proj₂ (proj₂ (merge' Σ'⊑ₕΣ Q))) (proj₁ (proj₂ (merge' Σ'⊑ₕΣ Q)))) A∈mergeQ)) B ]
        | merge'-ret-in Σ'⊑ₕΣ Q
  with (proj₁ (∈-⊒ₕ (pw-lift-∈ (⊑ₕ-trans (proj₂ (proj₂ (merge' Σ'⊑ₕΣ Q))) Σ'⊑ₕΣ) (⊑ₕ∈⇒∈ᵣ (proj₂ (∈ᵣ-⊒ₕ (pw-lift-∈ᵣ (⊑ₕ-trans (proj₂ (proj₂ (merge' Σ'⊑ₕΣ Q))) Σ'⊑ₕΣ) A∈mergeQ)))))))
     | ⊑ₕ∈⇒∈ (proj₂ (∈-⊒ₕ (pw-lift-∈ (⊑ₕ-trans (proj₂ (proj₂ (merge' Σ'⊑ₕΣ Q))) Σ'⊑ₕΣ) (⊑ₕ∈⇒∈ᵣ (proj₂ (∈ᵣ-⊒ₕ (pw-lift-∈ᵣ (⊑ₕ-trans (proj₂ (proj₂ (merge' Σ'⊑ₕΣ Q))) Σ'⊑ₕΣ) A∈mergeQ)))))))
     | strenthen-respects-weaken (⊑ₕ-trans (proj₂ (proj₂ (merge' Σ'⊑ₕΣ Q))) Σ'⊑ₕΣ) A∈mergeQ
... | A | _ | intro
    with ∼-decidable A B
... | no ¬A∼B = ⊥-elim (¬A∼B A∼B)
... | yes A∼B' rewrite ∼-respects-≡ A∼B' A∼B = Σ-cast⟹∈ A∈mergeQ (⊓ A∼B)

module ParamSuspendedCast
  (Value : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  where

  open ParamStoreValue Value
  open ParamStoreDef StoreValue

  data CastResult {Σ Σ'} (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ) (Q : List (SuspendedCast Σ)) (B : Type) : Set where
    error :
        CastResult Σ'⊑ₕΣ Q B

    done :
        (Q' : List (SuspendedCast Σ))
      → ∀ {M : proj₁ (merge' Σ'⊑ₕΣ (Q ++ Q')) ∣ ∅ ⊢ B}
      → Value M
        -----------------------------
      → CastResult Σ'⊑ₕΣ Q B

  data StorePartialCast {Σ Σ' A B}
    (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
    (Q : List (SuspendedCast Σ))
    (A∈Σ : A ∈ Σ)
    (B⊑A : B ⊑ (proj₁ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ))) : Set where
    error :
        --------------------------------
        StorePartialCast Σ'⊑ₕΣ Q A∈Σ B⊑A

    done :
        (Q' : List (SuspendedCast Σ))
      → Store (proj₁ (merge' (⊑ₕ-trans (build-prec (proj₂ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ)) B⊑A) Σ'⊑ₕΣ)
                             (Q ++ Q')))
              (Σ-cast (proj₂ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ)) B)
        -------------------------------------------------------------------------------------------
      → StorePartialCast Σ'⊑ₕΣ Q A∈Σ B⊑A

  data SuccessfulCast {Σ Σ' B} {Q : List (SuspendedCast Σ)} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ} : CastResult Σ'⊑ₕΣ Q B → Set where
    intro :
        (Q' : List (SuspendedCast Σ))
      → ∀ {M : proj₁ (merge' Σ'⊑ₕΣ (Q ++ Q')) ∣ ∅ ⊢ B}
      → (v : Value M)
        ------------------------------
      → SuccessfulCast (done Q' v)

  data FailedCast {Σ Σ' B} {Q : List (SuspendedCast Σ)} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ} : CastResult Σ'⊑ₕΣ Q B → Set where
    intro : FailedCast error

  data SuccessfulStoreCast {Σ Σ' A B} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ} {Q : List (SuspendedCast Σ)}
                           {A∈Σ : A ∈ Σ} {B⊑A : B ⊑ proj₁ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ)}
                           : StorePartialCast Σ'⊑ₕΣ Q A∈Σ B⊑A → Set where
    intro :
        (Q' : List (SuspendedCast Σ))
      → (μ' : Store (proj₁ (merge' (⊑ₕ-trans (build-prec (proj₂ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ)) B⊑A) Σ'⊑ₕΣ)
                                   (Q ++ Q')))
              (Σ-cast (proj₂ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ)) B))
        -------------------------------------------------------------------------------------------------
      → SuccessfulStoreCast (done Q' μ')

  data FailedStoreCast {Σ Σ' A B} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ} {Q : List (SuspendedCast Σ)}
                       {A∈Σ : A ∈ Σ} {B⊑A : B ⊑ proj₁ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ)}
                       : StorePartialCast Σ'⊑ₕΣ Q A∈Σ B⊑A → Set where
    intro :
        FailedStoreCast error

  get-val-from-successful-cast :
    ∀ {Σ Σ' B} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ} {Q : List (SuspendedCast Σ)}
      {c : CastResult Σ'⊑ₕΣ Q B}
    → SuccessfulCast c → Σ[ Q' ∈ List (SuspendedCast Σ) ] (Σ[ M ∈ proj₁ (merge' Σ'⊑ₕΣ (Q ++ Q')) ∣ ∅ ⊢ B ] Value M)
  get-val-from-successful-cast (intro Q' v) = -, -, v

  get-μ-from-successful-μ-cast :
    ∀ {Σ Σ' A B} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ} {Q : List (SuspendedCast Σ)} {A∈Σ : A ∈ Σ}
      {B⊑A : B ⊑ proj₁ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ)}
      {spc : StorePartialCast Σ'⊑ₕΣ Q A∈Σ B⊑A}
    → SuccessfulStoreCast spc → Σ[ Q' ∈ List (SuspendedCast Σ) ]
      (Store (proj₁ (merge' (⊑ₕ-trans (build-prec (proj₂ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ)) B⊑A) Σ'⊑ₕΣ)
                                   (Q ++ Q')))
              (Σ-cast (proj₂ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ)) B))
  get-μ-from-successful-μ-cast (intro Q' μ') = -, μ'

  successful-cast? : ∀ {Σ Σ' B} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ} {Q : List (SuspendedCast Σ)}
    → (c : CastResult Σ'⊑ₕΣ Q B) → SuccessfulCast c ⊎ FailedCast c
  successful-cast? error = inj₂ intro
  successful-cast? (done Q' v) = inj₁ (intro Q' v)

  successful-μ-cast? :
    ∀ {Σ Σ' A B} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ} {Q : List (SuspendedCast Σ)} {A∈Σ : A ∈ Σ}
      {B⊑A : B ⊑ proj₁ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ)}
    → (c : StorePartialCast Σ'⊑ₕΣ Q A∈Σ B⊑A) → SuccessfulStoreCast c ⊎ FailedStoreCast c
  successful-μ-cast? error = inj₂ intro
  successful-μ-cast? (done Q' μ) = inj₁ (intro Q' μ)
