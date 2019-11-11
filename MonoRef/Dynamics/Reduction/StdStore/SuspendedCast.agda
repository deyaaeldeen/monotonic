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

merge-respects-⊑ₕ : ∀ {Σ}
  → (Q Q' : List (SuspendedCast Σ)) → proj₁ (merge (Q ++ Q')) ⊑ₕ proj₁ (merge Q)
merge-respects-⊑ₕ Q Q' = merge-respects-⊑ₕ' ⊑ₕ-refl Q Q'

merge-soundness : ∀ {Σ A B}
  → (A∈Σ : A ∈ Σ) → (A∼B : A ∼ B) → (Q : List (SuspendedCast Σ))
  → proj₁ (merge' (build-prec A∈Σ (⊓⟹⊑ₗ A∼B)) Q) ⊑ₕ proj₁ (merge (cast A∈Σ B ∷ Q))
merge-soundness {A = A}{B} A∈Σ A∼B Q
  with ⊑ₕ∈⇒∈ (proj₂ (∈-⊒ₕ (pw-lift-∈ ⊑ₕ-refl A∈Σ))) | ⊑ₕ∈⇒∈-refl A∈Σ
... | A'∈Σ | q rewrite ∈-⊒ₕ-refl A∈Σ | ≅-to-≡ q
    with ∼-decidable A B
...   | no ¬p = ⊥-elim (¬p A∼B)
...   | yes p
  rewrite ∼-respects-≡ p A∼B
        | ⊑ₕ-trans-respects-reflʳ (build-prec A∈Σ (⊓⟹⊑ₗ A∼B)) = ⊑ₕ-refl

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

merge'-respects-++ : ∀ {Σ}
  → (Q Q' : List (SuspendedCast Σ))
  → proj₁ (merge (Q ++ Q')) ≡ proj₁ (merge' (proj₂ (merge Q)) Q')
merge'-respects-++ {Σ = Σ} [] Q' rewrite ⊑ₕ-trans-respects-reflʳ {Σ = Σ} ⊑ₕ-refl = refl
merge'-respects-++ (cast {A} A∈Σ B ∷ Q) Q'
  with ⊑ₕ∈⇒∈ (proj₂ (∈-⊒ₕ (pw-lift-∈ ⊑ₕ-refl A∈Σ)))
... | A'∈Σ rewrite ∈-⊒ₕ-refl A∈Σ
    with ∼-decidable A B
...   | no ¬p rewrite merge'-respects-++ Q Q' = refl
...   | yes p
  rewrite ⊑ₕ-trans-respects-reflʳ (build-prec A'∈Σ (⊓⟹⊑ₗ p))
        | ⊑ₕ-trans-respects-reflʳ (⊑ₕ-trans (proj₂ (proj₂ (merge' (build-prec A'∈Σ (⊓⟹⊑ₗ p)) Q))) (build-prec A'∈Σ (⊓⟹⊑ₗ p)))
        | merge'-respects-++' (build-prec A'∈Σ (⊓⟹⊑ₗ p)) Q Q' = refl

merge-extension-soundness : ∀ {Σ A B}
  → (Q : List (SuspendedCast Σ))
  → (A∈mergeQ : A ∈ proj₁ (merge Q))
  → (A∼B : A ∼ B) → ⊓ A∼B ∈ proj₁ (merge (Q ++ [ cast (proj₂ (weaken-ptr/⊑ₕ (proj₂ (merge Q)) A∈mergeQ)) B ]))
merge-extension-soundness {B = B} Q A∈mergeQ A∼B
  rewrite merge'-respects-++ Q [ cast (proj₂ (weaken-ptr/⊑ₕ (proj₂ (merge Q)) A∈mergeQ)) B ]
  with proj₁ (∈-⊒ₕ (pw-lift-∈ Σ'⊑ₕΣ (⊑ₕ∈⇒∈ᵣ (proj₂ (∈ᵣ-⊒ₕ (pw-lift-∈ᵣ Σ'⊑ₕΣ A∈mergeQ))))))
     | ⊑ₕ∈⇒∈ (proj₂ (∈-⊒ₕ (pw-lift-∈ Σ'⊑ₕΣ (⊑ₕ∈⇒∈ᵣ (proj₂ (∈ᵣ-⊒ₕ (pw-lift-∈ᵣ Σ'⊑ₕΣ A∈mergeQ)))))))
     | strenthen-respects-weaken Σ'⊑ₕΣ A∈mergeQ
  where Σ'⊑ₕΣ = ⊑ₕ-trans (proj₂ (proj₂ (merge' ⊑ₕ-refl Q))) (proj₁ (proj₂ (merge' ⊑ₕ-refl Q)))
... | A | _ | intro
    with ∼-decidable A B
... | no ¬A∼B = ⊥-elim (¬A∼B A∼B)
... | yes A∼B' rewrite ∼-respects-≡ A∼B' A∼B = Σ-cast⟹∈ A∈mergeQ (⊓ A∼B)

module ParamSuspendedCast
  (Value : ∀ {Σ Γ A} → Σ ∣ Γ ⊢ A → Set)
  where

  open ParamStoreValue Value
  open ParamStoreDef StoreValue

  data CastResult {Σ} (Q : List (SuspendedCast Σ)) (A : Type) : Set where
    error :
        ------------------
        CastResult Q A
  
    done :
        (Q' : List (SuspendedCast Σ))
      → ∀ {M : proj₁ (merge (Q ++ Q')) ∣ ∅ ⊢ A}
      → Value M
        -----------------------------
      → CastResult Q A

  data StorePartialCast {Σ A B} (Q : List (SuspendedCast Σ)) (A∈Σ : A ∈ Σ) (B⊑A : B ⊑ A) : Set where
    error :
        --------------------------
        StorePartialCast Q A∈Σ B⊑A

    done :
        (Q' : List (SuspendedCast Σ))
      → Store (proj₁ (merge' (build-prec A∈Σ B⊑A) (Q ++ Q'))) (Σ-cast A∈Σ B)
        --------------------------------------------------------------------
      → StorePartialCast Q A∈Σ B⊑A

  data SuccessfulCast {Σ A} {Q : List (SuspendedCast Σ)} : CastResult Q A → Set where
    intro :
        (Q' : List (SuspendedCast Σ))
      → ∀ {M : proj₁ (merge (Q ++ Q')) ∣ ∅ ⊢ A}
      → (v : Value M)
        ------------------------------
      → SuccessfulCast (done Q' v)

  data FailedCast {Σ A} {Q : List (SuspendedCast Σ)} : CastResult Q A → Set where
    intro : FailedCast error

  data SuccessfulStoreCast {Σ A B} {Q : List (SuspendedCast Σ)} {A∈Σ : A ∈ Σ} {B⊑A : B ⊑ A} : StorePartialCast Q A∈Σ B⊑A → Set where
    intro :
        (Q' : List (SuspendedCast Σ))
      → (μ' : Store (proj₁ (merge' (build-prec A∈Σ B⊑A) (Q ++ Q'))) (Σ-cast A∈Σ B))
        ---------------------------------------------------------------------------
      → SuccessfulStoreCast (done Q' μ')

  data FailedStoreCast {Σ A B} {Q : List (SuspendedCast Σ)} {A∈Σ : A ∈ Σ} {B⊑A : B ⊑ A} : StorePartialCast Q A∈Σ B⊑A → Set where
    intro : FailedStoreCast error

  get-val-from-successful-cast : ∀ {Σ A} {Q : List (SuspendedCast Σ)} {c : CastResult Q A}
    → SuccessfulCast c → Σ[ Q' ∈ List (SuspendedCast Σ) ] (Σ[ M ∈ proj₁ (merge (Q ++ Q')) ∣ ∅ ⊢ A ] Value M)
  get-val-from-successful-cast (intro Q' v) = -, -, v

  get-μ-from-successful-μ-cast : ∀ {Σ A B} {Q : List (SuspendedCast Σ)} {A∈Σ : A ∈ Σ} {B⊑A : B ⊑ A}
                                   {spc : StorePartialCast Q A∈Σ B⊑A}
    → SuccessfulStoreCast spc → Σ[ Q' ∈ List (SuspendedCast Σ) ]
      (Store (proj₁ (merge' (build-prec A∈Σ B⊑A) (Q ++ Q'))) (Σ-cast A∈Σ B))
  get-μ-from-successful-μ-cast (intro Q' μ') = -, μ'

  successful-cast? : ∀ {Σ A} {Q : List (SuspendedCast Σ)} → (c : CastResult Q A) → SuccessfulCast c ⊎ FailedCast c
  successful-cast? error = inj₂ intro
  successful-cast? (done Q' v) = inj₁ (intro Q' v)

  successful-μ-cast? : ∀ {Σ A B} {Q : List (SuspendedCast Σ)} {A∈Σ : A ∈ Σ} {B⊑A : B ⊑ A}
    → (c : StorePartialCast Q A∈Σ B⊑A) → SuccessfulStoreCast c ⊎ FailedStoreCast c
  successful-μ-cast? error = inj₂ intro
  successful-μ-cast? (done Q' x) = inj₁ (intro Q' x)
