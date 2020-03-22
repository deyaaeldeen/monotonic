open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Precision
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  where

open import Data.Empty using (⊥-elim)
open import Data.List using ([] ; _∷_)
open import Data.List.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Pointwise
  using (Pointwise ; [] ; _∷_) renaming (refl to pw-refl ; transitive to pw-trans ; map to pw-map)
open import Data.Product using (∃-syntax ; _×_ ; -,_ ; proj₁ ; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary using (Transitive ; Rel)
open import Relation.Binary.HeterogeneousEquality using (_≅_ ; ≅-to-≡) renaming (refl to hrefl)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Relation.Nullary using (yes ; no)

open import MonoRef.Dynamics.Store.Ptr
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Types.Relations


infix  3  _⊑ₕ_
infix  3 _,_∈_

{- Definition 1 (Precision relation on store typings) -}

_⊑ₕ_ : (Σ Σ' : StoreTyping) → Set
_⊑ₕ_ Σ' Σ = Pointwise _⊑_ Σ' Σ

⊑ₕ-refl : ∀ {Σ} → Σ ⊑ₕ Σ
⊑ₕ-refl = pw-refl ⊑-reflexive

⊑ₕ-trans : Transitive _⊑ₕ_
⊑ₕ-trans = pw-trans ⊑-trans

Σ-cast : ∀ {Σ T} → T ∈ Σ → Type → StoreTyping
Σ-cast {x ∷ Σ} (here refl) t = t ∷ Σ
Σ-cast {x ∷ Σ} (there mem) t = x ∷ Σ-cast mem t

build-prec : ∀ {Σ A B} → (A∈Σ : A ∈ Σ) → B ⊑ A → Σ-cast A∈Σ B ⊑ₕ Σ
build-prec (here refl) Σ'⊑ₕΣ = Σ'⊑ₕΣ ∷ ⊑ₕ-refl
build-prec (there A∈Σ) Σ'⊑ₕΣ = ⊑-reflexive ∷ build-prec A∈Σ Σ'⊑ₕΣ

Σ-cast⟹∈ : ∀ {Σ A} → (A∈Σ : A ∈ Σ) → (B : Type) → B ∈ Σ-cast A∈Σ B
Σ-cast⟹∈ (here refl) B = here refl
Σ-cast⟹∈ (there A∈Σ) B = there (Σ-cast⟹∈ A∈Σ B)

⊑ₕ-trans-respects-reflʳ : ∀ {Σ Σ'} → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ) → ⊑ₕ-trans Σ'⊑ₕΣ ⊑ₕ-refl ≡ Σ'⊑ₕΣ
⊑ₕ-trans-respects-reflʳ [] = refl
⊑ₕ-trans-respects-reflʳ (x∼y ∷ Σ'⊑ₕΣ) rewrite ⊑ₕ-trans-respects-reflʳ Σ'⊑ₕΣ | ⊑-trans-respects-reflʳ x∼y = refl

⊑ₕ-trans-respects-reflˡ : ∀ {Σ Σ'} → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ) → ⊑ₕ-trans ⊑ₕ-refl Σ'⊑ₕΣ ≡ Σ'⊑ₕΣ
⊑ₕ-trans-respects-reflˡ [] = refl
⊑ₕ-trans-respects-reflˡ (x∼y ∷ Σ'⊑ₕΣ) rewrite ⊑ₕ-trans-respects-reflˡ Σ'⊑ₕΣ | ⊑-trans-respects-reflˡ x∼y = refl

⊑ₕ-trans-assoc : ∀ {Σ₁ Σ₂ Σ₃ Σ₄}
  → (Σ₄⊑ₕΣ₃ : Σ₄ ⊑ₕ Σ₃)
  → (Σ₃⊑ₕΣ₂ : Σ₃ ⊑ₕ Σ₂)
  → (Σ₂⊑ₕΣ₁ : Σ₂ ⊑ₕ Σ₁)
  → ⊑ₕ-trans (⊑ₕ-trans Σ₄⊑ₕΣ₃ Σ₃⊑ₕΣ₂) Σ₂⊑ₕΣ₁ ≡ ⊑ₕ-trans Σ₄⊑ₕΣ₃ (⊑ₕ-trans Σ₃⊑ₕΣ₂ Σ₂⊑ₕΣ₁)
⊑ₕ-trans-assoc [] [] [] = refl
⊑ₕ-trans-assoc (x∼y ∷ Σ₄⊑ₕΣ₃) (x∼y₁ ∷ Σ₃⊑ₕΣ₂) (x∼y₂ ∷ Σ₂⊑ₕΣ₁)
  rewrite ⊑ₕ-trans-assoc Σ₄⊑ₕΣ₃ Σ₃⊑ₕΣ₂ Σ₂⊑ₕΣ₁
        | ⊑-trans-assoc x∼y x∼y₁ x∼y₂ = refl

weaken-ptr : ∀ {T A Σ}
  → (T∈Σ : T ∈ Σ) → (B : Type) → (A∈Σ : A ∈ Σ)
  → PtrInEquality T∈Σ A∈Σ → T ∈ Σ-cast A∈Σ B
weaken-ptr (here refl) _ (here refl) (PIE-ty _ ¬f) = ⊥-elim (¬f refl)
weaken-ptr (here refl) _ (here refl) (PIE-ptr ¬f _) = ⊥-elim (¬f refl)
weaken-ptr (there T∈Σ) _ (here refl) _ = there T∈Σ
weaken-ptr (here refl) _ (there A∈Σ) _ = here refl
weaken-ptr (there T∈Σ) B (there A∈Σ) (PIE-ty .(there A∈Σ) ¬f) =
  there (weaken-ptr T∈Σ B A∈Σ (PIE-ty A∈Σ λ { refl → ¬f refl}))
weaken-ptr (there T∈Σ) B (there A∈Σ) (PIE-ptr ¬f _) =
  there (weaken-ptr T∈Σ B A∈Σ (PIE-ptr ¬f A∈Σ))

-- Views

data _,_∈_ (t' t : Type) : ∀ {Σ' Σ} → Σ' ⊑ₕ Σ → Set where

  here : ∀ {Σ' Σ} {t'⊑t : t' ⊑ t} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ}
      -------------------------
    → _,_∈_ t' t (t'⊑t ∷ Σ'⊑ₕΣ)

  there : ∀ {x y Σ' Σ} {y⊑x : y ⊑ x} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ}
    → _,_∈_ t' t Σ'⊑ₕΣ
      ------------------------
    → _,_∈_ t' t (y⊑x ∷ Σ'⊑ₕΣ)

data _⊑∈ₗ_ (t : Type) : ∀ {Σ' Σ} → Σ' ⊑ₕ Σ → Set where

  here : ∀ {Σ' Σ t'} {t'⊑t : t' ⊑ t} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ}
      -------------------
    → t ⊑∈ₗ (t'⊑t ∷ Σ'⊑ₕΣ)

  there : ∀ {x y Σ' Σ} {y⊑x : y ⊑ x} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ}
    → t ⊑∈ₗ Σ'⊑ₕΣ
      ------------------
    → t ⊑∈ₗ (y⊑x ∷ Σ'⊑ₕΣ)

data _⊑∈ᵣ_ (t' : Type) : ∀ {Σ' Σ} → Σ' ⊑ₕ Σ → Set where

  here : ∀ {Σ' Σ t} {t'⊑t : t' ⊑ t} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ}
      -------------------
    → t' ⊑∈ᵣ (t'⊑t ∷ Σ'⊑ₕΣ)

  there : ∀ {x y Σ' Σ} {y⊑x : y ⊑ x} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ}
    → t' ⊑∈ᵣ Σ'⊑ₕΣ
      ------------------
    → t' ⊑∈ᵣ (y⊑x ∷ Σ'⊑ₕΣ)

⊒-⊒ₕ : ∀ {Σ' Σ t' t} {prec : Σ' ⊑ₕ Σ} →  _,_∈_ t' t prec → t' ⊑ t
⊒-⊒ₕ {prec = x∼y ∷ _} here = x∼y
⊒-⊒ₕ (there mem) = ⊒-⊒ₕ mem

∈-⊒ₕ : ∀ {Σ' Σ t} {prec : Σ' ⊑ₕ Σ} → t ⊑∈ₗ prec → ∃[ t' ] _,_∈_ t' t prec
∈-⊒ₕ here = -, here
∈-⊒ₕ (there mem) with ∈-⊒ₕ mem
... | ⟨ fst , snd ⟩  = -, there snd

∈ᵣ-⊒ₕ : ∀ {Σ' Σ t'} {prec : Σ' ⊑ₕ Σ} → t' ⊑∈ᵣ prec → ∃[ t ] _,_∈_ t' t prec
∈ᵣ-⊒ₕ here = -, here
∈ᵣ-⊒ₕ (there mem) with ∈ᵣ-⊒ₕ mem
... | ⟨ fst , snd ⟩  = -, there snd

pw-lift-∈ : ∀ {Σ' Σ t} → (prec : Σ' ⊑ₕ Σ) → t ∈ Σ → t ⊑∈ₗ prec
pw-lift-∈ (x∼y ∷ prec) (here refl) = here
pw-lift-∈ (x∼y ∷ prec) (there mem) = there (pw-lift-∈ prec mem)

pw-lift-∈ᵣ : ∀ {Σ' Σ t'} → (prec : Σ' ⊑ₕ Σ) → t' ∈ Σ' → t' ⊑∈ᵣ prec
pw-lift-∈ᵣ (x∼y ∷ prec) (here refl) = here
pw-lift-∈ᵣ (x∼y ∷ prec) (there mem) = there (pw-lift-∈ᵣ prec mem)

∈⇒⊑ₕ∈ : ∀ {Σ' Σ t} → (prec : Σ' ⊑ₕ Σ) → t ∈ Σ → ∃[ t' ] _,_∈_ t' t prec
∈⇒⊑ₕ∈ prec mem = ∈-⊒ₕ (pw-lift-∈ prec mem)

∈⇒⊑ₕ∈ᵣ : ∀ {Σ' Σ t'} → (prec : Σ' ⊑ₕ Σ) → t' ∈ Σ' → ∃[ t ] _,_∈_ t' t prec
∈⇒⊑ₕ∈ᵣ prec mem = ∈ᵣ-⊒ₕ (pw-lift-∈ᵣ prec mem)

⊑ₕ∈⇒∈ : ∀ {Σ' Σ t' t} {prec : Σ' ⊑ₕ Σ} → _,_∈_ t' t prec → t' ∈ Σ'
⊑ₕ∈⇒∈ here = here refl
⊑ₕ∈⇒∈ (there mem) = there (⊑ₕ∈⇒∈ mem)

⊑ₕ∈⇒∈ᵣ : ∀ {Σ' Σ t' t} {prec : Σ' ⊑ₕ Σ} → _,_∈_ t' t prec → t ∈ Σ
⊑ₕ∈⇒∈ᵣ here = here refl
⊑ₕ∈⇒∈ᵣ (there mem) = there (⊑ₕ∈⇒∈ᵣ mem)

∈-⊒ₕ-refl : ∀ {A Σ} → (A∈Σ : A ∈ Σ) → proj₁ (∈-⊒ₕ (pw-lift-∈ ⊑ₕ-refl A∈Σ)) ≡ A
∈-⊒ₕ-refl (here refl) = refl
∈-⊒ₕ-refl (there A∈Σ) rewrite ∈-⊒ₕ-refl A∈Σ = refl

⊑ₕ∈⇒∈-refl : ∀ {A Σ}
  → (A∈Σ : A ∈ Σ) → ⊑ₕ∈⇒∈ (proj₂ (∈-⊒ₕ (pw-lift-∈ ⊑ₕ-refl A∈Σ))) ≅ A∈Σ
⊑ₕ∈⇒∈-refl (here refl) = hrefl
⊑ₕ∈⇒∈-refl (there A∈Σ)
  with ⊑ₕ∈⇒∈ (proj₂ (∈-⊒ₕ (pw-lift-∈ ⊑ₕ-refl A∈Σ))) | ⊑ₕ∈⇒∈-refl A∈Σ
... | w | q rewrite ∈-⊒ₕ-refl A∈Σ | ≅-to-≡ q = hrefl

weaken-ptr/⊑ₕ : ∀ {A Σ Σ'} → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ) → A ∈ Σ' → ∃[ B ] (B ∈ Σ)
weaken-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ' = -, (⊑ₕ∈⇒∈ᵣ (proj₂ (∈⇒⊑ₕ∈ᵣ Σ'⊑ₕΣ A∈Σ')))

strenthen-ptr/⊑ₕ : ∀ {A Σ Σ'} → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ) → A ∈ Σ → ∃[ B ] (B ∈ Σ')
strenthen-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ = -, (⊑ₕ∈⇒∈ (proj₂ (∈⇒⊑ₕ∈ Σ'⊑ₕΣ A∈Σ)))

strenthen-respects-weaken : ∀ {A Σ Σ'}
  → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
  → (A∈Σ : A ∈ Σ')
  → PtrEquality A∈Σ (proj₂ (strenthen-ptr/⊑ₕ Σ'⊑ₕΣ (proj₂ (weaken-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ))))
strenthen-respects-weaken Σ'⊑ₕΣ A∈Σ
  with weaken-ptr/⊑ₕ Σ'⊑ₕΣ A∈Σ
strenthen-respects-weaken Σ'⊑ₕΣ A∈Σ | ⟨ B , B∈Σ ⟩
    with strenthen-ptr/⊑ₕ Σ'⊑ₕΣ B∈Σ
strenthen-respects-weaken (x∼y ∷ Σ'⊑ₕΣ) (here refl) | ⟨ B , B∈Σ ⟩ | ⟨ fst , snd ⟩ = intro
strenthen-respects-weaken (x∼y ∷ Σ'⊑ₕΣ) (there A∈Σ) | ⟨ B , B∈Σ ⟩ | ⟨ fst , snd ⟩
  with proj₁ (∈-⊒ₕ (pw-lift-∈ Σ'⊑ₕΣ (⊑ₕ∈⇒∈ᵣ (proj₂ (∈ᵣ-⊒ₕ (pw-lift-∈ᵣ Σ'⊑ₕΣ A∈Σ))))))
    | (⊑ₕ∈⇒∈ (proj₂ (∈-⊒ₕ (pw-lift-∈ Σ'⊑ₕΣ (⊑ₕ∈⇒∈ᵣ (proj₂ (∈ᵣ-⊒ₕ (pw-lift-∈ᵣ Σ'⊑ₕΣ A∈Σ))))))))
    | strenthen-respects-weaken Σ'⊑ₕΣ A∈Σ
... | _ | _ | intro = intro

{- Lemma 1 (Strengthening wrt. the heap typing) -}

typeprecise-strenthen-expr : ∀ {Σ Σ' Γ A}
  → Σ' ⊑ₕ Σ → Σ ∣ Γ ⊢ A → Σ' ∣ Γ ⊢ A
typeprecise-strenthen-expr _    (` x) = ` x
typeprecise-strenthen-expr prec (ƛ e) = ƛ typeprecise-strenthen-expr prec e
typeprecise-strenthen-expr prec (e · e₁) =
  typeprecise-strenthen-expr prec e · typeprecise-strenthen-expr prec e₁
typeprecise-strenthen-expr _    `zero = `zero
typeprecise-strenthen-expr prec (`suc e) = `suc typeprecise-strenthen-expr prec e
typeprecise-strenthen-expr prec (case e e₁ e₂) =
  case (typeprecise-strenthen-expr prec e)
       (typeprecise-strenthen-expr prec e₁)
       (typeprecise-strenthen-expr prec e₂)
typeprecise-strenthen-expr prec (ref t e) = ref t (typeprecise-strenthen-expr prec e)
typeprecise-strenthen-expr prec (e `× e₁) =
  typeprecise-strenthen-expr prec e `× typeprecise-strenthen-expr prec e₁
typeprecise-strenthen-expr prec (π₁ e) = π₁ typeprecise-strenthen-expr prec e
typeprecise-strenthen-expr prec (π₂ e) = π₂ typeprecise-strenthen-expr prec e
typeprecise-strenthen-expr prec (addr mem prec') with ∈⇒⊑ₕ∈ prec mem
... | ⟨ _ ,  tt'∈prec ⟩ = addr (⊑ₕ∈⇒∈ tt'∈prec) (⊑-trans (⊒-⊒ₕ tt'∈prec) prec')
typeprecise-strenthen-expr prec ((!ₛ e) x) =
  (!ₛ typeprecise-strenthen-expr prec e) x
typeprecise-strenthen-expr prec ((e :=ₛ e₁) x) =
  (typeprecise-strenthen-expr prec e :=ₛ typeprecise-strenthen-expr prec e₁) x
typeprecise-strenthen-expr prec (! A x e) = ! A x (typeprecise-strenthen-expr prec e)
typeprecise-strenthen-expr prec (:= A x e e₁) =
  := A x (typeprecise-strenthen-expr prec e) (typeprecise-strenthen-expr prec e₁)
typeprecise-strenthen-expr _    unit = unit
typeprecise-strenthen-expr prec (e < x >) = typeprecise-strenthen-expr prec e < x >
typeprecise-strenthen-expr _    error = error
