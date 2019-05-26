{-

  MonoRef.Dynamics.Store.Efficient instantiates MonoRef.Dynamics.Store.Base with
  the right efficient definitions and re-exports all store definitions. It is
  paramaterized by the semantics of coercions and requires a compose operator.

-}

open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)

open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations

module MonoRef.Dynamics.Store.Efficient
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  (Active : ∀ {A B} → A ⟹ B → Set)
  (inertP : ∀ {A B} → (c : A ⟹ B) → Dec (Inert c))
  (¬Inert⇒Active : ∀ {A B} {c : A ⟹ B} → ¬ Inert c → Active c)
  (make-coercion : ∀ A B → A ⟹ B)
  (Inert⇒¬Ref : ∀ {A B} {c : A ⟹ Ref B} → Inert c → ⊥)
  (compose : ∀ {A B C} → A ⟹ B → B ⟹ C → A ⟹ C)
  where

open import Data.List.All using (All)
open import Data.List.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Pointwise using (Pointwise ; _∷_)
open import Data.Product
  using (∃-syntax ; Σ ; Σ-syntax ; _×_ ; -,_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (refl)

open import MonoRef.Dynamics.Efficient.Value
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Base
  _⟹_ Inert Inert⇒¬Ref
open import MonoRef.Dynamics.Store.Efficient.Utilities
  _⟹_ Inert Inert⇒¬Ref public
open import MonoRef.Dynamics.Store.Normal
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert public
open import MonoRef.Dynamics.Store.Efficient.CastedValue
  _⟹_ Inert Active public
open import MonoRef.Dynamics.Store.Efficient.ExtensionWeakening
  _⟹_ Inert Active public
open import MonoRef.Dynamics.Store.Efficient.PrecisionStrenthening
  _⟹_ Inert Active public
open import MonoRef.Dynamics.Store.Ptr public
open import MonoRef.Dynamics.Store.Store
  _⟹_ Inert Inert⇒¬Ref
open import MonoRef.Dynamics.Store.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context


open ParamStoreValue Value CastedValue StrongCastedValue public
open ParamStoreDef StoreValue public
open ParamStore
  Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑ public
open ParamNormal Value CastedValue StrongCastedValue public
open ParamNormalDecidable scv-decidable public


¬NormalStore⇒∃cv : ∀ {Σ Σ'} {ν : StoreUnder Σ Σ'}
  → ¬ NormalStore ν
  → ∃[ A ] (A ∈ Σ' × (Σ[ cv ∈ EvolvingStoreValue A Σ ] StronglyEvolvingStoreValue cv))
¬NormalStore⇒∃cv {ν = All.[]} ν-¬NS = ⊥-elim (ν-¬NS NS-Z)
¬NormalStore⇒∃cv {ν = fromNormalValue (intro v _) All.∷ ν} ν-¬NS
  with normalStoreP ν
... | yes p = ⊥-elim (ν-¬NS (NS-S p v))
... | no ¬p with ¬NormalStore⇒∃cv ¬p
...   | ⟨ _ , ⟨ A∈Σ , cv ⟩ ⟩ = -, ⟨ there A∈Σ , cv ⟩
¬NormalStore⇒∃cv {ν = fromCastedValue (intro (v⇑ v) _) All.∷ ν'} ν-¬NS
  with normalStoreP ν'
... | yes ν'-NS = ⊥-elim (ν-¬NS (NS-S' ν'-NS (λ ())))
... | no ν'-¬NS with ¬NormalStore⇒∃cv ν'-¬NS
...   | ⟨ _ , ⟨ A∈Σ , cv ⟩ ⟩ = -, ⟨ there A∈Σ , cv ⟩
¬NormalStore⇒∃cv {ν = fromCastedValue v@(intro (cast-val cv c) T) All.∷ _} _ =
  -, ⟨ here refl , ⟨ v , intro (SCV-cast cv c) T ⟩ ⟩
¬NormalStore⇒∃cv {ν = fromCastedValue v@(intro (cv-pair  cv₁ cv₂ p) T) All.∷ _} _ =
  -, ⟨ here refl , ⟨ v , intro (SCV-pair cv₁ cv₂ p) T ⟩ ⟩

private

  data Value∧Cast {A B Σ Γ} {e : Σ ∣ Γ ⊢ A} (v : Value e) (c : A ⟹ B) : Set where
    V∧C-inert : ∀ {e' : Σ ∣ Γ ⊢ B} → Value e' → Value∧Cast v c
    V∧C-active : ∀ {A'} {e' : Σ ∣ Γ ⊢ A'} {d : A' ⟹ B} → Value e' → Active d → Value∧Cast v c
  
  cast-value/compose : ∀ {A B Σ Γ} {e : Σ ∣ Γ ⊢ A}
    → (v : Value e) → (c : A ⟹ B) → Value∧Cast v c
  cast-value/compose (S-Val v) c
    with inertP c
  ... | yes c-inert = V∧C-inert (V-cast v c-inert)
  ... | no c-¬inert = V∧C-active (S-Val v) (¬Inert⇒Active c-¬inert)
  cast-value/compose (V-cast {c = c} sv _) d
    with inertP (compose c d)
  ... | yes c-inert = V∧C-inert (V-cast sv c-inert)
  ... | no c-¬inert = V∧C-active (S-Val sv) (¬Inert⇒Active c-¬inert)

  {-

    all-⊑ₕ does the second step in the process of casting a store. It strenthens
    the store typing given that all elements are already strenthened.

  -}

  all-⊑ₕ : ∀ {Σ Σ' : StoreTyping}
    → All (λ ty → StoreValue ty Σ') Σ
    → Σ' ⊑ₕ Σ
    → All (λ ty → StoreValue ty Σ') Σ'
  all-⊑ₕ ν Σ'⊑ₕΣ = pw-map' update-type Σ'⊑ₕΣ ν
    where
  
      cast-casted-value : ∀ {A B Σ} {e : Σ ∣ ∅ ⊢ A}
        → B ⊑ A
        → CastedValue e
        → Σ[ e' ∈ Σ ∣ ∅ ⊢ B ] (Value e' ⊎ (Σ[ cv' ∈ CastedValue e' ] StrongCastedValue cv'))
      cast-casted-value _ (v⇑ v)
        with cast-value/compose v (make-coercion _ _)
      ... | V∧C-inert v' = -, (inj₁ v')
      ... | V∧C-active v' d = -, (inj₂ (-, (SCV-cast v' d)))
      cast-casted-value _ (cast-val {c = c} v _)
        with cast-value/compose v (compose c (make-coercion _ _))
      ... | V∧C-inert  v'   = -, (inj₁ v')
      ... | V∧C-active v' d = -, (inj₂ (-, (SCV-cast v' d)))
      cast-casted-value ⊑-refl (cv-pair _ _ p) = -, (inj₂ (-, (SCV-pair _ _ p)))
      cast-casted-value (⊑-× ext1 ext2) (cv-pair cv₁ cv₂ p)
        with cast-casted-value ext1 cv₁ | cast-casted-value ext2 cv₂
      ... | ⟨ _ , a ⟩ | ⟨ _ , b ⟩
        with a | b
      ...  | inj₂ ⟨ _ , scv₁' ⟩ | inj₁ v =
        -, (inj₂ (-, (SCV-pair _ (v⇑ v) (inj₁ ⟨ scv₁' , v ⟩))))
      ...  | inj₂ ⟨ _ , scv₁' ⟩ | inj₂ ⟨ _ , scv₂' ⟩ =
        -, (inj₂ (-, (SCV-pair _ _ (inj₂ (inj₂ ⟨ scv₁' , scv₂' ⟩)))))  
      ...  | inj₁ v₁ | inj₁ v₂ = -, (inj₁ (S-Val (V-pair v₁ v₂)))
      ...  | inj₁ v | inj₂ ⟨ _ , scv₂' ⟩ =
        -, (inj₂ (-, (SCV-pair (v⇑ v) _ (inj₂ (inj₁ ⟨ v , scv₂' ⟩))))) 
  
      update-type : ∀ {A B Σ} → B ⊑ A → StoreValue A Σ → StoreValue B Σ
      update-type _ (fromNormalValue (intro v ty))
        with cast-value/compose v (make-coercion _ _)
      ... | V∧C-inert  v'   = fromNormalValue (intro v' (Type⇑ _))
      ... | V∧C-active v' d = fromCastedValue (intro (cast-val v' d) (Type⇑ _))
  
      update-type B⊑A (fromCastedValue (intro cv _))
        with cast-casted-value B⊑A cv
      ... | ⟨ _ , inj₁ v           ⟩ = fromNormalValue (intro v   (Type⇑ _))
      ... | ⟨ _ , inj₂ ⟨ cv' , _ ⟩ ⟩ = fromCastedValue (intro cv' (Type⇑ _))
  
      -- a modified version of pw-map where the relation is anti-symmetric and
      -- points left
      pw-map' : ∀ {a ℓ}{A : Set a}{_∼_ : Rel A ℓ} {l m p}{P : A → Set p}
        → (∀ {a b} → a ∼ b → P b → P a) → Pointwise _∼_ m l → All P l → All P m
      pw-map' f Pointwise.[] All.[] = All.[]
      pw-map' f (x∼y ∷ r) (px All.∷ xs) = f x∼y px All.∷ pw-map' f r xs


ν-update/ref : ∀ {A Σ Γ} {r : Σ ∣ Γ ⊢ Ref A}
  → (R : Value r) → Store Σ → ∀ {e : Σ ∣ ∅ ⊢ A} → Value e → Store Σ
ν-update/ref R ν v
  with cast-value/compose v (make-coercion _ (ref⟹T R))
... | V∧C-inert  v'   = μ-update (ref⟹∈ R) ν v'
... | V∧C-active v' d = ν-update (ref⟹∈ R) ν (cast-val v' d)

{- Re-exported concrete definitions -}

open ParamBase Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑
open StoreExtend prefix-weaken-val prefix-weaken-cv public
open Corollary1 typeprecise-strenthen-val typeprecise-strenthen-cv all-⊑ₕ public

open import MonoRef.Dynamics.Store.TypingProgress
  _⟹_ Inert public
