{-

  MonoRef.Dynamics.Store.Simple instantiates MonoRef.Dynamics.Store.Base with
  the right simple (space-inefficient) definitions and re-exports all store
  definitions. It is paramaterized by the semantics of coercions.

-}

open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)

open import MonoRef.Static.Types

module MonoRef.Dynamics.Store.Simple
  (_⟹_ : Type → Type → Set)
  (Inert : ∀ {A B} → A ⟹ B → Set)
  (Active : ∀ {A B} → A ⟹ B → Set)
  (inertP : ∀ {A B} → (c : A ⟹ B) → Dec (Inert c))
  (¬Inert⇒Active : ∀ {A B} {c : A ⟹ B} → ¬ Inert c → Active c)
  (make-coercion : ∀ A B → A ⟹ B)
  (Inert⇒¬Ref : ∀ {A B} {c : A ⟹ Ref B} → Inert c → ⊥)
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

open import MonoRef.Dynamics.Simple.Value
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Base
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Normal
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Precision
  _⟹_ Inert public
open import MonoRef.Dynamics.Store.Ptr public
open import MonoRef.Dynamics.Store.Simple.CastedValue
  _⟹_ Inert Active public
open import MonoRef.Dynamics.Store.Simple.ExtensionWeakening
  _⟹_ Inert Active public
open import MonoRef.Dynamics.Store.Simple.PrecisionStrenthening
  _⟹_ Inert Active public
open import MonoRef.Dynamics.Store.Store
  _⟹_ Inert
open import MonoRef.Dynamics.Store.StoreDef
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Simple.Utilities
  _⟹_ Inert Inert⇒¬Ref public
open import MonoRef.Dynamics.Store.Value
  _⟹_ Inert
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


open ParamStoreValue Value CastedValue StrongCastedValue public
open ParamStoreDef StoreValue public
open ParamStore
  Value Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑ public
open ParamNormal
  Value CastedValue StrongCastedValue public
open ParamNormalDecidable scv-decidable public


¬NormalStore⇒∃cv : ∀ {Σ Σ'} {ν : StoreUnder Σ Σ'}
  → ¬ NormalStore ν
  → ∃[ A ] (A ∈ Σ' × (Σ[ cv ∈ EvolvingStoreValue A Σ ] StronglyEvolvingStoreValue cv))
¬NormalStore⇒∃cv {ν = All.[]} ¬ν-NS = ⊥-elim (¬ν-NS NS-Z)
¬NormalStore⇒∃cv {ν = fromNormalValue (intro v _) All.∷ ν} ¬ν-NS
  with normalStoreP ν
... | yes p = ⊥-elim (¬ν-NS (NS-S p v))
... | no ¬p with ¬NormalStore⇒∃cv ¬p
...   | ⟨ _ , ⟨ A∈Σ , cv ⟩ ⟩ = -, ⟨ there A∈Σ , cv ⟩
¬NormalStore⇒∃cv {ν = fromCastedValue (intro (v⇑ v) _) All.∷ ν} ¬ν-NS
  with normalStoreP ν
... | yes p = ⊥-elim (¬ν-NS (NS-S' p (λ ())))
... | no ¬p with ¬NormalStore⇒∃cv ¬p
...   | ⟨ _ , ⟨ A∈Σ , cv ⟩ ⟩ = -, ⟨ there A∈Σ , cv ⟩
¬NormalStore⇒∃cv {ν = fromCastedValue v@(intro (cast-val cv c) T) All.∷ _} ¬ν-NS =
  -, ⟨ here refl , ⟨ v , intro (SCV-cast cv c) T ⟩ ⟩
¬NormalStore⇒∃cv {ν = fromCastedValue v@(intro (cast-cval cv p c) T) All.∷ _} ¬ν-NS =
  -, ⟨ here refl , ⟨ v , intro (SCV-ccast cv p c) T ⟩ ⟩
¬NormalStore⇒∃cv {ν = fromCastedValue v@(intro (cv-pair  cv₁ cv₂ p) T) All.∷ _} ¬ν-NS =
  -, ⟨ here refl , ⟨ v , intro (SCV-pair cv₁ cv₂ p) T ⟩ ⟩

ν-update/ref : ∀ {A Σ Γ} {r : Σ ∣ Γ ⊢ Ref A}
  → (R : Value r) → Store Σ → ∀ {e : Σ ∣ ∅ ⊢ A} → Value e → Store Σ
ν-update/ref R ν v
  with inertP (make-coercion _ (ref⟹T R))
... | yes c-Inert = μ-update (ref⟹∈ R) ν (V-cast v c-Inert)
... | no ¬c-Inert = ν-update (ref⟹∈ R) ν (cast-val v (¬Inert⇒Active ¬c-Inert))

private

  {-

    all-⊑ₕ does the second step in the process of casting a store. It strenthens
    the store typing given that all elements are already strenthened.

  -}

  all-⊑ₕ : ∀ {Σ Σ' : StoreTyping}
    → All (λ ty → StoreValue ty Σ') Σ
    → Σ' ⊑ₕ Σ
    → All (λ ty → StoreValue ty Σ') Σ'
  all-⊑ₕ ν prec = pw-map' update-type prec ν
    where

      cast-casted-value : ∀ {A B Σ} {cv : Σ ∣ ∅ ⊢ A}
        → B ⊑ A → CastedValue cv → Σ[ e ∈ Σ ∣ ∅ ⊢ B ] (Value e ⊎ (Σ[ cv' ∈ CastedValue e ] StrongCastedValue cv'))
      cast-casted-value _ (v⇑ v)
        with inertP (make-coercion _ _)
      ... | yes c-Inert = -, (inj₁ (V-cast v c-Inert))
      ... | no c-¬Inert = -, (inj₂ (-, (SCV-cast v (¬Inert⇒Active c-¬Inert))))
      cast-casted-value _ cv@(cast-val _ _) =
        -, (inj₂ (-, (SCV-ccast cv (SCV-cast _ _) (make-coercion _ _))))
      cast-casted-value _ cv@(cast-cval _ _ _) =
        -, (inj₂ (-, (SCV-ccast cv (SCV-ccast _ _ _) (make-coercion _ _))))
      cast-casted-value ⊑-refl (cv-pair _ _ p) = -, (inj₂ (-, (SCV-pair _ _ p)))
      cast-casted-value (⊑-× ext1 ext2) (cv-pair cv₁ cv₂ _)
        with cast-casted-value ext1 cv₁ | cast-casted-value ext2 cv₂
      ... | ⟨ _ , a ⟩ | ⟨ _ , b ⟩
        with a | b
      ...  | inj₂ ⟨ _ , scv₁' ⟩ | inj₁ v =
        -, (inj₂ (-, (SCV-pair _ (v⇑ v) (inj₁ ⟨ scv₁' , v ⟩))))
      ...  | inj₂ ⟨ _ , scv₁' ⟩ | inj₂ ⟨ _ , scv₂' ⟩ =
        -, (inj₂ (-, (SCV-pair _ _ (inj₂ (inj₂ ⟨ scv₁' , scv₂' ⟩)))))
      ...  | inj₁ v₁ | inj₁ v₂ = -, (inj₁ (V-pair v₁ v₂))
      ...  | inj₁ v | inj₂ ⟨ _ , scv₂' ⟩ =
        -, (inj₂ (-, (SCV-pair (v⇑ v) _ (inj₂ (inj₁ ⟨ v , scv₂' ⟩)))))

      update-type : ∀ {A B Σ} → B ⊑ A → StoreValue A Σ → StoreValue B Σ
      update-type _ (fromNormalValue (intro v ty))
        with inertP (make-coercion _ _)
      ... | yes c-Inert = fromNormalValue (intro (V-cast v c-Inert) (Type⇑ _))
      ... | no c-¬Inert =
        fromCastedValue (intro (cast-val v (¬Inert⇒Active c-¬Inert)) (Type⇑ _))

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

{- Re-exported concrete definitions -}

open ParamBase Value Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑
open StoreExtend prefix-weaken-val prefix-weaken-cv public
open Corollary1 typeprecise-strenthen-val typeprecise-strenthen-cv all-⊑ₕ public

open import MonoRef.Dynamics.Store.TypingProgress
  _⟹_ Inert public
