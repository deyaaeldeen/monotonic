module MonoRef.Dynamics.Efficient.Forgetful.Properties where

open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Product using (∃ ; ∃-syntax ; -,_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality using (_≢_ ; refl)
open import Relation.Nullary using (yes ; no ; ¬_)

open import MonoRef.Coercions.NormalForm.Forgetful.CastedValueReduction
open import MonoRef.Coercions.NormalForm.Forgetful.Compose
open import MonoRef.Coercions.NormalForm.Forgetful.Reduction
open import MonoRef.Coercions.NormalForm.Forgetful.Syntax
  renaming (NormalFormCoercion to _⟹_ ; InertNormalForm to Inert
           ; ActiveNormalForm to Active ; inert-normalform-decidable to inertP
           ; ¬Inert⇒Active-normform to ¬Inert⇒Active)
open import MonoRef.Coercions.NormalForm.Forgetful.Make renaming (make-normal-form-coercion to make-coercion)
open import MonoRef.Dynamics.Efficient.Frames
  _⟹_ Inert
open import MonoRef.Dynamics.Efficient.Forgetful.Reduction
  _⟹_ Inert Active make-coercion
open import MonoRef.Dynamics.Efficient.Value
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Efficient
  _⟹_ Inert Active inertP ¬Inert⇒Active make-coercion compose
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


open ParamReduction SimpleValue Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑
open ParamReduction/ν-cast/ν-update/ref/store/⟶ᵤ/⟶ᵤᶜᵛ ν-cast ν-update/ref store _⟶ᵤ_ _⟶ᵤᶜᵛ_


sval∧Inert⇒¬⟶ᵤᶜᵛ : ∀ {Σ A B} {e : Σ ∣ ∅ ⊢ A} {e' : Σ ∣ ∅ ⊢ B} {c : A ⟹ B}
  → SimpleValue e → Inert c → ¬ (e < c > ⟶ᵤᶜᵛ e')
sval∧Inert⇒¬⟶ᵤᶜᵛ _ (I-final ()) (`⊥ _)
sval∧Inert⇒¬⟶ᵤᶜᵛ _ (I-final (I-middle ())) (pair-simple _ _)
sval∧Inert⇒¬⟶ᵤᶜᵛ _ (I-final (I-middle ())) (pair-cast-left _ _)
sval∧Inert⇒¬⟶ᵤᶜᵛ _ (I-final (I-middle ())) (pair-cast-right _ _)
sval∧Inert⇒¬⟶ᵤᶜᵛ _ (I-final (I-middle ())) (pair-cast-both _ _)
sval∧Inert⇒¬⟶ᵤᶜᵛ _ (I-final (I-middle ())) (ι _)

sval∧Inert⇒¬⟶ₘ : ∀ {Σ Σ' A B} {e : Σ ∣ ∅ ⊢ A} {ν : Store Σ} {e' : Σ' ∣ ∅ ⊢ B} {ν' : Store Σ'} {c : A ⟹ B}
  → SimpleValue e → Inert c → ¬ (e < c > , ν ⟶ₘ e' , ν')
sval∧Inert⇒¬⟶ₘ _ (I-final (I-middle ())) (castref1 _ _ _)
sval∧Inert⇒¬⟶ₘ _ (I-final (I-middle ())) (castref2 _ _ _)
sval∧Inert⇒¬⟶ₘ _ (I-final (I-middle ())) (castref3 _ _)

sval⟶ᵤᵣ⊥ : ∀ {Σ Σ' A bc} {e : Σ ∣ ∅ ⊢ A} {ν : Store Σ} {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → SimpleValue e → ¬ (bc / e , ν ⟶ᵤᵣ e' , ν')

sval∧Inert⇒¬⟶ᵤᵣ : ∀ {Σ Σ' A B bc} {e : Σ ∣ ∅ ⊢ A} {ν : Store Σ} {e' : Σ' ∣ ∅ ⊢ B} {ν' : Store Σ'} {c : A ⟹ B}
  → SimpleValue e → Inert c → ¬ (bc / e < c > , ν ⟶ᵤᵣ e' , ν')
sval∧Inert⇒¬⟶ᵤᵣ sv c (switch red) = sval∧Inert⇒¬⟶ᵤᵣ sv c red
sval∧Inert⇒¬⟶ᵤᵣ sv c (pure red) = sval∧Inert⇒¬⟶ᵤᶜᵛ sv c red
sval∧Inert⇒¬⟶ᵤᵣ sv c (mono red) = sval∧Inert⇒¬⟶ₘ sv c red
sval∧Inert⇒¬⟶ᵤᵣ sv c (ξ-cast red) = sval⟶ᵤᵣ⊥ sv red
sval∧Inert⇒¬⟶ᵤᵣ () c ξ-cast-error

sval⟶ᵤᶜᵛ⊥ : ∀ {Σ A} {e : Σ ∣ ∅ ⊢ A} {e' : Σ ∣ ∅ ⊢ A} → SimpleValue e → ¬ (e ⟶ᵤᶜᵛ e')
sval⟶ᵤᶜᵛ⊥ (V-ƛ N) ()
sval⟶ᵤᶜᵛ⊥ V-zero ()
sval⟶ᵤᶜᵛ⊥ (V-suc v) ()
sval⟶ᵤᶜᵛ⊥ V-unit ()
sval⟶ᵤᶜᵛ⊥ (V-addr _ _) ()
sval⟶ᵤᶜᵛ⊥ (V-pair _ _) ()

val⟶ᵤᶜᵛ⊥ : ∀ {Σ A} {e : Σ ∣ ∅ ⊢ A} {e' : Σ ∣ ∅ ⊢ A} → Value e → ¬ (e ⟶ᵤᶜᵛ e')
val⟶ᵤᶜᵛ⊥ (S-Val sv) red = sval⟶ᵤᶜᵛ⊥ sv red
val⟶ᵤᶜᵛ⊥ (V-cast _ (I-final ())) (`⊥ _)
val⟶ᵤᶜᵛ⊥ (V-cast _ (I-final (I-middle ()))) (ι _)
val⟶ᵤᶜᵛ⊥ (V-cast _ (I-final (I-middle ()))) (pair-simple _ _)
val⟶ᵤᶜᵛ⊥ (V-cast _ (I-final (I-middle ()))) (pair-cast-left _ _)
val⟶ᵤᶜᵛ⊥ (V-cast _ (I-final (I-middle ()))) (pair-cast-right _ _)
val⟶ᵤᶜᵛ⊥ (V-cast _ (I-final (I-middle ()))) (pair-cast-both _ _)

sval⟶ₘ⊥ : ∀ {Σ Σ' A} {e : Σ ∣ ∅ ⊢ A} {ν : Store Σ} {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → SimpleValue e → ¬ (e , ν ⟶ₘ e' , ν')
sval⟶ₘ⊥ () (castref1 _ _ _)
sval⟶ₘ⊥ () (castref2 _ _ _)
sval⟶ₘ⊥ () (castref3 _ _)

val⟶ₘ⊥ : ∀ {Σ Σ' A} {e : Σ ∣ ∅ ⊢ A} {ν : Store Σ} {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → Value e → ¬ (e , ν ⟶ₘ e' , ν')
val⟶ₘ⊥ (S-Val sv) red = sval⟶ₘ⊥ sv red
val⟶ₘ⊥ (V-cast _ c) (castref1 _ _ _) = Inert⇒¬Ref c
val⟶ₘ⊥ (V-cast _ c) (castref2 _ _ _) = Inert⇒¬Ref c
val⟶ₘ⊥ (V-cast _ c) (castref3 _ _) = Inert⇒¬Ref c

val-error⇒⊥ : ∀ {Γ Σ A} → ¬ Value (error {Σ}{Γ}{A})
val-error⇒⊥ (S-Val ())

val⟶ᵤᵣ⊥ : ∀ {Σ Σ' A bc} {e : Σ ∣ ∅ ⊢ A} {ν : Store Σ} {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → Value e → ¬ (bc / e , ν ⟶ᵤᵣ e' , ν')

sval⟶ᵤᵣ⊥ sv (switch red) = sval⟶ᵤᵣ⊥ sv red
sval⟶ᵤᵣ⊥ sv (pure red) = sval⟶ᵤᶜᵛ⊥ sv red
sval⟶ᵤᵣ⊥ sv (mono red) = sval⟶ₘ⊥ sv red
sval⟶ᵤᵣ⊥ (V-pair v _) (ξ-×ₗ red) = val⟶ᵤᵣ⊥ v red
sval⟶ᵤᵣ⊥ (V-pair _ v) (ξ-×ᵣ red) = val⟶ᵤᵣ⊥ v red
sval⟶ᵤᵣ⊥ () (ξ-cast _)
sval⟶ᵤᵣ⊥ (V-pair v _) ξ-×ₗ-error = val-error⇒⊥ v
sval⟶ᵤᵣ⊥ (V-pair _ v) ξ-×ᵣ-error = val-error⇒⊥ v
sval⟶ᵤᵣ⊥ () ξ-cast-error

val⟶ᵤᵣ⊥ (S-Val sv) red = sval⟶ᵤᵣ⊥ sv red
val⟶ᵤᵣ⊥ (V-cast sv c) red = sval∧Inert⇒¬⟶ᵤᵣ sv c red

scv⟶ᵤᶜᵛ⟹cv' : ∀ {Σ A} {e : Σ ∣ ∅ ⊢ A} {cv : CastedValue e} {e' : Σ ∣ ∅ ⊢ A}
  → StrongCastedValue cv
  → e ⟶ᵤᶜᵛ e'
  → CastedValue e' ⊎ Erroneous e'
scv⟶ᵤᶜᵛ⟹cv' scv (ι v) = inj₁ (v⇑ (S-Val v))
scv⟶ᵤᶜᵛ⟹cv' _ (pair-simple {c = c}{d} sv₁ sv₂)
  with inertP c | inertP d
... | yes c-inert | yes d-inert =
  inj₁ (v⇑ (S-Val (V-pair (V-cast sv₁ c-inert) (V-cast sv₂ d-inert))))
... | yes c-inert | no d-¬inert =
  inj₁ (cv-pair (v⇑ (V-cast sv₁ c-inert)) (cast-val sv₂ (¬Inert⇒Active d-¬inert))
    (inj₂ (inj₁ ⟨ V-cast sv₁ c-inert , SCV-cast sv₂ (¬Inert⇒Active d-¬inert) ⟩)))
... | no c-¬inert | yes d-inert =
  inj₁ (cv-pair (cast-val sv₁ (¬Inert⇒Active c-¬inert)) (v⇑ (V-cast sv₂ d-inert))
    (inj₁ ⟨ SCV-cast sv₁ (¬Inert⇒Active c-¬inert) , V-cast sv₂ d-inert ⟩))
... | no c-¬inert | no d-¬inert =
  inj₁ (cv-pair (cast-val sv₁ (¬Inert⇒Active c-¬inert)) (cast-val sv₂ (¬Inert⇒Active d-¬inert))
    (inj₂ (inj₂ ⟨ SCV-cast sv₁ (¬Inert⇒Active c-¬inert) , SCV-cast sv₂ (¬Inert⇒Active d-¬inert) ⟩)))
scv⟶ᵤᶜᵛ⟹cv' _ (pair-cast-left {c' = c'}{c}{d} sv₁ sv₂)
  with inertP (compose c' c) | inertP d
... | yes c-inert | yes d-inert =
  inj₁ (v⇑ (S-Val (V-pair (V-cast sv₁ c-inert) (V-cast sv₂ d-inert))))
... | yes c-inert | no d-¬inert =
  inj₁ (cv-pair (v⇑ (V-cast sv₁ c-inert)) (cast-val sv₂ (¬Inert⇒Active d-¬inert))
    (inj₂ (inj₁ ⟨ V-cast sv₁ c-inert , SCV-cast sv₂ (¬Inert⇒Active d-¬inert) ⟩)))
... | no c-¬inert | yes d-inert =
  inj₁ (cv-pair (cast-val sv₁ (¬Inert⇒Active c-¬inert)) (v⇑ (V-cast sv₂ d-inert))
    (inj₁ ⟨ SCV-cast sv₁ (¬Inert⇒Active c-¬inert) , V-cast sv₂ d-inert ⟩))
... | no c-¬inert | no d-¬inert =
  inj₁ (cv-pair (cast-val sv₁ (¬Inert⇒Active c-¬inert)) (cast-val sv₂ (¬Inert⇒Active d-¬inert))
    (inj₂ (inj₂ ⟨ SCV-cast sv₁ (¬Inert⇒Active c-¬inert) , SCV-cast sv₂ (¬Inert⇒Active d-¬inert) ⟩)))
scv⟶ᵤᶜᵛ⟹cv' _ (pair-cast-right {d' = d'}{c}{d} sv₁ sv₂)
  with inertP c | inertP (compose d' d)
... | yes c-inert | yes d-inert =
  inj₁ (v⇑ (S-Val (V-pair (V-cast sv₁ c-inert) (V-cast sv₂ d-inert))))
... | yes c-inert | no d-¬inert =
  inj₁ (cv-pair (v⇑ (V-cast sv₁ c-inert)) (cast-val sv₂ (¬Inert⇒Active d-¬inert))
    (inj₂ (inj₁ ⟨ V-cast sv₁ c-inert , SCV-cast sv₂ (¬Inert⇒Active d-¬inert) ⟩)))
... | no c-¬inert | yes d-inert =
  inj₁ (cv-pair (cast-val sv₁ (¬Inert⇒Active c-¬inert)) (v⇑ (V-cast sv₂ d-inert))
    (inj₁ ⟨ SCV-cast sv₁ (¬Inert⇒Active c-¬inert) , V-cast sv₂ d-inert ⟩))
... | no c-¬inert | no d-¬inert =
  inj₁ (cv-pair (cast-val sv₁ (¬Inert⇒Active c-¬inert)) (cast-val sv₂ (¬Inert⇒Active d-¬inert))
    (inj₂ (inj₂ ⟨ SCV-cast sv₁ (¬Inert⇒Active c-¬inert) , SCV-cast sv₂ (¬Inert⇒Active d-¬inert) ⟩)))
scv⟶ᵤᶜᵛ⟹cv' _ (pair-cast-both {c' = c'}{d'}{c}{d} sv₁ sv₂)
  with inertP (compose c' c) | inertP (compose d' d)
... | yes c-inert | yes d-inert =
  inj₁ (v⇑ (S-Val (V-pair (V-cast sv₁ c-inert) (V-cast sv₂ d-inert))))
... | yes c-inert | no d-¬inert =
  inj₁ (cv-pair (v⇑ (V-cast sv₁ c-inert)) (cast-val sv₂ (¬Inert⇒Active d-¬inert))
    (inj₂ (inj₁ ⟨ V-cast sv₁ c-inert , SCV-cast sv₂ (¬Inert⇒Active d-¬inert) ⟩)))
... | no c-¬inert | yes d-inert =
  inj₁ (cv-pair (cast-val sv₁ (¬Inert⇒Active c-¬inert)) (v⇑ (V-cast sv₂ d-inert))
    (inj₁ ⟨ SCV-cast sv₁ (¬Inert⇒Active c-¬inert) , V-cast sv₂ d-inert ⟩))
... | no c-¬inert | no d-¬inert =
  inj₁ (cv-pair (cast-val sv₁ (¬Inert⇒Active c-¬inert)) (cast-val sv₂ (¬Inert⇒Active d-¬inert))
    (inj₂ (inj₂ ⟨ SCV-cast sv₁ (¬Inert⇒Active c-¬inert) , SCV-cast sv₂ (¬Inert⇒Active d-¬inert) ⟩)))
scv⟶ᵤᶜᵛ⟹cv' _ (`⊥ x₁) = inj₂ Err-intro

scv⟶ₘ⟹cv' : ∀ {Σ Σ' A} {e : Σ ∣ ∅ ⊢ A} {cv : CastedValue e} {ν : Store Σ}
  {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → StrongCastedValue cv
  → e , ν ⟶ₘ e' , ν'
  → CastedValue e' ⊎ Erroneous e'
scv⟶ₘ⟹cv' scv (castref1 R rtti∼T₂ x) =
  inj₁ (v⇑ (S-Val (V-addr (Σ-cast⟹∈ (ref⟹∈ R) (⊓ rtti∼T₂)) (⊓⟹⊑ᵣ rtti∼T₂))))
scv⟶ₘ⟹cv' _ (castref2 {ν = ν} R rtti∼T₂ eq) =
  inj₁ (v⇑ (S-Val (V-addr (ref-ν⟹∈ R ν) (⊓⟹⊑ᵣ-with-≡ rtti∼T₂ eq))))
scv⟶ₘ⟹cv' _ (castref3 _ _) = inj₂ Err-intro

scv⟶ᵤᵣ⟹cv' : ∀ {Σ Σ' A bc} {e : Σ ∣ ∅ ⊢ A} {cv : CastedValue e} {ν : Store Σ}
  {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → StrongCastedValue cv
  → bc / e , ν ⟶ᵤᵣ e' , ν'
  → CastedValue e' ⊎ Erroneous e'
scv⟶ᵤᵣ⟹cv' scv (switch red) = scv⟶ᵤᵣ⟹cv' scv red
scv⟶ᵤᵣ⟹cv' scv (pure red) = scv⟶ᵤᶜᵛ⟹cv' scv red
scv⟶ᵤᵣ⟹cv' scv (mono red) = scv⟶ₘ⟹cv' scv red
scv⟶ᵤᵣ⟹cv' (SCV-pair _ _ p) (ξ-×ₗ red)
  -- we case-analysis on the shape of the pair and process each case accordingly
  with p
... | inj₁ ⟨ scv₁ , v₂ ⟩
   with scv⟶ᵤᵣ⟹cv' scv₁ red
...    | inj₁ cv₁'

  -- we check if the result is a strong casted value, so we can build the shape
  -- of the result pair accordingly.

     with scv-decidable cv₁'
...      | yes scv₁' = inj₁ (cv-pair cv₁' (v⇑ v₂') (inj₁ ⟨ scv₁' , v₂' ⟩))
     where v₂' = typeprecise-strenthen-val (⟶ᵤᵣ⟹⊑ₕ red) v₂
...      | no ¬scv =
  inj₁ (v⇑ (S-Val (V-pair (¬scv⇒Value ¬scv) (typeprecise-strenthen-val (⟶ᵤᵣ⟹⊑ₕ red) v₂))))
scv⟶ᵤᵣ⟹cv' (SCV-pair _ _ _) (ξ-×ₗ {e₂ = e₂} red) | inj₁ ⟨ _ , _ ⟩ | inj₂ err =
  inj₂ (Err-plugged err (ξ-×ₗ (typeprecise-strenthen-expr (⟶ᵤᵣ⟹⊑ₕ red) e₂)))
scv⟶ᵤᵣ⟹cv' (SCV-pair _ _ _) (ξ-×ₗ red) | inj₂ (inj₁ ⟨ v₁ , _ ⟩) =
  ⊥-elim (val⟶ᵤᵣ⊥ v₁ red)
scv⟶ᵤᵣ⟹cv' (SCV-pair cv₁ cv₂ p) (ξ-×ₗ red) | inj₂ (inj₂ ⟨ scv₁ , scv₂ ⟩)
  with scv⟶ᵤᵣ⟹cv' scv₁ red
...    | inj₁ cv₁'
  with scv-decidable cv₁'
...      | yes scv₁' =
  inj₁ (cv-pair cv₁'
                cv₂'
                (inj₂ (inj₂ ⟨ scv₁'
                            , typeprecise-strenthen-scv (⟶ᵤᵣ⟹⊑ₕ red) scv₂ ⟩)))
  where cv₂' = typeprecise-strenthen-cv (⟶ᵤᵣ⟹⊑ₕ red) cv₂
...      | no ¬scv =
  inj₁ (cv-pair (v⇑ v₁')
       cv₂'
       (inj₂ (inj₁ ⟨ v₁'
                   , typeprecise-strenthen-scv (⟶ᵤᵣ⟹⊑ₕ red) scv₂ ⟩)))
  where cv₂' = typeprecise-strenthen-cv (⟶ᵤᵣ⟹⊑ₕ red) cv₂
        v₁'  = ¬scv⇒Value ¬scv
scv⟶ᵤᵣ⟹cv' (SCV-pair _ _ _) (ξ-×ₗ {e₂ = e₂} red) | inj₂ (inj₂ ⟨ _ , _ ⟩) | inj₂ err =
  inj₂ (Err-plugged err (ξ-×ₗ (typeprecise-strenthen-expr (⟶ᵤᵣ⟹⊑ₕ red) e₂)))
scv⟶ᵤᵣ⟹cv' (SCV-pair _ _ p) (ξ-×ᵣ red)
  with p
... | inj₁ ⟨ _ , v₂ ⟩ = ⊥-elim (val⟶ᵤᵣ⊥ v₂ red)
... | inj₂ (inj₁ ⟨ v₁ , scv₂ ⟩)
     with scv⟶ᵤᵣ⟹cv' scv₂ red
... | inj₁ cv₂'
      with scv-decidable cv₂'
...  | yes scv₂' = inj₁ (cv-pair (v⇑ v₁') cv₂' (inj₂ (inj₁ ⟨ v₁' , scv₂' ⟩)))
      where v₁' = typeprecise-strenthen-val (⟶ᵤᵣ⟹⊑ₕ red) v₁
...  | no ¬scv₂' =
  inj₁ (v⇑ (S-Val (V-pair (typeprecise-strenthen-val (⟶ᵤᵣ⟹⊑ₕ red) v₁)
                   (¬scv⇒Value ¬scv₂'))))
scv⟶ᵤᵣ⟹cv' (SCV-pair _ _ _) (ξ-×ᵣ {e₁ = e₁} red) | inj₂ (inj₁ _) | inj₂ err =
  inj₂ (Err-plugged err (ξ-×ᵣ (typeprecise-strenthen-expr (⟶ᵤᵣ⟹⊑ₕ red) e₁)))
scv⟶ᵤᵣ⟹cv' (SCV-pair cv₁ _ _) (ξ-×ᵣ red) | inj₂ (inj₂ ⟨ scv₁ , scv₂ ⟩)
  with scv⟶ᵤᵣ⟹cv' scv₂ red
... | inj₁ cv₂'
      with scv-decidable cv₂'
...  | yes scv₂' =
  inj₁ (cv-pair (typeprecise-strenthen-cv (⟶ᵤᵣ⟹⊑ₕ red) cv₁)
                cv₂'
                (inj₂ (inj₂ ⟨ typeprecise-strenthen-scv (⟶ᵤᵣ⟹⊑ₕ red) scv₁
                            , scv₂' ⟩)))
...  | no ¬scv₂' =
  inj₁ (cv-pair (typeprecise-strenthen-cv (⟶ᵤᵣ⟹⊑ₕ red) cv₁)
                cv₂'
                (inj₁ ⟨ (typeprecise-strenthen-scv (⟶ᵤᵣ⟹⊑ₕ red) scv₁)
                      , (¬scv⇒Value ¬scv₂') ⟩))
scv⟶ᵤᵣ⟹cv' (SCV-pair _ _ _) (ξ-×ᵣ {e₁ = e₁} red) | inj₂ (inj₂ _) | inj₂ err =
  inj₂ (Err-plugged err (ξ-×ᵣ (typeprecise-strenthen-expr (⟶ᵤᵣ⟹⊑ₕ red) e₁)))
scv⟶ᵤᵣ⟹cv' (SCV-cast v _) (ξ-cast red) = ⊥-elim (sval⟶ᵤᵣ⊥ v red)
scv⟶ᵤᵣ⟹cv' _ ξ-×ₗ-error = inj₂ Err-intro
scv⟶ᵤᵣ⟹cv' _ ξ-×ᵣ-error = inj₂ Err-intro
scv⟶ᵤᵣ⟹cv' _ ξ-cast-error = inj₂ Err-intro
