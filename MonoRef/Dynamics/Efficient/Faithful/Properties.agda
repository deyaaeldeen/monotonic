module MonoRef.Dynamics.Efficient.Faithful.Properties where

open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Product using (∃ ; ∃-syntax ; -,_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality using (_≢_ ; refl)
open import Relation.Nullary using (yes ; no ; ¬_)

open import MonoRef.Coercions.NormalForm.Faithful.Compose
open import MonoRef.Coercions.NormalForm.Faithful.Reduction
open import MonoRef.Coercions.NormalForm.Faithful.Syntax
  renaming (NormalFormCoercion to _⟹_ ; InertNormalForm to Inert
           ; ActiveNormalForm to Active ; inert-normalform-decidable to inertP
           ; ¬Inert⇒Active-normform to ¬Inert⇒Active)
open import MonoRef.Coercions.NormalForm.Faithful.Make renaming (make-normal-form-coercion to make-coercion)
open import MonoRef.Dynamics.Efficient.Frames
  _⟹_ Inert
open import MonoRef.Dynamics.Efficient.Faithful.Reduction
open import MonoRef.Dynamics.Efficient.Value
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Efficient
  _⟹_ Inert Active inertP ¬Inert⇒Active make-coercion compose
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


sval∧Inert⇒¬⟶ᵤ : ∀ {Σ A B} {e : Σ ∣ ∅ ⊢ A} {e' : Σ ∣ ∅ ⊢ B} {c : A ⟹ B}
  → SimpleValue e → Inert c → ¬ (e < c > ⟶ᵤ e')
sval∧Inert⇒¬⟶ᵤ _ (I-final ()) (`⊥ _)
sval∧Inert⇒¬⟶ᵤ _ (I-final (I-middle ())) (⊥ₘ _)
sval∧Inert⇒¬⟶ᵤ _ (I-final (I-middle ())) (`× _ _)
sval∧Inert⇒¬⟶ᵤ _ (I-final (I-middle ())) (ι _)
sval∧Inert⇒¬⟶ᵤ () _ compose-casts

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
sval∧Inert⇒¬⟶ᵤᵣ sv c (pure red) = sval∧Inert⇒¬⟶ᵤ sv c red
sval∧Inert⇒¬⟶ᵤᵣ sv c (mono red) = sval∧Inert⇒¬⟶ₘ sv c red
sval∧Inert⇒¬⟶ᵤᵣ sv c (ξ-cast red) = sval⟶ᵤᵣ⊥ sv red
sval∧Inert⇒¬⟶ᵤᵣ () c ξ-cast-error

sval⟶ᵤ⊥ : ∀ {Σ A} {e : Σ ∣ ∅ ⊢ A} {e' : Σ ∣ ∅ ⊢ A} → SimpleValue e → ¬ (e ⟶ᵤ e')
sval⟶ᵤ⊥ (V-ƛ N) ()
sval⟶ᵤ⊥ V-zero ()
sval⟶ᵤ⊥ (V-suc v) ()
sval⟶ᵤ⊥ V-unit ()
sval⟶ᵤ⊥ (V-addr _ _) ()
sval⟶ᵤ⊥ (V-pair _ _) ()

val⟶ᵤ⊥ : ∀ {Σ A} {e : Σ ∣ ∅ ⊢ A} {e' : Σ ∣ ∅ ⊢ A} → Value e → ¬ (e ⟶ᵤ e')
val⟶ᵤ⊥ (S-Val sv) red = sval⟶ᵤ⊥ sv red
val⟶ᵤ⊥ (V-cast _ (I-final ())) (`⊥ _)
val⟶ᵤ⊥ (V-cast _ (I-final (I-middle ()))) (⊥ₘ _)
val⟶ᵤ⊥ (V-cast () _) compose-casts
val⟶ᵤ⊥ (V-cast _ (I-final (I-middle ()))) (ι _)
val⟶ᵤ⊥ (V-cast _ (I-final (I-middle ()))) (`× _ _)

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
sval⟶ᵤᵣ⊥ sv (pure red) = sval⟶ᵤ⊥ sv red
sval⟶ᵤᵣ⊥ sv (mono red) = sval⟶ₘ⊥ sv red
sval⟶ᵤᵣ⊥ (V-pair v _) (ξ-×ₗ red) = val⟶ᵤᵣ⊥ v red
sval⟶ᵤᵣ⊥ (V-pair _ v) (ξ-×ᵣ red) = val⟶ᵤᵣ⊥ v red
sval⟶ᵤᵣ⊥ () (ξ-cast _)
sval⟶ᵤᵣ⊥ (V-pair v _) ξ-×ₗ-error = val-error⇒⊥ v
sval⟶ᵤᵣ⊥ (V-pair _ v) ξ-×ᵣ-error = val-error⇒⊥ v
sval⟶ᵤᵣ⊥ () ξ-cast-error

val⟶ᵤᵣ⊥ (S-Val sv) red = sval⟶ᵤᵣ⊥ sv red
val⟶ᵤᵣ⊥ (V-cast sv c) red = sval∧Inert⇒¬⟶ᵤᵣ sv c red

scv⟶ᵤ⟹cv' : ∀ {Σ A} {e : Σ ∣ ∅ ⊢ A} {cv : CastedValue e} {e' : Σ ∣ ∅ ⊢ A}
  → StrongCastedValue cv
  → e ⟶ᵤ e'
  → CastedValue e' ⊎ Erroneous e'
scv⟶ᵤ⟹cv' scv (ι v) = inj₁ (v⇑ (S-Val v))
scv⟶ᵤ⟹cv' _ (`× {c = c} {d = d} (V-cast {c = c'} v₁ _) (S-Val v₂))
  with inertP d
... | yes d-inert =
  inj₁ (cv-pair (cast-cval v₁ c' c) (v⇑ (V-cast v₂ d-inert))
    (inj₁ ⟨ SCV-ccast v₁ c' c , V-cast v₂ d-inert ⟩))
... | no d-¬inert =
  inj₁ (cv-pair (cast-cval v₁ c' c) (cast-val v₂ (¬Inert⇒Active d-¬inert))
    (inj₂ (inj₂ ⟨ SCV-ccast v₁ c' c , SCV-cast v₂ (¬Inert⇒Active d-¬inert) ⟩)))
scv⟶ᵤ⟹cv' _ (`× {c = c} {d = d} (V-cast {c = c'} v₁ _) (V-cast {c = d'} v₂ _)) =
  inj₁ (cv-pair (cast-cval v₁ c' c) (cast-cval v₂ d' d)
    (inj₂ (inj₂ ⟨ SCV-ccast v₁ c' c , SCV-ccast v₂ d' d ⟩)))
scv⟶ᵤ⟹cv' _ (`× {c = c} {d = d} (S-Val v₁) (S-Val v₂))
  with inertP c | inertP d
... | yes c-inert | yes d-inert =
  inj₁ (v⇑ (S-Val (V-pair (V-cast v₁ c-inert) (V-cast v₂ d-inert))))
... | no c-¬inert | yes d-inert =
 inj₁ (cv-pair (cast-val v₁ (¬Inert⇒Active c-¬inert)) (v⇑ (V-cast v₂ d-inert))
   (inj₁ ⟨ SCV-cast v₁ (¬Inert⇒Active c-¬inert) , V-cast v₂ d-inert ⟩))
... | yes c-inert | no d-¬inert =
 inj₁ (cv-pair (v⇑ (V-cast v₁ c-inert)) (cast-val v₂ (¬Inert⇒Active d-¬inert))
   (inj₂ (inj₁ ⟨ V-cast v₁ c-inert , SCV-cast v₂ (¬Inert⇒Active d-¬inert) ⟩)))
... | no c-¬inert | no d-¬inert =
  inj₁ (cv-pair (cast-val v₁ (¬Inert⇒Active c-¬inert)) (cast-val v₂ (¬Inert⇒Active d-¬inert))
    (inj₂ (inj₂ ⟨ SCV-cast v₁ (¬Inert⇒Active c-¬inert) ,
                  SCV-cast v₂ (¬Inert⇒Active d-¬inert) ⟩)))
scv⟶ᵤ⟹cv' _ (`× {c = c} {d = d} (S-Val v₁) (V-cast {c = d'} v₂ _))
  with inertP c
... | yes c-inert =
  inj₁ (cv-pair (v⇑ V-cast v₁ c-inert) (cast-cval v₂ d' d)
    (inj₂ (inj₁ ⟨ V-cast v₁ c-inert , SCV-ccast v₂ d' d ⟩)))
... | no c-¬inert =
  inj₁ (cv-pair (cast-val v₁ (¬Inert⇒Active c-¬inert)) (cast-cval v₂ d' d)
    (inj₂ (inj₂ ⟨ SCV-cast v₁ (¬Inert⇒Active c-¬inert) , SCV-ccast v₂ d' d ⟩)))
scv⟶ᵤ⟹cv' (SCV-cast () _) compose-casts
scv⟶ᵤ⟹cv' (SCV-ccast v c d) compose-casts
  with inertP (compose c d)
... | yes cd-inert = inj₁ (v⇑ (V-cast v cd-inert))
... | no cd-¬inert = inj₁ (cast-val v (¬Inert⇒Active cd-¬inert))
scv⟶ᵤ⟹cv' _ (`⊥ _) = inj₂ Err-intro
scv⟶ᵤ⟹cv' _ (⊥ₘ _) = inj₂ Err-intro

scv⟶ₘ⟹cv' : ∀ {Σ Σ' A} {e : Σ ∣ ∅ ⊢ A} {cv : CastedValue e} {ν : Store Σ}
  {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → StrongCastedValue cv
  → e , ν ⟶ₘ e' , ν'
  → CastedValue e' ⊎ Erroneous e'
scv⟶ₘ⟹cv' scv (castref1 {T₂⊑A = T₂⊑A} R rtti∼T₂ x) =
  inj₁ (v⇑ (S-Val (V-addr (Σ-cast⟹∈ (ref⟹∈ R) (⊓ rtti∼T₂)) (⊑-trans (⊓⟹⊑ᵣ rtti∼T₂) T₂⊑A))))
scv⟶ₘ⟹cv' _ (castref2 {ν = ν} {T₂⊑A = T₂⊑A} R rtti∼T₂ eq) =
  inj₁ (v⇑ (S-Val (V-addr (ref-ν⟹∈ R ν) (⊑-trans (⊓⟹⊑ᵣ-with-≡ rtti∼T₂ eq) T₂⊑A))))
scv⟶ₘ⟹cv' _ (castref3 _ _) = inj₂ Err-intro

scv⟶ᵤᵣ⟹cv' : ∀ {Σ Σ' A bc} {e : Σ ∣ ∅ ⊢ A} {cv : CastedValue e} {ν : Store Σ}
  {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → StrongCastedValue cv
  → bc / e , ν ⟶ᵤᵣ e' , ν'
  → CastedValue e' ⊎ Erroneous e'
scv⟶ᵤᵣ⟹cv' scv (switch red) = scv⟶ᵤᵣ⟹cv' scv red
scv⟶ᵤᵣ⟹cv' scv (pure red) = scv⟶ᵤ⟹cv' scv red
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
scv⟶ᵤᵣ⟹cv' (SCV-ccast _ _ _) (ξ-cast ())
scv⟶ᵤᵣ⟹cv' _ ξ-×ₗ-error = inj₂ Err-intro
scv⟶ᵤᵣ⟹cv' _ ξ-×ᵣ-error = inj₂ Err-intro
scv⟶ᵤᵣ⟹cv' _ ξ-cast-error = inj₂ Err-intro
