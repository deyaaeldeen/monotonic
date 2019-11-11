module MonoRef.Dynamics.Efficient.EvStore.Properties where

open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Nullary using (yes ; no ; ¬_)

open import MonoRef.Dynamics.Efficient.Coercions
open import MonoRef.Dynamics.Efficient.EvStore.Reduction
open import MonoRef.Dynamics.Efficient.EvStore.Store
open import MonoRef.Dynamics.Efficient.Frames
open import MonoRef.Dynamics.Efficient.TargetWithoutBlame
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


sval∧Inert⇒¬⟶ᵤᶜᵛ : ∀ {Σ A B} {e : Σ ∣ ∅ ⊢ A} {e' : Σ ∣ ∅ ⊢ B} {c : A ⟹ B}
  → SimpleValue e → Inert c → ¬ (e < c > ⟶ᵤᶜᵛ e')
sval∧Inert⇒¬⟶ᵤᶜᵛ _ (I-final (I-middle ())) (`⊥ _)
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

sval⟶ᶜ⊥ : ∀ {Σ Σ' A} {e : Σ ∣ ∅ ⊢ A} {ν : Store Σ} {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → SimpleValue e → ¬ (e , ν ⟶ᶜ e' , ν')

sval∧Inert⇒¬⟶ᶜ : ∀ {Σ Σ' A B} {e : Σ ∣ ∅ ⊢ A} {ν : Store Σ} {e' : Σ' ∣ ∅ ⊢ B} {ν' : Store Σ'} {c : A ⟹ B}
  → SimpleValue e → Inert c → ¬ (e < c > , ν ⟶ᶜ e' , ν')
sval∧Inert⇒¬⟶ᶜ sv c (pure red) = sval∧Inert⇒¬⟶ᵤᶜᵛ sv c red
sval∧Inert⇒¬⟶ᶜ sv c (mono red) = sval∧Inert⇒¬⟶ₘ sv c red

sval⟶ᵤᶜᵛ⊥ : ∀ {Σ A} {e : Σ ∣ ∅ ⊢ A} {e' : Σ ∣ ∅ ⊢ A} → SimpleValue e → ¬ (e ⟶ᵤᶜᵛ e')
sval⟶ᵤᶜᵛ⊥ (V-ƛ N) ()
sval⟶ᵤᶜᵛ⊥ V-zero ()
sval⟶ᵤᶜᵛ⊥ (V-suc v) ()
sval⟶ᵤᶜᵛ⊥ V-unit ()
sval⟶ᵤᶜᵛ⊥ (V-addr _ _) ()
sval⟶ᵤᶜᵛ⊥ (V-pair _ _) ()

val⟶ᵤᶜᵛ⊥ : ∀ {Σ A} {e : Σ ∣ ∅ ⊢ A} {e' : Σ ∣ ∅ ⊢ A} → Value e → ¬ (e ⟶ᵤᶜᵛ e')
val⟶ᵤᶜᵛ⊥ (S-Val sv) red = sval⟶ᵤᶜᵛ⊥ sv red
val⟶ᵤᶜᵛ⊥ (V-cast _ (I-final (I-middle ()))) (`⊥ _)
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

val⟶ᶜ⊥ : ∀ {Σ Σ' A} {e : Σ ∣ ∅ ⊢ A} {ν : Store Σ} {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → Value e → ¬ (e , ν ⟶ᶜ e' , ν')

sval⟶ᶜ⊥ sv (pure red) = sval⟶ᵤᶜᵛ⊥ sv red
sval⟶ᶜ⊥ sv (mono red) = sval⟶ₘ⊥ sv red
sval⟶ᶜ⊥ (V-pair v _) (ξ-×ₗ red) = val⟶ᶜ⊥ v red
sval⟶ᶜ⊥ (V-pair _ v) (ξ-×ᵣ red) = val⟶ᶜ⊥ v red

val⟶ᶜ⊥ (S-Val sv) red = sval⟶ᶜ⊥ sv red
val⟶ᶜ⊥ (V-cast sv c) red = sval∧Inert⇒¬⟶ᶜ sv c red

scv⟶ᵤᶜᵛ⟹cv' : ∀ {Σ A} {e : Σ ∣ ∅ ⊢ A} {e' : Σ ∣ ∅ ⊢ A}
  → DelayedCast e → e ⟶ᵤᶜᵛ e' → DelayedCast e' ⊎ Erroneous e'
scv⟶ᵤᶜᵛ⟹cv' scv (ι v) = inj₁ (v⇑ (S-Val v))
scv⟶ᵤᶜᵛ⟹cv' _ (pair-simple {c = c}{d} sv₁ sv₂) =
  inj₁ (cv-pair (cast-val sv₁ c) (cast-val sv₂ d))
scv⟶ᵤᶜᵛ⟹cv' _ (pair-cast-left {c' = c'}{c}{d} sv₁ sv₂) =
  inj₁ (cv-pair (cast-val sv₁ (compose c' c)) (cast-val sv₂ d))
scv⟶ᵤᶜᵛ⟹cv' _ (pair-cast-right {d' = d'}{c}{d} sv₁ sv₂) =
  inj₁ (cv-pair (cast-val sv₁ c) (cast-val sv₂ (compose d' d)))
scv⟶ᵤᶜᵛ⟹cv' _ (pair-cast-both {c' = c'}{d'}{c}{d} sv₁ sv₂) =
  inj₁ (cv-pair (cast-val sv₁ (compose c' c)) (cast-val sv₂ (compose d' d)))
scv⟶ᵤᶜᵛ⟹cv' _ (`⊥ x₁) = inj₂ Err-intro

scv⟶ₘ⟹cv' : ∀ {Σ Σ' A} {e : Σ ∣ ∅ ⊢ A} {ν : Store Σ}
  {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → DelayedCast e → e , ν ⟶ₘ e' , ν' → DelayedCast e' ⊎ Erroneous e'
scv⟶ₘ⟹cv' scv (castref1 {C⊑B = C⊑B} R rtti∼C x) =
  inj₁ (v⇑ (S-Val (V-addr (Σ-cast⟹∈ (ref⟹∈ R) (⊓ rtti∼C)) (⊑-trans (⊓⟹⊑ᵣ rtti∼C) C⊑B))))
scv⟶ₘ⟹cv' _ (castref2 {ν = ν} {C⊑B = C⊑B} R rtti∼C eq) =
  inj₁ (v⇑ (S-Val (V-addr (ref-ν⟹∈ R ν) (⊑-trans (⊓⟹⊑ᵣ-with-≡ rtti∼C eq) C⊑B))))
scv⟶ₘ⟹cv' _ (castref3 _ _) = inj₂ Err-intro

scv⟶ᶜ⟹cv' : ∀ {Σ Σ' A} {e : Σ ∣ ∅ ⊢ A} {ν : Store Σ}
  {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → DelayedCast e → ¬ Value e → e , ν ⟶ᶜ e' , ν' → DelayedCast e' ⊎ Erroneous e'
scv⟶ᶜ⟹cv' scv _ (pure red) = scv⟶ᵤᶜᵛ⟹cv' scv red
scv⟶ᶜ⟹cv' scv _ (mono red) = scv⟶ₘ⟹cv' scv red
scv⟶ᶜ⟹cv' (v⇑ x) ¬v (ξ-×ₗ red) = ⊥-elim (¬v x)
scv⟶ᶜ⟹cv' (cv-pair {e₁ = e₁} {e₂ = e₂} cv₁ cv₂) ¬v (ξ-×ₗ red)
      with valueP e₁
...     | yes v₁ = ⊥-elim (val⟶ᶜ⊥ v₁ red)
...     | no ¬v₁
        with scv⟶ᶜ⟹cv' cv₁ ¬v₁ red
...       | inj₁ cv₁' = inj₁ (cv-pair cv₁' (typeprecise-strenthen-cv (⟶ᶜ⟹⊑ₕ red) cv₂))
...       | inj₂ err = inj₂ (Err-plugged err (ξ-×ₗ (typeprecise-strenthen-expr (⟶ᶜ⟹⊑ₕ red) e₂)))
scv⟶ᶜ⟹cv' (v⇑ x) ¬v (ξ-×ᵣ red) = ⊥-elim (¬v x)
scv⟶ᶜ⟹cv' (cv-pair {e₁ = e₁} {e₂ = e₂} cv₁ cv₂) ¬v (ξ-×ᵣ red)
      with valueP e₂
...     | yes v₂ = ⊥-elim (val⟶ᶜ⊥ v₂ red)
...     | no ¬v₂
        with scv⟶ᶜ⟹cv' cv₂ ¬v₂ red
...       | inj₁ cv₂' = inj₁ (cv-pair (typeprecise-strenthen-cv (⟶ᶜ⟹⊑ₕ red) cv₁) cv₂')
...       | inj₂ err = inj₂ (Err-plugged err (ξ-×ᵣ (typeprecise-strenthen-expr (⟶ᶜ⟹⊑ₕ red) e₁)))
