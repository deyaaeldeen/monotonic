module MonoRef.Dynamics.Simple.EvStore.Properties where

open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Nullary using (yes ; no ; ¬_)

open import MonoRef.Dynamics.Simple.Coercions
open import MonoRef.Dynamics.Simple.Frames
open import MonoRef.Dynamics.Simple.EvStore.SReduction
open import MonoRef.Dynamics.Simple.EvStore.Store
open import MonoRef.Dynamics.Simple.TargetWithoutBlame
open import MonoRef.Static.Context
open import MonoRef.Static.Types.Relations


val⟶ᵤ⊥ : ∀ {Σ A} {e : Σ ∣ ∅ ⊢ A} {e' : Σ ∣ ∅ ⊢ A} → Value e → ¬ (e ⟶ᵤ e')
val⟶ᵤ⊥ (V-ƛ _) ()
val⟶ᵤ⊥ V-zero ()
val⟶ᵤ⊥ (V-suc _) ()
val⟶ᵤ⊥ V-unit ()
val⟶ᵤ⊥ (V-addr _ _) ()
val⟶ᵤ⊥ (V-pair _ _) ()
val⟶ᵤ⊥ (V-cast _ ()) (ι _)
val⟶ᵤ⊥ (V-cast _ ()) (!? _)
val⟶ᵤ⊥ (V-cast _ ()) (`× _ _)
val⟶ᵤ⊥ (V-cast _ ()) (`⊥ _ _)

val⟶ₘ⊥ : ∀ {Σ Σ' A} {e : Σ ∣ ∅ ⊢ A} {ν : Store Σ} {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → Value e → ¬ (e , ν ⟶ₘ e' , ν')
val⟶ₘ⊥ (V-cast _ c) (castref1 _ _ _) = Inert⇒¬Ref c
val⟶ₘ⊥ (V-cast _ c) (castref2 _ _ _) = Inert⇒¬Ref c
val⟶ₘ⊥ (V-cast _ c) (castref3 _ _  ) = Inert⇒¬Ref c

val⟶ᶜ⊥ : ∀ {Σ Σ' A} {e : Σ ∣ ∅ ⊢ A} {ν : Store Σ} {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → Value e → ¬ (e , ν ⟶ᶜ e' , ν')
val⟶ᶜ⊥ v (pure red) = val⟶ᵤ⊥ v red
val⟶ᶜ⊥ v (mono red) = val⟶ₘ⊥ v red
val⟶ᶜ⊥ () (cong (ξ-appₗ _) _)
val⟶ᶜ⊥ () (cong (ξ-appᵣ _) _)
val⟶ᶜ⊥ v (cong ξ-suc red)
  with v
... | V-suc v' = val⟶ᶜ⊥ v' red
val⟶ᶜ⊥ () (cong (ξ-caseₚ _ _) _)
val⟶ᶜ⊥ v (cong (ξ-×ₗ _) red)
  with v
... | (V-pair v₁ _) = val⟶ᶜ⊥ v₁ red
val⟶ᶜ⊥ v (cong (ξ-×ᵣ _) red)
  with v
... | (V-pair _ v₂) = val⟶ᶜ⊥ v₂ red
val⟶ᶜ⊥ () (cong ξ-πₗ _)
val⟶ᶜ⊥ () (cong ξ-πᵣ _)
val⟶ᶜ⊥ () (cong (ξ-ref _) _)
val⟶ᶜ⊥ () (cong (ξ-!ₛ _) _)
val⟶ᶜ⊥ () (cong (ξ-! _) _)
val⟶ᶜ⊥ () (cong (ξ-:=ₛₗ _ _) _)
val⟶ᶜ⊥ () (cong (ξ-:=ₛᵣ _ _) _)
val⟶ᶜ⊥ () (cong (ξ-:=ₗ _ _) _)
val⟶ᶜ⊥ () (cong (ξ-:=ᵣ _ _) _)
val⟶ᶜ⊥ v (cong (ξ-<> _) red)
  with v
... | V-cast v' _ = val⟶ᶜ⊥ v' red
val⟶ᶜ⊥ () (cong-error (ξ-appₗ _))
val⟶ᶜ⊥ () (cong-error (ξ-appᵣ _))
val⟶ᶜ⊥ v (cong-error ξ-suc)
  with v
... | V-suc ()
val⟶ᶜ⊥ () (cong-error (ξ-caseₚ _ _))
val⟶ᶜ⊥ v (cong-error (ξ-×ₗ _))
  with v
... | V-pair () _
val⟶ᶜ⊥ v (cong-error (ξ-×ᵣ _))
  with v
... | V-pair _ ()
val⟶ᶜ⊥ () (cong-error ξ-πₗ)
val⟶ᶜ⊥ () (cong-error ξ-πᵣ)
val⟶ᶜ⊥ () (cong-error (ξ-ref _))
val⟶ᶜ⊥ () (cong-error (ξ-!ₛ _))
val⟶ᶜ⊥ () (cong-error (ξ-! _))
val⟶ᶜ⊥ () (cong-error (ξ-:=ₛₗ _ _))
val⟶ᶜ⊥ () (cong-error (ξ-:=ₛᵣ _ _))
val⟶ᶜ⊥ () (cong-error (ξ-:=ₗ _ _))
val⟶ᶜ⊥ () (cong-error (ξ-:=ᵣ _ _))
val⟶ᶜ⊥ v (cong-error (ξ-<> _))
  with v
... | V-cast () _

scv⟶ᶜ⟹cv'/pure : ∀ {Σ A} {e e' : Σ ∣ ∅ ⊢ A}
  → DelayedCast e → e ⟶ᵤ e' → DelayedCast e' ⊎ Erroneous e'
scv⟶ᶜ⟹cv'/pure dc (ι v) = inj₁ (v⇑ v)
scv⟶ᶜ⟹cv'/pure dc (!? v)
  with inertP (make-coercion _ _)
... | yes c-inert = inj₁ (v⇑ (V-cast v c-inert))
... | no c-¬inert = inj₁ (cast-val (v⇑ v) (make-coercion _ _))
scv⟶ᶜ⟹cv'/pure _ (`× {c₁ = c₁} {c₂ = c₂} a b) =
  inj₁ (cv-pair (cast-val (v⇑ a) c₁) (cast-val (v⇑ b) c₂))
scv⟶ᶜ⟹cv'/pure _ (`⊥ _ _) = inj₂ Err-intro

scv⟶ᶜ⟹cv'/mono : ∀ {Σ Σ' A} {e : Σ ∣ ∅ ⊢ A} {ν : Store Σ}
  {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → DelayedCast e → e , ν ⟶ₘ e' , ν' → DelayedCast e' ⊎ Erroneous e'
scv⟶ᶜ⟹cv'/mono dc (castref1 {C⊑B = C⊑B} R rtti∼C x) =
  inj₁ (v⇑ (V-addr (Σ-cast⟹∈ (ref⟹∈ R) (⊓ rtti∼C)) (⊑-trans (⊓⟹⊑ᵣ rtti∼C) C⊑B)))
scv⟶ᶜ⟹cv'/mono dc (castref2 {ν = ν} {C⊑B = C⊑B} R rtti∼C eq) =
  inj₁ (v⇑ (V-addr (ref-ν⟹∈ R ν) (⊑-trans (⊓⟹⊑ᵣ-with-≡ rtti∼C eq) C⊑B)))
scv⟶ᶜ⟹cv'/mono dc (castref3 R x) = inj₂ Err-intro

scv⟶ᶜ⟹cv' : ∀ {Σ Σ' A} {e : Σ ∣ ∅ ⊢ A} {ν : Store Σ}
  {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → DelayedCast e → ¬ Value e → e , ν ⟶ᶜ e' , ν' → DelayedCast e' ⊎ Erroneous e'
scv⟶ᶜ⟹cv' dc _ (pure red) = scv⟶ᶜ⟹cv'/pure dc red
scv⟶ᶜ⟹cv' dc _ (mono red) = scv⟶ᶜ⟹cv'/mono dc red
scv⟶ᶜ⟹cv' (v⇑ ()) ¬v (cong (ξ-appₗ _) _)
scv⟶ᶜ⟹cv' (v⇑ ()) ¬v (cong (ξ-appᵣ _) _)
scv⟶ᶜ⟹cv' (v⇑ v) ¬v (cong ξ-suc red) = ⊥-elim (¬v v)
scv⟶ᶜ⟹cv' (v⇑ ()) ¬v (cong (ξ-caseₚ x x₁) red)
scv⟶ᶜ⟹cv' dc ¬v (cong {A = A} (ξ-×ₗ N) red)
  with typeprecise-strenthen-frame {A = A} (⟶ᶜ⟹⊑ₕ red) (ξ-×ₗ N)
... | _
    with dc
...   | v⇑ v = ⊥-elim (¬v v)
...   | cv-pair {e₁ = e₁} {e₂ = e₂} cv₁ cv₂
      with valueP e₁
...     | yes v₁ = ⊥-elim (val⟶ᶜ⊥ v₁ red)
...     | no ¬v₁
        with scv⟶ᶜ⟹cv' cv₁ ¬v₁ red
...       | inj₁ cv₁' = inj₁ (cv-pair cv₁' (typeprecise-strenthen-cv (⟶ᶜ⟹⊑ₕ red) cv₂))
...       | inj₂ err = inj₂ (Err-plugged err (ξ-×ₗ (typeprecise-strenthen-expr (⟶ᶜ⟹⊑ₕ red) N)))
scv⟶ᶜ⟹cv' dc ¬v (cong {A = A} (ξ-×ᵣ N) red)
  with typeprecise-strenthen-frame {A = A} (⟶ᶜ⟹⊑ₕ red) (ξ-×ᵣ N)
... | _
    with dc
...   | v⇑ v = ⊥-elim (¬v v)
...   | cv-pair {e₁ = e₁} {e₂ = e₂} cv₁ cv₂
      with valueP e₂
...     | yes v₂ = ⊥-elim (val⟶ᶜ⊥ v₂ red)
...     | no ¬v₂
        with scv⟶ᶜ⟹cv' cv₂ ¬v₂ red
...       | inj₁ cv₂' = inj₁ (cv-pair (typeprecise-strenthen-cv (⟶ᶜ⟹⊑ₕ red) cv₁) cv₂')
...       | inj₂ err = inj₂ (Err-plugged err (ξ-×ᵣ (typeprecise-strenthen-expr (⟶ᶜ⟹⊑ₕ red) N)))
scv⟶ᶜ⟹cv' (v⇑ ()) _ (cong ξ-πₗ _)
scv⟶ᶜ⟹cv' (v⇑ ()) _ (cong ξ-πᵣ _)
scv⟶ᶜ⟹cv' (v⇑ ()) _ (cong (ξ-ref _) _)
scv⟶ᶜ⟹cv' (v⇑ ()) _ (cong (ξ-!ₛ _) _)
scv⟶ᶜ⟹cv' (v⇑ ()) _ (cong (ξ-! _) _)
scv⟶ᶜ⟹cv' (v⇑ ()) _ (cong (ξ-:=ₛₗ _ _) _)
scv⟶ᶜ⟹cv' (v⇑ ()) _ (cong (ξ-:=ₛᵣ _ _) _)
scv⟶ᶜ⟹cv' (v⇑ ()) _ (cong (ξ-:=ₗ _ _) _)
scv⟶ᶜ⟹cv' (v⇑ ()) _ (cong (ξ-:=ᵣ _ _) _)
scv⟶ᶜ⟹cv' dc ¬v (cong (ξ-<> x) red)
  with dc
... | v⇑ v = ⊥-elim (¬v v)
... | cast-val {e = e} cv c
    with valueP e
...   | yes v = ⊥-elim (val⟶ᶜ⊥ v red)
...   | no ¬v'
      with scv⟶ᶜ⟹cv' cv ¬v' red
...     | inj₁ cv' = inj₁ (cast-val cv' c)
...     | inj₂ err = inj₂ (Err-plugged err (ξ-<> c))
scv⟶ᶜ⟹cv' _ _ (cong-error _) = inj₂ Err-intro
