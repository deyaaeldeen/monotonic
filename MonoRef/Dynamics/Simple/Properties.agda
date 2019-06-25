module MonoRef.Dynamics.Simple.Properties where

open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Product using (∃ ; ∃-syntax ; -,_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality using (_≢_ ; refl)
open import Relation.Nullary using (yes ; no ; ¬_)

open import MonoRef.Coercions.Reduction
open import MonoRef.Coercions.Syntax
open import MonoRef.Dynamics.Simple.Frames
  _⟹_ Inert
open import MonoRef.Dynamics.Simple.Reduction
  _⟹_ Inert make-coercion Inert⇒¬Ref
open import MonoRef.Dynamics.Simple.Value
  _⟹_ Inert
open import MonoRef.Dynamics.Store.Simple
  _⟹_ Inert Active inertP ¬Inert⇒Active make-coercion Inert⇒¬Ref
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


open ParamReduction Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑
open ParamReduction/ν-cast/ν-update/ref/store/⟶ᵤ ν-cast ν-update/ref store _⟶ᵤ_


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

val⟶ᵤᵣ⊥ : ∀ {Σ Σ' A} {e : Σ ∣ ∅ ⊢ A} {ν : Store Σ} {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → Value e → ¬ (e , ν ⟶ᵤᵣ e' , ν')
val⟶ᵤᵣ⊥ v (pure red) = val⟶ᵤ⊥ v red
val⟶ᵤᵣ⊥ v (mono red) = val⟶ₘ⊥ v red
val⟶ᵤᵣ⊥ () (cong (ξ-appₗ _) _)
val⟶ᵤᵣ⊥ () (cong (ξ-appᵣ _) _)
val⟶ᵤᵣ⊥ v (cong ξ-suc red)
  with v
... | V-suc v' = val⟶ᵤᵣ⊥ v' red
val⟶ᵤᵣ⊥ () (cong (ξ-caseₚ _ _) _)
val⟶ᵤᵣ⊥ v (cong (ξ-×ₗ _) red)
  with v
... | (V-pair v₁ _) = val⟶ᵤᵣ⊥ v₁ red
val⟶ᵤᵣ⊥ v (cong (ξ-×ᵣ _) red)
  with v
... | (V-pair _ v₂) = val⟶ᵤᵣ⊥ v₂ red
val⟶ᵤᵣ⊥ () (cong ξ-πₗ _)
val⟶ᵤᵣ⊥ () (cong ξ-πᵣ _)
val⟶ᵤᵣ⊥ () (cong ξ-ref _)
val⟶ᵤᵣ⊥ () (cong (ξ-!ₛ _) _)
val⟶ᵤᵣ⊥ () (cong ξ-! _)
val⟶ᵤᵣ⊥ () (cong (ξ-:=ₛₗ _ _) _)
val⟶ᵤᵣ⊥ () (cong (ξ-:=ₛᵣ _ _) _)
val⟶ᵤᵣ⊥ () (cong (ξ-:=ₗ _) _)
val⟶ᵤᵣ⊥ () (cong (ξ-:=ᵣ _) _)
val⟶ᵤᵣ⊥ v (cong (ξ-<> _) red)
  with v
... | V-cast v' _ = val⟶ᵤᵣ⊥ v' red
val⟶ᵤᵣ⊥ () (cong-error (ξ-appₗ _))
val⟶ᵤᵣ⊥ () (cong-error (ξ-appᵣ _))
val⟶ᵤᵣ⊥ v (cong-error ξ-suc)
  with v
... | V-suc ()
val⟶ᵤᵣ⊥ () (cong-error (ξ-caseₚ _ _))
val⟶ᵤᵣ⊥ v (cong-error (ξ-×ₗ _))
  with v
... | V-pair () _
val⟶ᵤᵣ⊥ v (cong-error (ξ-×ᵣ _))
  with v
... | V-pair _ ()
val⟶ᵤᵣ⊥ () (cong-error ξ-πₗ)
val⟶ᵤᵣ⊥ () (cong-error ξ-πᵣ)
val⟶ᵤᵣ⊥ () (cong-error ξ-ref)
val⟶ᵤᵣ⊥ () (cong-error (ξ-!ₛ _))
val⟶ᵤᵣ⊥ () (cong-error ξ-!)
val⟶ᵤᵣ⊥ () (cong-error (ξ-:=ₛₗ _ _))
val⟶ᵤᵣ⊥ () (cong-error (ξ-:=ₛᵣ _ _))
val⟶ᵤᵣ⊥ () (cong-error (ξ-:=ₗ _))
val⟶ᵤᵣ⊥ () (cong-error (ξ-:=ᵣ _))
val⟶ᵤᵣ⊥ v (cong-error (ξ-<> _))
  with v
... | V-cast () _

scv⟶ᵤᵣ⟹cv' : ∀ {Σ Σ' A} {e : Σ ∣ ∅ ⊢ A} {cv : CastedValue e} {ν : Store Σ}
  {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → StrongCastedValue cv
  → e , ν ⟶ᵤᵣ e' , ν'
  → CastedValue e' ⊎ Erroneous e'
scv⟶ᵤᵣ⟹cv' _ (pure (ι v)) = inj₁ (v⇑ v)
scv⟶ᵤᵣ⟹cv' _ (pure (!? v))
  with inertP (make-coercion _ _)
... | yes c-inert = inj₁ (v⇑ (V-cast v c-inert))
... | no c-¬inert = inj₁ (cast-val v (¬Inert⇒Active c-¬inert))
scv⟶ᵤᵣ⟹cv' _ (pure (`× {c₁ = c₁} {c₂ = c₂} a b))
  with inertP c₁ | inertP c₂
... | yes c₁-inert | yes c₂-inert =
  inj₁ (v⇑ (V-pair (V-cast a c₁-inert) (V-cast b c₂-inert)))
... | no c₁-¬inert | yes c₂-inert =
  inj₁ (cv-pair (cast-val a (¬Inert⇒Active c₁-¬inert)) (v⇑ (V-cast b c₂-inert))
    (inj₁ ⟨ SCV-cast a (¬Inert⇒Active c₁-¬inert) , V-cast b c₂-inert ⟩))
... | yes c₁-inert | no c₂-¬inert =
  inj₁ (cv-pair (v⇑ (V-cast a c₁-inert)) (cast-val b (¬Inert⇒Active c₂-¬inert))
    (inj₂ (inj₁ ⟨ V-cast a c₁-inert , SCV-cast b (¬Inert⇒Active c₂-¬inert) ⟩)))
... | no c₁-¬inert | no c₂-¬inert =
  inj₁ (cv-pair (cast-val a (¬Inert⇒Active c₁-¬inert)) (cast-val b (¬Inert⇒Active c₂-¬inert))
    (inj₂ (inj₂ ⟨ SCV-cast a (¬Inert⇒Active c₁-¬inert) ,
                  SCV-cast b (¬Inert⇒Active c₂-¬inert) ⟩)))
scv⟶ᵤᵣ⟹cv' _ (pure (`⊥ x A≁B)) = inj₂ Err-intro
scv⟶ᵤᵣ⟹cv' _ (mono (castref1 R rtti∼T₂ x)) =
  inj₁ (v⇑ (V-addr (Σ-cast⟹∈ (ref⟹∈ R) (⊓ rtti∼T₂)) (⊓⟹⊑ᵣ rtti∼T₂)))
scv⟶ᵤᵣ⟹cv' _ (mono (castref2 {ν = ν} R rtti∼T₂ eq)) =
  inj₁ (v⇑ (V-addr (ref-ν⟹∈ R ν) (⊓⟹⊑ᵣ-with-≡ rtti∼T₂ eq)))
scv⟶ᵤᵣ⟹cv' _ (mono (castref3 _ _)) = inj₂ Err-intro
scv⟶ᵤᵣ⟹cv' () (cong (ξ-appₗ _) _)
scv⟶ᵤᵣ⟹cv' () (cong (ξ-appᵣ _) _)
scv⟶ᵤᵣ⟹cv' () (cong ξ-suc _)
scv⟶ᵤᵣ⟹cv' () (cong (ξ-caseₚ x x₁) red)
scv⟶ᵤᵣ⟹cv' _ (cong {A = A} (ξ-×ₗ N) red)

  -- we abstract over the strenthened frame so we can pattern match on the
  -- strong casted value constructor.

  with typeprecise-strenthen-frame {A = A} (⟶ᵤᵣ⟹⊑ₕ red) (ξ-×ₗ N)
scv⟶ᵤᵣ⟹cv' (SCV-pair _ _ p) (cong (ξ-×ₗ _) _) | _

  -- we case-analysis on the shape of the pair and process each case accordingly

   with p
scv⟶ᵤᵣ⟹cv' (SCV-pair _ _ _) (cong (ξ-×ₗ _) red) | _ | inj₁ ⟨ scv₁ , v₂ ⟩
    with scv⟶ᵤᵣ⟹cv' scv₁ red
...    | inj₁ cv₁'

  -- we check if the result is a strong casted value, so we can build the shape
  -- of the result pair accordingly.

     with scv-decidable cv₁'
...      | yes scv₁' = inj₁ (cv-pair cv₁' (v⇑ v₂') (inj₁ ⟨ scv₁' , v₂' ⟩))
     where v₂' = typeprecise-strenthen-val (⟶ᵤᵣ⟹⊑ₕ red) v₂
...      | no ¬scv =
  inj₁ (v⇑ (V-pair (¬scv⇒Value ¬scv) (typeprecise-strenthen-val (⟶ᵤᵣ⟹⊑ₕ red) v₂)))
scv⟶ᵤᵣ⟹cv' (SCV-pair _ _ _) (cong (ξ-×ₗ N) red) | _ | inj₁ ⟨ _ , _ ⟩ | inj₂ err =
  inj₂ (Err-plugged err (ξ-×ₗ (typeprecise-strenthen-expr (⟶ᵤᵣ⟹⊑ₕ red) N)))
scv⟶ᵤᵣ⟹cv' (SCV-pair cv₁ cv₂ p) (cong (ξ-×ₗ N) red) | _ | inj₂ (inj₁ ⟨ v₁ , scv₂ ⟩) =
  ⊥-elim (val⟶ᵤᵣ⊥ v₁ red)
scv⟶ᵤᵣ⟹cv' (SCV-pair cv₁ cv₂ p) (cong (ξ-×ₗ N) red) | _ | inj₂ (inj₂ ⟨ scv₁ , scv₂ ⟩)
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
scv⟶ᵤᵣ⟹cv' (SCV-pair _ _ _) (cong (ξ-×ₗ N) red) | _ | inj₂ (inj₂ ⟨ _ , _ ⟩) | inj₂ err =
  inj₂ (Err-plugged err (ξ-×ₗ (typeprecise-strenthen-expr (⟶ᵤᵣ⟹⊑ₕ red) N)))
scv⟶ᵤᵣ⟹cv' cv (cong {B = B} (ξ-×ᵣ M) red)
  with typeprecise-strenthen-frame {B = B} (⟶ᵤᵣ⟹⊑ₕ red) (ξ-×ᵣ M)
scv⟶ᵤᵣ⟹cv' (SCV-pair _ _ p) (cong (ξ-×ᵣ _) _) | _
    with p
scv⟶ᵤᵣ⟹cv' (SCV-pair _ _ _) (cong (ξ-×ᵣ _) red) | _ | inj₁ ⟨ _ , v₂ ⟩ =
  ⊥-elim (val⟶ᵤᵣ⊥ v₂ red)
scv⟶ᵤᵣ⟹cv' (SCV-pair _ _ _) (cong (ξ-×ᵣ _) red) | _ | inj₂ (inj₁ ⟨ v₁ , scv₂ ⟩)
     with scv⟶ᵤᵣ⟹cv' scv₂ red
... | inj₁ cv₂'
      with scv-decidable cv₂'
...  | yes scv₂' = inj₁ (cv-pair (v⇑ v₁') cv₂' (inj₂ (inj₁ ⟨ v₁' , scv₂' ⟩)))
      where v₁' = typeprecise-strenthen-val (⟶ᵤᵣ⟹⊑ₕ red) v₁
...  | no ¬scv₂' =
  inj₁ (v⇑ (V-pair (typeprecise-strenthen-val (⟶ᵤᵣ⟹⊑ₕ red) v₁)
                   (¬scv⇒Value ¬scv₂')))
scv⟶ᵤᵣ⟹cv' (SCV-pair _ _ _) (cong (ξ-×ᵣ M) red) | _ | inj₂ (inj₁ _) | inj₂ err =
  inj₂ (Err-plugged err (ξ-×ᵣ (typeprecise-strenthen-expr (⟶ᵤᵣ⟹⊑ₕ red) M)))
scv⟶ᵤᵣ⟹cv' (SCV-pair cv₁ _ _) (cong (ξ-×ᵣ M) red) | _ | inj₂ (inj₂ ⟨ scv₁ , scv₂ ⟩)
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
scv⟶ᵤᵣ⟹cv' (SCV-pair _ _ _) (cong (ξ-×ᵣ M) red) | _ | inj₂ (inj₂ _) | inj₂ err =
  inj₂ (Err-plugged err (ξ-×ᵣ (typeprecise-strenthen-expr (⟶ᵤᵣ⟹⊑ₕ red) M)))
scv⟶ᵤᵣ⟹cv' () (cong ξ-πₗ _)
scv⟶ᵤᵣ⟹cv' () (cong ξ-πᵣ _)
scv⟶ᵤᵣ⟹cv' () (cong ξ-ref _)
scv⟶ᵤᵣ⟹cv' () (cong (ξ-!ₛ _) _)
scv⟶ᵤᵣ⟹cv' () (cong ξ-! _)
scv⟶ᵤᵣ⟹cv' () (cong (ξ-:=ₛₗ _ _) _)
scv⟶ᵤᵣ⟹cv' () (cong (ξ-:=ₛᵣ _ _) _)
scv⟶ᵤᵣ⟹cv' () (cong (ξ-:=ₗ _) _)
scv⟶ᵤᵣ⟹cv' () (cong (ξ-:=ᵣ _) _)
scv⟶ᵤᵣ⟹cv' scv (cong (ξ-<> c) red)
  with scv
... | (SCV-cast v ac) = ⊥-elim (val⟶ᵤᵣ⊥ v red)
... | (SCV-ccast cv scv' c)
   with scv⟶ᵤᵣ⟹cv' scv' red
...  | inj₂ err = inj₂ (Err-plugged err (ξ-<> c) )
...  | inj₁ cv'
    with scv-decidable cv'
...   | yes cv'-scv' = inj₁ (cast-cval cv' cv'-scv' c)
...   | no ¬scv'
     with inertP c
...    | yes c-inert = inj₁ (v⇑ (V-cast (¬scv⇒Value ¬scv') c-inert))
...    | no c-¬inert = inj₁ (cast-val (¬scv⇒Value ¬scv') (¬Inert⇒Active c-¬inert))
scv⟶ᵤᵣ⟹cv' _ (cong-error _) = inj₂ Err-intro
