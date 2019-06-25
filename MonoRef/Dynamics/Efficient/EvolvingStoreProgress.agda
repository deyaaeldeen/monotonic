module MonoRef.Dynamics.Efficient.EvolvingStoreProgress where

open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes ; no ; ¬_)

open import MonoRef.Coercions.NormalForm.Compose
open import MonoRef.Coercions.NormalForm.Reduction
open import MonoRef.Coercions.NormalForm.Syntax
  renaming (NormalFormCoercion to _⟹_ ; InertNormalForm to Inert
           ; ActiveNormalForm to Active ; inert-normalform-decidable to inertP
           ; ¬Inert⇒Active-normform to ¬Inert⇒Active)
open import MonoRef.Coercions.NormalForm.Make renaming (make-normal-form-coercion to make-coercion)
open import MonoRef.Dynamics.Efficient.Frames
  _⟹_ Inert
open import MonoRef.Dynamics.Efficient.Reduction
  _⟹_ Inert Active make-coercion Inert⇒¬Ref
open import MonoRef.Dynamics.Store.Efficient
  _⟹_ Inert Active inertP ¬Inert⇒Active make-coercion Inert⇒¬Ref compose
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Dynamics.Efficient.ActiveCastProgress
open import MonoRef.Dynamics.Efficient.CastedValueProgress
open import MonoRef.Dynamics.Efficient.ProgressDef
open import MonoRef.Dynamics.Efficient.Properties
open import MonoRef.Dynamics.Efficient.StoreProgress
open import MonoRef.Dynamics.Efficient.Value
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


open ParamReduction SimpleValue Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑
open ParamReduction/ν-cast/ν-update/ref/store/⟶ᵤ ν-cast ν-update/ref store _⟶ᵤ_


proof : ∀ {Σ Σ' A B bc} {M : Σ ∣ ∅ ⊢ B} {e : Σ ∣ ∅ ⊢ A} {cv : CastedValue e} {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → A ∈ Σ → (ν : Store Σ) → ¬ NormalStore ν → StrongCastedValue cv → bc / e , ν ⟶ᵤᵣ e' , ν' → Progress M ν
proof A∈Σ ν ν-¬NS scv R with scv⟶ᵤᵣ⟹cv' scv R
...   | inj₂ err = step (error ν-¬NS A∈Σ R err)
...   | inj₁ cv' with get-ptr R | progress-store ν A∈Σ R
...   | _ | S-no-change = step (hcast ν-¬NS A∈Σ scv R cv')
...   | _ | S-cyclic T'⊑T T'≢T = step (hdrop ν-¬NS A∈Σ scv T'⊑T T'≢T R)
...   | _ | S-acyclic B∈Σ A≢B C⊑B = step (hmcast ν-¬NS A∈Σ scv B∈Σ A≢B C⊑B R cv')

progress-evolving-store : ∀ {Σ A} {M : Σ ∣ ∅ ⊢ A}
  → (ν : Store Σ) → ¬ NormalStore ν → Progress M ν
progress-evolving-store ν ν-¬NS
  with ¬NormalStore⇒∃cv ν-¬NS
... | ⟨ A , ⟨ A∈Σ , ⟨ _ , intro scv _ ⟩ ⟩ ⟩
   with ⟶ᵤᵣprogress-scv scv ν
...  | step-d R = proof A∈Σ ν ν-¬NS scv R
...  | step-a R = proof A∈Σ ν ν-¬NS scv R
