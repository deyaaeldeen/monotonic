module MonoRef.Dynamics.Simple.EvolvingStoreProgress where

open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes ; no ; ¬_)

open import MonoRef.Coercions.Reduction
open import MonoRef.Coercions.Syntax
open import MonoRef.Dynamics.Simple.Frames
  _⟹_ Inert
open import MonoRef.Dynamics.Simple.Reduction
  _⟹_ Inert make-coercion Inert⇒¬Ref
open import MonoRef.Dynamics.Store.Simple
  _⟹_ Inert Active inertP ¬Inert⇒Active make-coercion Inert⇒¬Ref
open import MonoRef.Language.TargetWithoutBlame
  _⟹_ Inert
open import MonoRef.Dynamics.Simple.ActiveCastProgress
open import MonoRef.Dynamics.Simple.CastedValueProgress
open import MonoRef.Dynamics.Simple.ProgressDef
open import MonoRef.Dynamics.Simple.Properties
open import MonoRef.Dynamics.Simple.StoreProgress
open import MonoRef.Dynamics.Simple.Value
  _⟹_ Inert
open import MonoRef.Static.Context
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


open ParamReduction Value CastedValue StrongCastedValue ref⟹T ref⟹∈ ref⟹⊑
open ParamReduction/ν-cast/ν-update/ref/store/⟶ᵤ ν-cast ν-update/ref store _⟶ᵤ_

progress-evolving-store : ∀ {Σ A} {M : Σ ∣ ∅ ⊢ A}
  → (ν : Store Σ) → ¬ NormalStore ν → Progress M ν
progress-evolving-store ν ν-¬NS
  with ¬NormalStore⇒∃cv ν-¬NS
... | ⟨ A , ⟨ A∈Σ , ⟨ _ , intro scv _ ⟩ ⟩ ⟩
   with ⟶ᵤᵣprogress-scv scv ν
...  | step R
    with scv⟶ᵤᵣ⟹cv' scv R
...   | inj₂ err = step (error ν-¬NS A∈Σ R err)
...   | inj₁ cv' with get-ptr R | progress-store ν A∈Σ R
...   | _ | S-no-change = step (hcast ν-¬NS A∈Σ scv R cv')
...   | _ | S-cyclic T'⊑T T'≢T = step (hdrop ν-¬NS A∈Σ scv T'⊑T T'≢T R)
...   | _ | S-acyclic B∈Σ A≢B C⊑B = step (hmcast ν-¬NS A∈Σ scv B∈Σ A≢B C⊑B R cv')
