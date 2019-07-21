module MonoRef.Dynamics.Simple.EvolvingStoreProgress where

open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Nullary using (¬_)

open import MonoRef.Dynamics.Simple.ActiveCastProgress
open import MonoRef.Dynamics.Simple.CastedValueProgress
open import MonoRef.Dynamics.Simple.MonoStoreProgress
open import MonoRef.Dynamics.Simple.ProgressDef
open import MonoRef.Dynamics.Simple.Properties
open import MonoRef.Dynamics.Simple.SReduction
open import MonoRef.Dynamics.Simple.Store
open import MonoRef.Dynamics.Simple.StoreProgress
open import MonoRef.Dynamics.Simple.TargetWithoutBlame
open import MonoRef.Static.Context


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
