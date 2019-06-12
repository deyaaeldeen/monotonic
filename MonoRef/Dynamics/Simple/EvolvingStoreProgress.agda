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

progress-evolving-store/mono :
  ∀ {Σ Σ' A B} {M : Σ ∣ ∅ ⊢ A} {e : Σ ∣ ∅ ⊢ B} {cv : CastedValue e} {e' : Σ' ∣ ∅ ⊢ B} {ν' : Store Σ'}
  → (ν : Store Σ)
  → ¬ NormalStore ν
  → StrongCastedValue cv
  → B ∈ Σ
  → e , ν ⟶ₘ e' , ν'
  → Progress M ν
progress-evolving-store/mono ν ν-¬NS scv B∈Σ red@(castref2 R rtti∼T₂ rtti≡T₂) =
  step (hcast ν-¬NS B∈Σ scv (mono red) (v⇑ V-addr (ref-ν⟹∈ R ν) (⊓⟹⊑ᵣ-with-≡ rtti∼T₂ rtti≡T₂)))
progress-evolving-store/mono ν ν-¬NS scv B∈Σ red@(castref3 _ _) =
  step (error ν-¬NS B∈Σ (mono red) Err-intro)

{-
  Unrolled the definition of the address value so I can get the refl constructor
  for decidable equality between the rtti and the type of the pointer in hand
-}
progress-evolving-store/mono _ _ _ _ (castref1 (V-cast _ c) _ _) =
  ⊥-elim (Inert⇒¬Ref c)
progress-evolving-store/mono {B = B} ν ν-¬NS scv B∈Σ red@(castref1 (V-addr {A = A} A∈Σ A⊑T) rtti∼T₂ ⊓rtti∼T₂≢rtti)
  with ≡Type-decidable B A
... | yes refl =
  step (hdrop ν-¬NS A∈Σ scv (⊓⟹⊑ₗ rtti∼T₂) ⊓rtti∼T₂≢rtti (mono red))
... | no B≢A =
  step (hmcast ν-¬NS B∈Σ scv A∈Σ (PIE-ptr B≢A A∈Σ) (⊓⟹⊑ₗ rtti∼T₂) (mono red) -- B≢A
          (v⇑ V-addr (Σ-cast⟹∈ A∈Σ (⊓ rtti∼T₂)) (⊓⟹⊑ᵣ rtti∼T₂)))

progress-evolving-store/cong : ∀ {Σ Σ' T A B} {M : Σ ∣ ∅ ⊢ T} {e : Σ ∣ ∅ ⊢ A} {e' : Σ' ∣ ∅ ⊢ A} {ν' : Store Σ'}
  → (ν : Store Σ)
  → ¬ NormalStore ν
  → B ∈ Σ
  → (ξ : Frame {∅}{Σ} A B)
  → {cv : CastedValue (plug e ξ)}
  → e , ν ⟶ᵤᵣ e' , ν'
  → StrongCastedValue cv
  → Progress M ν
progress-evolving-store/cong ν ν-¬NS A∈Σ ξ red scv
  with scv⟶ᵤᵣ⟹cv' scv (cong ξ red)
... | inj₂ err = step (error ν-¬NS A∈Σ (cong ξ red) err)
... | inj₁ cv'
   with get-ptr red | progress-store ν A∈Σ (cong ξ red)
...  | _ | S-no-change = step (hcast ν-¬NS A∈Σ scv (cong ξ red) cv')
...  | _ | S-cyclic T'⊑T T'≢T =
  step (hdrop ν-¬NS A∈Σ scv T'⊑T T'≢T (cong ξ red))
...  | _ | S-acyclic B∈Σ A≢B C⊑B =
  step (hmcast ν-¬NS A∈Σ scv B∈Σ A≢B C⊑B (cong ξ red) cv')

progress-evolving-store : ∀ {Σ A} {M : Σ ∣ ∅ ⊢ A}
  → (ν : Store Σ) → ¬ NormalStore ν → Progress M ν
progress-evolving-store ν ν-¬NS
  with ¬NormalStore⇒∃cv ν-¬NS
... | ⟨ A , ⟨ A∈Σ , ⟨ _ , intro scv _ ⟩ ⟩ ⟩
   with ⟶ᵤᵣprogress-scv scv ν
... | step (cong ξ red) = progress-evolving-store/cong ν ν-¬NS A∈Σ ξ red scv
... | step (mono red) = progress-evolving-store/mono ν ν-¬NS scv A∈Σ red 
... | step red@(cong-error _) = step (error ν-¬NS A∈Σ red Err-intro)
... | step red@(pure _)
  with scv⟶ᵤᵣ⟹cv' scv red
...  | inj₁ cv' = step (hcast ν-¬NS A∈Σ scv red cv')
...  | inj₂ err = step (error ν-¬NS A∈Σ red err)
