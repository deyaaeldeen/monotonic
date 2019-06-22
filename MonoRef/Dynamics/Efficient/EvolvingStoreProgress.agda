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

progress-evolving-store/mono :
  ∀ {Σ Σ' A B} {M : Σ ∣ ∅ ⊢ A} {e : Σ ∣ ∅ ⊢ B} {cv : CastedValue e} {e' : Σ' ∣ ∅ ⊢ B} {ν' : Store Σ'}
  → (ν : Store Σ)
  → ¬ NormalStore ν
  → StrongCastedValue cv
  → B ∈ Σ
  → e , ν ⟶ₘ e' , ν'
  → Progress M ν
progress-evolving-store/mono ν ν-¬NS scv B∈Σ red@(castref2 R rtti∼T₂ rtti≡T₂) =
  step (hcast ν-¬NS B∈Σ scv (mono red) (v⇑ (S-Val (V-addr (ref-ν⟹∈ R ν) (⊓⟹⊑ᵣ-with-≡ rtti∼T₂ rtti≡T₂)))))
progress-evolving-store/mono ν ν-¬NS scv B∈Σ red@(castref3 _ _) =
  step (error ν-¬NS B∈Σ (mono red) Err-intro)

{-
  Unrolled the definition of the address value so I can get the refl constructor
  for decidable equality between the rtti and the type of the pointer in hand
-}
progress-evolving-store/mono _ _ _ _ (castref1 (V-cast _ c) _ _) =
  ⊥-elim (Inert⇒¬Ref c)
progress-evolving-store/mono {B = B} ν ν-¬NS scv B∈Σ red@(castref1 (S-Val (V-addr {A = A} A∈Σ A⊑T)) rtti∼T₂ ⊓rtti∼T₂≢rtti)
  with ≡Type-decidable B A
... | yes refl = step (hdrop ν-¬NS A∈Σ scv (⊓⟹⊑ₗ rtti∼T₂) ⊓rtti∼T₂≢rtti (mono red))
... | no B≢A =
  step (hmcast ν-¬NS B∈Σ scv A∈Σ (PIE-ptr B≢A A∈Σ) (⊓⟹⊑ₗ rtti∼T₂) (mono red) -- B≢A
          (v⇑ (S-Val (V-addr (Σ-cast⟹∈ A∈Σ (⊓ rtti∼T₂)) (⊓⟹⊑ᵣ rtti∼T₂)))))

progress-evolving-store : ∀ {Σ A} {M : Σ ∣ ∅ ⊢ A}
  → (ν : Store Σ) → ¬ NormalStore ν → Progress M ν
progress-evolving-store ν ν-¬NS
  with ¬NormalStore⇒∃cv ν-¬NS
... | ⟨ A , ⟨ A∈Σ , ⟨ _ , intro scv _ ⟩ ⟩ ⟩
   with ⟶ᵤᵣprogress-scv scv ν
... | step-d red'@(ξ-×ₗ red)
  with scv⟶ᵤᵣ⟹cv' scv red'
...  | inj₂ err = step (error ν-¬NS A∈Σ red' err)
...  | inj₁ cv'
   with get-ptr red | progress-store ν A∈Σ red'
...  | _ | S-no-change = step (hcast ν-¬NS A∈Σ scv red' cv')
...  | _ | S-cyclic T'⊑T T'≢T =
  step (hdrop ν-¬NS A∈Σ scv T'⊑T T'≢T red')
...  | _ | S-acyclic B∈Σ A≢B C⊑B =
  step (hmcast ν-¬NS A∈Σ scv B∈Σ A≢B C⊑B red' cv')
progress-evolving-store ν ν-¬NS | ⟨ _ , ⟨ A∈Σ , ⟨ _ , intro scv _ ⟩ ⟩ ⟩ | step-a red'@(switch (ξ-×ₗ red))
  with scv⟶ᵤᵣ⟹cv' scv red'
...  | inj₂ err = step (error ν-¬NS A∈Σ red' err)
...  | inj₁ cv'
   with get-ptr red | progress-store ν A∈Σ red'
...  | _ | S-no-change = step (hcast ν-¬NS A∈Σ scv red' cv')
...  | _ | S-cyclic T'⊑T T'≢T =
  step (hdrop ν-¬NS A∈Σ scv T'⊑T T'≢T red')
...  | _ | S-acyclic B∈Σ A≢B C⊑B =
  step (hmcast ν-¬NS A∈Σ scv B∈Σ A≢B C⊑B red' cv')
progress-evolving-store ν ν-¬NS | ⟨ _ , ⟨ A∈Σ , ⟨ _ , intro scv _ ⟩ ⟩ ⟩ | step-d red'@(ξ-×ᵣ red)
  with scv⟶ᵤᵣ⟹cv' scv red'
...  | inj₂ err = step (error ν-¬NS A∈Σ red' err)
...  | inj₁ cv'
   with get-ptr red | progress-store ν A∈Σ red'
...  | _ | S-no-change = step (hcast ν-¬NS A∈Σ scv red' cv')
...  | _ | S-cyclic T'⊑T T'≢T =
  step (hdrop ν-¬NS A∈Σ scv T'⊑T T'≢T red')
...  | _ | S-acyclic B∈Σ A≢B C⊑B =
  step (hmcast ν-¬NS A∈Σ scv B∈Σ A≢B C⊑B red' cv')
progress-evolving-store ν ν-¬NS | ⟨ _ , ⟨ A∈Σ , ⟨ _ , intro scv _ ⟩ ⟩ ⟩ | step-a red'@(switch (ξ-×ᵣ red))
  with scv⟶ᵤᵣ⟹cv' scv red'
...  | inj₂ err = step (error ν-¬NS A∈Σ red' err)
...  | inj₁ cv'
   with get-ptr red | progress-store ν A∈Σ red'
...  | _ | S-no-change = step (hcast ν-¬NS A∈Σ scv red' cv')
...  | _ | S-cyclic T'⊑T T'≢T =
  step (hdrop ν-¬NS A∈Σ scv T'⊑T T'≢T red')
...  | _ | S-acyclic B∈Σ A≢B C⊑B =
  step (hmcast ν-¬NS A∈Σ scv B∈Σ A≢B C⊑B red' cv')
progress-evolving-store _ ν-¬NS | ⟨ _ , ⟨ A∈Σ , _ ⟩ ⟩ | step-d red@ξ-×ₗ-error =
  step (error ν-¬NS A∈Σ red Err-intro)
progress-evolving-store _ ν-¬NS | ⟨ _ , ⟨ A∈Σ , _ ⟩ ⟩ | step-a (switch red@ξ-×ₗ-error) =
  step (error ν-¬NS A∈Σ red Err-intro)
progress-evolving-store _ ν-¬NS | ⟨ _ , ⟨ A∈Σ , _ ⟩ ⟩ | step-d red@ξ-×ᵣ-error =
  step (error ν-¬NS A∈Σ red Err-intro)
progress-evolving-store _ ν-¬NS | ⟨ _ , ⟨ A∈Σ , _ ⟩ ⟩ | step-a (switch red@ξ-×ᵣ-error) =
  step (error ν-¬NS A∈Σ red Err-intro)
progress-evolving-store ν ν-¬NS | ⟨ _ , ⟨ A∈Σ , ⟨ _ , intro scv _ ⟩ ⟩ ⟩ | step-a red'@(ξ-cast red)
  with scv⟶ᵤᵣ⟹cv' scv red'
...  | inj₂ err = step (error ν-¬NS A∈Σ red' err)
...  | inj₁ cv'
   with get-ptr red | progress-store ν A∈Σ red'
...  | _ | S-no-change = step (hcast ν-¬NS A∈Σ scv red' cv')
...  | _ | S-cyclic T'⊑T T'≢T =
  step (hdrop ν-¬NS A∈Σ scv T'⊑T T'≢T red')
...  | _ | S-acyclic B∈Σ A≢B C⊑B =
  step (hmcast ν-¬NS A∈Σ scv B∈Σ A≢B C⊑B red' cv')
progress-evolving-store ν ν-¬NS | ⟨ _ , ⟨ A∈Σ , ⟨ _ , intro scv _ ⟩ ⟩ ⟩ | step-a (mono red) =
  progress-evolving-store/mono ν ν-¬NS scv A∈Σ red
progress-evolving-store ν ν-¬NS | ⟨ _ , ⟨ A∈Σ , _ ⟩ ⟩ | step-a red@ξ-cast-error =
  step (error ν-¬NS A∈Σ red Err-intro)
progress-evolving-store ν ν-¬NS | ⟨ _ , ⟨ A∈Σ , ⟨ _ , intro scv _ ⟩ ⟩ ⟩ | step-a red@(pure _)
  with scv⟶ᵤᵣ⟹cv' scv red
...  | inj₁ cv' = step (hcast ν-¬NS A∈Σ scv red cv')
...  | inj₂ err = step (error ν-¬NS A∈Σ red err)
