module MonoRef.Dynamics.Efficient.StdStore.ApplyCast where

open import Data.List using (List ; [] ; [_] ; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (sym ; cong)
open import Relation.Nullary using (yes ; no)

open import MonoRef.Dynamics.Efficient.StdStore.SuspendedCast
open import MonoRef.Dynamics.Efficient.StdStore.Store
open import MonoRef.Dynamics.Efficient.Coercions
open import MonoRef.Dynamics.Efficient.TargetWithoutBlame
open import MonoRef.Dynamics.Efficient.Value
open import MonoRef.Static.Context
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


apply-cast : ∀ {A B Σ}
  → (Q : List (SuspendedCast Σ)) → ∀ {e : proj₁ (merge Q) ∣ ∅ ⊢ A} → (v : Value e) → A ⟹ B → CastResult Q B

apply-active-cast : ∀ {Σ A B} {c : A ⟹ B}
  → (Q : List (SuspendedCast Σ)) → ∀ {e : proj₁ (merge Q) ∣ ∅ ⊢ A} → (v : SimpleValue e) → (ac : Active c) → CastResult Q B

apply-active-cast/final : ∀ {Σ A B} {c : FinalCoercion A B}
  → (Q : List (SuspendedCast Σ)) → ∀ {e : proj₁ (merge Q) ∣ ∅ ⊢ A} (v : SimpleValue e) → (ac : ActiveFinal c)
  → CastResult Q B

apply-active-cast/middle : ∀ {Σ A B} {c : MiddleCoercion A B}
  → (Q : List (SuspendedCast Σ)) → ∀ {e : proj₁ (merge Q) ∣ ∅ ⊢ A} → (v : SimpleValue e) → (ac : ActiveMiddle c)
  → CastResult Q B

apply-active-cast/middle Q v A-id rewrite cong (merge' ⊑ₕ-refl) (sym (++-identityʳ Q)) =
  done [] (S-Val v)
apply-active-cast/middle Q (V-pair v₁ v₂) (A-prod c d)
  with apply-cast Q v₁ c
... | error = error
... | done Qₗ v₁'
    with apply-cast (Q ++ Qₗ) v₂' d
    where
      v₂' = typeprecise-strenthen-val (merge-respects-⊑ₕ Q Qₗ) v₂
...   | error = error
...   | done Qᵣ v₂' rewrite ++-assoc Q Qₗ Qᵣ =
  done (Qₗ ++ Qᵣ) (S-Val (V-pair (typeprecise-strenthen-val mergeQ+Qₗ+Qᵣ⊑ₕmergeQ+Qₗ v₁') v₂'))
    where
      mergeQ+Qₗ+Qᵣ⊑ₕmergeQ+Qₗ : proj₁ (merge (Q ++ Qₗ ++ Qᵣ)) ⊑ₕ proj₁ (merge (Q ++ Qₗ))
      mergeQ+Qₗ+Qᵣ⊑ₕmergeQ+Qₗ rewrite sym (++-assoc Q Qₗ Qᵣ) = merge-respects-⊑ₕ (Q ++ Qₗ) Qᵣ
apply-active-cast/middle _ _ (A-fail) = error
apply-active-cast/middle Q (V-addr {A} A∈Σ A⊑B) (A-Ref C C⊑B)
  with ∼-decidable A C
... | no _ = error
... | yes A∼C =
  done [ cast (proj₂ (weaken-ptr/⊑ₕ (proj₂ (merge Q)) A∈Σ)) C ]
       (S-Val (V-addr (merge-extension-soundness Q A∈Σ A∼C) (⊑-trans (⊓⟹⊑ᵣ A∼C) C⊑B)))
apply-active-cast/final Q v (A-middle c) = apply-active-cast/middle Q v c

apply-active-cast Q v (A-final c) = apply-active-cast/final Q v c
apply-active-cast _ () (A-prjSeq _ _)

apply-cast Q (S-Val v) c
  with inertP c
... | yes c-inert rewrite cong (merge' ⊑ₕ-refl) (sym (++-identityʳ Q)) =
  done [] (V-cast v c-inert)
... | no c-¬inert = apply-active-cast Q v (¬Inert⇒Active c-¬inert)
apply-cast Q (V-cast {c = c} v ic) d
  with inertP (compose c d)
... | yes c-inert rewrite cong (merge' ⊑ₕ-refl) (sym (++-identityʳ Q)) =
  done [] (V-cast v c-inert)
... | no c-¬inert =
  apply-active-cast Q v (¬Inert⇒Active c-¬inert)
