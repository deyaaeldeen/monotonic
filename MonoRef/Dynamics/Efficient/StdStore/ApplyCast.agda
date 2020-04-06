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


apply-cast : ∀ {A B Σ Σ'}
  → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
  → (Q : List (SuspendedCast Σ))
  → ∀ {e : proj₁ (merge' Σ'⊑ₕΣ Q) ∣ ∅ ⊢ A}
  → (v : Value e)
  → A ⟹ B
  → CastResult Σ'⊑ₕΣ Q B

apply-active-cast : ∀ {Σ Σ' A B} {c : A ⟹ B}
  → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
  → (Q : List (SuspendedCast Σ))
  → ∀ {e : proj₁ (merge' Σ'⊑ₕΣ Q) ∣ ∅ ⊢ A} → (v : SimpleValue e)
  → (ac : Active c)
  → CastResult Σ'⊑ₕΣ Q B

apply-active-cast/final : ∀ {Σ Σ' A B} {c : FinalCoercion A B}
  → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
  → (Q : List (SuspendedCast Σ))
  → ∀ {e : proj₁ (merge' Σ'⊑ₕΣ Q) ∣ ∅ ⊢ A} (v : SimpleValue e)
  → (ac : ActiveFinal c)
  → CastResult Σ'⊑ₕΣ Q B

apply-active-cast/middle : ∀ {Σ Σ' A B} {c : MiddleCoercion A B}
  → (Σ'⊑ₕΣ : Σ' ⊑ₕ Σ)
  → (Q : List (SuspendedCast Σ))
  → ∀ {e : proj₁ (merge' Σ'⊑ₕΣ Q) ∣ ∅ ⊢ A} → (v : SimpleValue e)
  → (ac : ActiveMiddle c)
  → CastResult Σ'⊑ₕΣ Q B

apply-active-cast/middle Σ'⊑ₕΣ Q v (A-id _)
  rewrite cong (merge' Σ'⊑ₕΣ) (sym (++-identityʳ Q)) = done [] (S-Val v)
apply-active-cast/middle Σ'⊑ₕΣ Q (V-pair v₁ v₂) (A-prod c d)
  with apply-cast Σ'⊑ₕΣ Q v₁ c
... | error = error
... | done Qₗ v₁'
    with apply-cast Σ'⊑ₕΣ (Q ++ Qₗ) v₂' d
    where
      v₂' = typeprecise-strenthen-val (merge-respects-⊑ₕ' Σ'⊑ₕΣ Q Qₗ) v₂
...   | error = error
...   | done Qᵣ v₂' rewrite ++-assoc Q Qₗ Qᵣ =
  done (Qₗ ++ Qᵣ) (S-Val (V-pair (typeprecise-strenthen-val mergeQ+Qₗ+Qᵣ⊑ₕmergeQ+Qₗ v₁') v₂'))
    where
      mergeQ+Qₗ+Qᵣ⊑ₕmergeQ+Qₗ : proj₁ (merge' Σ'⊑ₕΣ (Q ++ Qₗ ++ Qᵣ)) ⊑ₕ proj₁ (merge' Σ'⊑ₕΣ (Q ++ Qₗ))
      mergeQ+Qₗ+Qᵣ⊑ₕmergeQ+Qₗ rewrite sym (++-assoc Q Qₗ Qᵣ) = merge-respects-⊑ₕ' Σ'⊑ₕΣ (Q ++ Qₗ) Qᵣ
apply-active-cast/middle _ _ _ (A-fail) = error
apply-active-cast/middle Σ'⊑ₕΣ Q (V-addr {A} A∈Σ A⊑B) (A-Ref C C⊑B)
  with ∼-decidable A C
... | no _ = error
... | yes A∼C =
  done [ cast (proj₂ (weaken-ptr/⊑ₕ (⊑ₕ-trans (proj₂ (proj₂ (merge' Σ'⊑ₕΣ Q))) (proj₁ (proj₂ (merge' Σ'⊑ₕΣ Q)))) A∈Σ)) C ]
       (S-Val (V-addr (merge-extension-soundness Σ'⊑ₕΣ Q A∈Σ A∼C) (⊑-trans (⊓⟹⊑ᵣ A∼C) C⊑B)))
apply-active-cast/final Σ'⊑ₕΣ Q v (A-middle c) = apply-active-cast/middle Σ'⊑ₕΣ Q v c

apply-active-cast _ _ () A-id⋆
apply-active-cast Σ'⊑ₕΣ Q v (A-final c) = apply-active-cast/final Σ'⊑ₕΣ Q v c
apply-active-cast _ _ () (A-prjSeq _ _)

apply-cast Σ'⊑ₕΣ Q (S-Val v) c
  with inertP c
... | yes c-inert rewrite cong (merge' Σ'⊑ₕΣ) (sym (++-identityʳ Q)) =
  done [] (V-cast v c-inert)
... | no c-¬inert = apply-active-cast Σ'⊑ₕΣ Q v (¬Inert⇒Active c-¬inert)
apply-cast Σ'⊑ₕΣ Q (V-cast {c = c} v ic) d
  with inertP (compose c d)
... | yes c-inert rewrite cong (merge' Σ'⊑ₕΣ) (sym (++-identityʳ Q)) =
  done [] (V-cast v c-inert)
... | no c-¬inert =
  apply-active-cast Σ'⊑ₕΣ Q v (¬Inert⇒Active c-¬inert)
