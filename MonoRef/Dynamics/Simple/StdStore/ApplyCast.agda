module MonoRef.Dynamics.Simple.StdStore.ApplyCast where

open import Data.List using (List ; [] ; [_] ; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.All using (_∷_) renaming (map to all-map)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (sym ; cong)
open import Relation.Nullary using (yes ; no)

open import MonoRef.Dynamics.Simple.StdStore.SuspendedCast
open import MonoRef.Dynamics.Simple.StdStore.Store
open import MonoRef.Dynamics.Simple.Coercions
open import MonoRef.Dynamics.Simple.TargetWithoutBlame
open import MonoRef.Dynamics.Simple.Value
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
apply-cast Σ'⊑ₕΣ Q v ι rewrite cong (merge' Σ'⊑ₕΣ) (sym (++-identityʳ Q)) = done [] v
apply-cast Σ'⊑ₕΣ Q (V-cast v (I-inj iA)) (prj iB) =
  apply-cast Σ'⊑ₕΣ Q v (make-coercion (injectable-to-type iA) (injectable-to-type iB))
apply-cast Σ'⊑ₕΣ Q v (inj x) rewrite cong (merge' Σ'⊑ₕΣ) (sym (++-identityʳ Q)) =
  done [] (V-cast v (I-inj x))
apply-cast Σ'⊑ₕΣ Q v (c ⇒ d) rewrite cong (merge' Σ'⊑ₕΣ) (sym (++-identityʳ Q)) =
  done [] (V-cast v (I-⇒ {c = c}{d = d}))
apply-cast _ Q (V-cast v ()) (_ `× _)
apply-cast {A = A `× B} Σ'⊑ₕΣ Q (V-pair v₁ v₂) (c `× d)
  with apply-cast Σ'⊑ₕΣ Q v₁ c
... | error = error
... | done Qₗ v₁'
    with apply-cast Σ'⊑ₕΣ (Q ++ Qₗ) v₂' d
    where
      v₂' = typeprecise-strenthen-val (merge-respects-⊑ₕ' Σ'⊑ₕΣ Q Qₗ) v₂
...   | error = error
...   | done Qᵣ v₂' rewrite ++-assoc Q Qₗ Qᵣ =
  done (Qₗ ++ Qᵣ) (V-pair (typeprecise-strenthen-val mergeQ+Qₗ+Qᵣ⊑ₕmergeQ+Qₗ v₁') v₂')
    where
      mergeQ+Qₗ+Qᵣ⊑ₕmergeQ+Qₗ : proj₁ (merge' Σ'⊑ₕΣ (Q ++ Qₗ ++ Qᵣ)) ⊑ₕ proj₁ (merge' Σ'⊑ₕΣ (Q ++ Qₗ))
      mergeQ+Qₗ+Qᵣ⊑ₕmergeQ+Qₗ rewrite sym (++-assoc Q Qₗ Qᵣ) = merge-respects-⊑ₕ' Σ'⊑ₕΣ (Q ++ Qₗ) Qᵣ
apply-cast _ Q (V-cast v ()) (Ref _ _)
apply-cast Σ'⊑ₕΣ Q (V-addr {A} A∈Σ A⊑B) (Ref _ B)
  with ∼-decidable A B
... | no _ = error
... | yes A∼B =
  done [ cast (proj₂ (weaken-ptr/⊑ₕ (⊑ₕ-trans (proj₂ (proj₂ (merge' Σ'⊑ₕΣ Q))) (proj₁ (proj₂ (merge' Σ'⊑ₕΣ Q)))) A∈Σ)) B ]
       (V-addr (merge-extension-soundness Σ'⊑ₕΣ Q A∈Σ A∼B) (⊓⟹⊑ᵣ A∼B))
apply-cast _ _ _ (`⊥ _) = error
