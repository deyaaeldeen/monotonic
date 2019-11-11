module MonoRef.Dynamics.Store.Ptr.Properties where

open import Data.List.Any using (here ; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Fin using (Fin) renaming (_<_ to _Fin<_)
open import Data.Fin.Properties
  using (<-trans ; suc-injective) renaming (<-cmp to <-cmpF)
open import Function using (_on_ ; _∘_)
open import Level using () renaming (zero to ℓ₀)
open import Relation.Binary
  using (Rel ; Trichotomous ; Tri ; tri< ; tri≈ ; tri> ; IsStrictTotalOrder)
open import Relation.Binary using (Decidable)
open import Relation.Binary.HeterogeneousEquality using (_≅_ ; ≅-to-≡ ; ≡-to-≅) renaming (refl to hrefl)
open import Relation.Binary.PropositionalEquality as P using (_≡_ ; _≢_ ; refl; sym; trans)
open import Relation.Nullary using (Dec ; yes ; no)

open import MonoRef.Dynamics.Store.Ptr
open import MonoRef.Static.Types.Relations


_<_ : ∀ {Σ} → Rel (Ptr Σ) ℓ₀
_<_ = _Fin<_ on ptr-index

ptr-addr≡⇒there≡ : ∀ {Σ A B C} → (x : A ∈ Σ) → (y : B ∈ Σ) → addr x ≅ addr y → addr (there {x = C} x) ≅ addr (there {x = C} y)
ptr-addr≡⇒there≡ x .x _≅_.refl = _≅_.refl

ptr-indexe≡⇒≡ : ∀ {Σ} → (x : Ptr Σ) → (y : Ptr Σ) → ptr-index x ≡ ptr-index y → x ≡ y
ptr-indexe≡⇒≡ (addr (here refl)) (addr (here refl)) w = refl
ptr-indexe≡⇒≡ (addr (here refl)) (addr (there y)) ()
ptr-indexe≡⇒≡ (addr (there x)) (addr (here px)) ()
ptr-indexe≡⇒≡ (addr (there x)) (addr (there y)) w =
  ≅-to-≡ (ptr-addr≡⇒there≡ x y (≡-to-≅ (ptr-indexe≡⇒≡ (addr x) (addr y) (suc-injective w))))

<-cmp : ∀ {Σ} → Trichotomous _≡_ (_<_ {Σ})
<-cmp x y
  with <-cmpF (ptr-index x) (ptr-index y)
<-cmp x y | tri< i<j i≢j j≮i = tri< i<j (λ {refl → i≢j refl}) j≮i
<-cmp x y | tri≈ ¬a b ¬c rewrite ptr-indexe≡⇒≡ x y b = tri≈ ¬c refl ¬c
<-cmp x y | tri> ¬a ¬b c = tri> ¬a (λ {refl → ¬b refl}) c

<-isStrictTotalOrder : ∀ {Σ} → IsStrictTotalOrder _≡_ (_<_ {Σ})
<-isStrictTotalOrder = record
  { isEquivalence = P.isEquivalence
  ; trans         = <-trans
  ; compare       = <-cmp
  }
