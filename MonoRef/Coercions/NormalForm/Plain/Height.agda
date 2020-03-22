module MonoRef.Coercions.NormalForm.Plain.Height where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ ; suc ; _+_ ; _*_ ; _≤_ ; _⊔_ ; z≤n ; s≤s)
open import Data.Nat.Properties
open ≤-Reasoning
open import Relation.Binary.PropositionalEquality using (refl ; sym ; cong₂)
open import Relation.Nullary using (yes ; no)

open import MonoRef.Coercions.NormalForm.Plain.Compose
open import MonoRef.Coercions.NormalForm.Plain.Height.Lemmas
open import MonoRef.Coercions.NormalForm.Plain.Make
open import MonoRef.Coercions.NormalForm.Plain.Size
open import MonoRef.Coercions.NormalForm.Plain.Syntax
open import MonoRef.Coercions.NormalForm.InEqReasoning
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


compose-middle-height : ∀ {A B C}
  → (mc : MiddleCoercion A B) → (md : MiddleCoercion B C)
  → {n : ℕ} {m : ‖ mc ‖ₘ + ‖ md ‖ₘ ≤ n }
  → ‖ compose-middle-internal mc md {n} {m} ‖ʰₘ ≤ ‖ mc ‖ʰₘ ⊔ ‖ md ‖ʰₘ

compose-middle-final-height : ∀ {A B C}
  → (fc : MiddleCoercion A B) → (nd : FinalCoercion B C)
  → {n : ℕ} {m : ‖ fc ‖ₘ + ‖ nd ‖ᶠ ≤ n }
  → ‖ compose-middle-final-internal fc nd {n} {m} ‖ʰᶠ ≤ ‖ fc ‖ʰₘ ⊔ ‖ nd ‖ʰᶠ

compose-final-normal-height : ∀ {A B C}
  → (fc : FinalCoercion A B) → (nd : NormalFormCoercion B C)
  → {n : ℕ} {m : ‖ fc ‖ᶠ + ‖ nd ‖ ≤ n }
  → ‖ compose-final-normal-internal fc nd {n} {m} ‖ʰᶠ ≤ ‖ fc ‖ʰᶠ ⊔ ‖ nd ‖ʰ

compose-normal-form-height : ∀ {A B C}
  → (nc : NormalFormCoercion A B) → (nd : NormalFormCoercion B C)
  → {n : ℕ} {m : ‖ nc ‖ + ‖ nd ‖ ≤ n }
  → ‖ compose-normal-form nc nd {n} {m} ‖ʰ ≤ ‖ nc ‖ʰ ⊔ ‖ nd ‖ʰ
compose-normal-form-height id⋆ d {suc n} {s≤s m} = n≤m⊔n _ _
compose-normal-form-height (prjSeq A≢⋆ i) d {suc n} {s≤s m}
  with compose-final-normal-internal i d {n} {c+a+b≤n⇒a+b≤n{‖ i ‖ᶠ} m}
     | compose-final-normal-height i d {n} {c+a+b≤n⇒a+b≤n{‖ i ‖ᶠ} m}
...  | x | w =
  begin
    ‖ A≢⋆ ‖ʰᵢₜ ⊔ ‖ x ‖ʰᶠ
      ≤⟨ ⊔-monoʳ-≤ _ w ⟩
    ‖ A≢⋆ ‖ʰᵢₜ ⊔ (‖ i ‖ʰᶠ ⊔ ‖ d ‖ʰ)
      ≡⟨ sym (⊔-assoc ‖ A≢⋆ ‖ʰᵢₜ ‖ i ‖ʰᶠ ‖ d ‖ʰ)  ⟩
    (‖ A≢⋆ ‖ʰᵢₜ ⊔ ‖ i ‖ʰᶠ) ⊔ ‖ d ‖ʰ
  ∎
compose-normal-form-height (final c) d {suc n} {s≤s m} = compose-final-normal-height c d {n} {m}

compose-middle-final-height c (injSeq {B = B} iB d) {n} {m} =
  begin
    ‖ B ‖ʰₜ ⊔ ‖ compose-middle-internal c d {n} {a+1+c+b≤n⇒a+b≤n{‖ c ‖ₘ}{‖ d ‖ₘ}{2 * ‖ B ‖ₜ} m} ‖ʰₘ
      ≤⟨ ⊔-monoʳ-≤ ‖ B ‖ʰₜ (compose-middle-height c d {n} {a+1+c+b≤n⇒a+b≤n{‖ c ‖ₘ}{‖ d ‖ₘ}{2 * ‖ B ‖ₜ} m} ) ⟩
    ‖ B ‖ʰₜ ⊔ (‖ c ‖ʰₘ ⊔ ‖ d ‖ʰₘ)
      ≡⟨ sym (⊔-assoc ‖ B ‖ʰₜ ‖ c ‖ʰₘ ‖ d ‖ʰₘ) ⟩
    (‖ B ‖ʰₜ ⊔ ‖ c ‖ʰₘ) ⊔ ‖ d ‖ʰₘ
      ≡⟨ cong₂ (_⊔_) (⊔-comm ‖ B ‖ʰₜ ‖ c ‖ʰₘ) (refl{x = ‖ d ‖ʰₘ}) ⟩
    (‖ c ‖ʰₘ ⊔ ‖ B ‖ʰₜ) ⊔ ‖ d ‖ʰₘ
      ≡⟨ ⊔-assoc ‖ c ‖ʰₘ _ _ ⟩
    ‖ c ‖ʰₘ ⊔ (‖ B ‖ʰₜ ⊔ ‖ d ‖ʰₘ)
  ∎
compose-middle-final-height c (middle d) {n} {m} =
  compose-middle-height c d {n} {a+1+b≤n⇒a+b≤n{‖ c ‖ₘ} m}

{- The height of compose-final-normal-internal -}
compose-final-normal-height c id⋆ {n} {m} = m≤m⊔n _ _
compose-final-normal-height (injSeq B≢⋆ g) (prjSeq A≢⋆ i) {n} {m}
  with compose-middle-final-height (make-middle-coercion B≢⋆ A≢⋆) i {n} {make-coercion+i≤n g i n m}
... | fst
  with compose-middle-final-height g i⨟c {n} {injPrj≤n g i n m m'}
    where
      c   = make-middle-coercion B≢⋆ A≢⋆
      m'  = make-coercion+i≤n g i n m
      i⨟c = compose-middle-final-internal c i {n} {m'}
... | snd =
  begin
    ‖ compose-middle-final-internal g i⨟c {n} {injPrj≤n g i n m m'} ‖ʰᶠ
      ≤⟨ snd ⟩
    ‖ g ‖ʰₘ ⊔ ‖ compose-middle-final-internal c i {n} {m'} ‖ʰᶠ
      ≤⟨ ⊔-monoʳ-≤ _ fst ⟩
    ‖ g ‖ʰₘ ⊔ (‖ c ‖ʰₘ ⊔ ‖ i ‖ʰᶠ)
      ≤⟨ ⊔-monoʳ-≤ ‖ g ‖ʰₘ (⊔-monoˡ-≤ _ (mk-fcoercion-height B≢⋆ A≢⋆)) ⟩
    ‖ g ‖ʰₘ ⊔ ((‖ B≢⋆ ‖ʰᵢₜ ⊔ ‖ A≢⋆ ‖ʰᵢₜ) ⊔ ‖ i ‖ʰᶠ)
      ≤⟨ ⊔-monoʳ-≤ ‖ g ‖ʰₘ (≤-reflexive (⊔-assoc ‖ B≢⋆ ‖ʰᵢₜ ‖ A≢⋆ ‖ʰᵢₜ _)) ⟩
    ‖ g ‖ʰₘ ⊔ (‖ B≢⋆ ‖ʰᵢₜ ⊔ (‖ A≢⋆ ‖ʰᵢₜ ⊔ ‖ i ‖ʰᶠ))
      ≡⟨ sym (⊔-assoc ‖ g ‖ʰₘ _ _) ⟩
    (‖ g ‖ʰₘ ⊔ ‖ B≢⋆ ‖ʰᵢₜ) ⊔ (‖ A≢⋆ ‖ʰᵢₜ ⊔ ‖ i ‖ʰᶠ)
      ≤⟨ ⊔-monoˡ-≤ _ (≤-reflexive (⊔-comm ‖ g ‖ʰₘ _)) ⟩
    ‖ B≢⋆ ‖ʰᵢₜ ⊔ ‖ g ‖ʰₘ ⊔ (‖ A≢⋆ ‖ʰᵢₜ ⊔ ‖ i ‖ʰᶠ)
  ∎
  where
    c   = make-middle-coercion B≢⋆ A≢⋆
    m'  = make-coercion+i≤n g i n m
    i⨟c = compose-middle-final-internal c i {n} {m'}
compose-final-normal-height (injSeq A x) (final (injSeq B fail)) {suc n} {s≤s m} =
  begin
   1
      ≤⟨ n≤m⊔n _ 1 ⟩
    ((‖ A ‖ʰᵢₜ ⊔ ‖ x ‖ʰₘ) ⊔ ‖ B ‖ʰᵢₜ) ⊔ 1
      ≡⟨ ⊔-assoc (‖ A ‖ʰᵢₜ ⊔ ‖ x ‖ʰₘ) ‖ B ‖ʰᵢₜ 1 ⟩
    ‖ A ‖ʰᵢₜ ⊔ ‖ x ‖ʰₘ ⊔ (‖ B ‖ʰᵢₜ ⊔ 1)
  ∎
compose-final-normal-height (injSeq _ _) (final (injSeq () (id _)))
compose-final-normal-height (injSeq _ _) (final (middle (id ())))
compose-final-normal-height (injSeq _ _) (final (middle fail)) = n≤m⊔n _ 1
compose-final-normal-height (middle g) (final i) {n} {m} =
  compose-middle-final-height g i {n} {1+a+1+b≤n⇒a+b≤n m}
compose-final-normal-height (middle (id ())) (prjSeq _ _)
compose-final-normal-height (middle fail) (prjSeq A c) = m≤m⊔n 1 (‖ A ‖ʰᵢₜ ⊔ ‖ c ‖ʰᶠ)

compose-middle-height (id _) d = n≤m⊔n 1 ‖ d ‖ʰₘ
compose-middle-height fail d = m≤m⊔n 1 ‖ d ‖ʰₘ
compose-middle-height (fun _ _) (id _) = m≤m⊔n _ 1
compose-middle-height (fun c d) (fun c' d') {n} {m}
  with compose-normal-form-height c' c {n} {1+a+c+1+b+d≤n⇒b+a≤n{‖ c ‖} m}
     | compose-normal-form-height d d' {n} {1+c+a+1+d+b≤n⇒a+b≤n{‖ d ‖} m}
...  | l | r =
  begin
    suc
    (‖ compose-normal-form c' c {n} {1+a+c+1+b+d≤n⇒b+a≤n{‖ c ‖} m} ‖ʰ ⊔
     ‖ compose-normal-form d d' {n} {1+c+a+1+d+b≤n⇒a+b≤n{‖ d ‖} m} ‖ʰ)
      ≤⟨ +-monoʳ-≤ 1 ((⊔-mono-≤ l r)) ⟩
    suc (‖ c' ‖ʰ ⊔ ‖ c ‖ʰ ⊔ (‖ d ‖ʰ ⊔ ‖ d' ‖ʰ))
      ≤⟨ 1+b⊔a⊔c⊔d≤1+a⊔c⊔b⊔d{‖ c ‖ʰ}{‖ c' ‖ʰ} ⟩
    suc (‖ c ‖ʰ ⊔ ‖ d ‖ʰ ⊔ (‖ c' ‖ʰ ⊔ ‖ d' ‖ʰ))
  ∎
compose-middle-height c@(fun _ _) fail = m≤m+n 1 _
compose-middle-height (prod _ _) (id _) = m≤m⊔n _ 1
compose-middle-height (prod c d) (prod c' d') {n} {m}
  with compose-normal-form-height c c' {n} {1+a+c+1+b+d≤n⇒a+b≤n{‖ c ‖} m}
     | compose-normal-form-height d d' {n} {1+c+a+1+d+b≤n⇒a+b≤n{‖ d ‖} m}
...  | l | r =
  begin
    suc
    (‖ compose-normal-form c c' {n} {1+a+c+1+b+d≤n⇒a+b≤n{‖ c ‖} m} ‖ʰ ⊔
     ‖ compose-normal-form d d' {n} {1+c+a+1+d+b≤n⇒a+b≤n{‖ d ‖} m} ‖ʰ)
      ≤⟨ +-monoʳ-≤ 1 ((⊔-mono-≤ l r)) ⟩
    suc (‖ c ‖ʰ ⊔ ‖ c' ‖ʰ ⊔ (‖ d ‖ʰ ⊔ ‖ d' ‖ʰ))
      ≤⟨ 1+a⊔b⊔c⊔d≤1+a⊔c⊔b⊔d{‖ c ‖ʰ}{‖ c' ‖ʰ} ⟩
    suc (‖ c ‖ʰ ⊔ ‖ d ‖ʰ ⊔ (‖ c' ‖ʰ ⊔ ‖ d' ‖ʰ))
  ∎
compose-middle-height (prod _ _) fail = m≤m+n 1 _
compose-middle-height (Ref _ _) (id _) = m≤m⊔n _ 1
compose-middle-height (Ref A _) (Ref B _)
  with ∼-decidable A B
... | yes p = s≤s (A⊓B≤A⊔B p)
... | no _ = m≤m+n 1 _
compose-middle-height (Ref _ _) fail = m≤m+n 1 _
