module MonoRef.Coercions.NormalForm.Faithful.Height where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ ; suc ; _+_ ; _*_ ; _≤_ ; _⊔_ ; z≤n ; s≤s)
open import Data.Nat.Properties
open ≤-Reasoning
open import Relation.Binary.PropositionalEquality using (sym)
open import Relation.Nullary using (yes ; no)

open import MonoRef.Coercions.NormalForm.Faithful.Compose
open import MonoRef.Coercions.NormalForm.Faithful.Height.Lemmas
open import MonoRef.Coercions.NormalForm.Faithful.Make
open import MonoRef.Coercions.NormalForm.Faithful.Size
open import MonoRef.Coercions.NormalForm.Faithful.Syntax
open import MonoRef.Coercions.NormalForm.InEqReasoning
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


compose-final-height : ∀ {A B C}
  → (fc : FinalCoercion A B) → (nd : NormalFormCoercion B C)
  → {n : ℕ} {m : ‖ fc ‖ᶠ + ‖ nd ‖ ≤ n }
  → ‖ compose-final fc nd {n} {m} ‖ʰ ≤ ‖ fc ‖ʰᶠ ⊔ ‖ nd ‖ʰ

compose-normal-form-height : ∀ {A B C}
  → (nc : NormalFormCoercion A B) → (nd : NormalFormCoercion B C)
  → {n : ℕ} {m : ‖ nc ‖ + ‖ nd ‖ ≤ n }
  → ‖ compose-normal-form nc nd {n} {m} ‖ʰ ≤ ‖ nc ‖ʰ ⊔ ‖ nd ‖ʰ
compose-normal-form-height (prjSeq A≢⋆ i) d {suc n} {s≤s m}
  with compose-final i d {n} {1+c+a+b≤n⇒a+b≤n{‖ i ‖ᶠ} m}
     | compose-final-height i d {n} {1+c+a+b≤n⇒a+b≤n{‖ i ‖ᶠ} m}
...  | prjSeq _ _ | _ = ⊥-elim (Injectable⋆⇒⊥ A≢⋆)
...  | final x    | w =
  begin
    ‖ A≢⋆ ‖ʰᵢₜ ⊔ ‖ x ‖ʰᶠ
      ≤⟨ ⊔-monoʳ-≤ _ w ⟩
    ‖ A≢⋆ ‖ʰᵢₜ ⊔ (‖ i ‖ʰᶠ ⊔ ‖ d ‖ʰ)
      ≡⟨ sym (⊔-assoc ‖ A≢⋆ ‖ʰᵢₜ ‖ i ‖ʰᶠ ‖ d ‖ʰ)  ⟩
    (‖ A≢⋆ ‖ʰᵢₜ ⊔ ‖ i ‖ʰᶠ) ⊔ ‖ d ‖ʰ
  ∎
compose-normal-form-height (final c) d {suc n} {s≤s m} = compose-final-height c d {n} {m}

{- The height of compose-final -}
compose-final-height c d {0} {m} = ⊥-elim (¬size-two-nf&fcoercions≤0 c d m)
compose-final-height fail (prjSeq {A = A} iA x) {suc _} = m≤m⊔n 1 (‖ A ‖ʰₜ ⊔ ‖ x ‖ʰᶠ)
compose-final-height fail (final fail) {suc _} = s≤s z≤n
compose-final-height fail (final (injSeq {B = B} iB x)) {suc _} = m≤m⊔n 1 (‖ B ‖ʰₜ ⊔ ‖ x ‖ʰₘ)
compose-final-height fail (final (middle x)) {suc _} = m≤m⊔n 1 ‖ x ‖ʰₘ
compose-final-height (injSeq B≢⋆ g) (prjSeq A≢⋆ i) {suc n} {s≤s m}
  with compose-final-height (make-final-coercion B≢⋆ A≢⋆) (final i) {n} {m'}
    where m' = make-coercion+i≤n g i n m
... | fst
  with compose-final-height (middle g) i⨟c {n} {injPrj≤n g i n m m'}
    where
      c   = make-final-coercion B≢⋆ A≢⋆
      m'  = make-coercion+i≤n g i n m
      i⨟c = compose-final c (final i) {n} {m'}
... | snd =
  begin
    ‖ compose-final (middle g) i⨟c {n} {injPrj≤n g i n m m'} ‖ʰ
      ≤⟨ snd ⟩
    ‖ g ‖ʰₘ ⊔ ‖ compose-final c (final i) {n} {m'} ‖ʰ
      ≤⟨ ⊔-monoʳ-≤ _ fst ⟩
    ‖ g ‖ʰₘ ⊔ (‖ c ‖ʰᶠ ⊔ ‖ i ‖ʰᶠ)
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
    c   = make-final-coercion B≢⋆ A≢⋆
    m'  = make-coercion+i≤n g i n m
    i⨟c = compose-final c (final i) {n} {m'}
compose-final-height (injSeq iB x) (final x₁) {suc n} {s≤s m} = {!!}
compose-final-height (middle x) (prjSeq iA x₁) {suc n} {s≤s m} = {!!}
compose-final-height (middle x) (final x₁) {suc n} = {!!}

compose-middle-height : ∀ {A B C}
  → (mc : MiddleCoercion A B) → (md : MiddleCoercion B C)
  → {n : ℕ} {m : ‖ mc ‖ₘ + ‖ md ‖ₘ ≤ n }
  → ‖ compose-middle mc md {n} {m} ‖ʰₘ ≤ ‖ mc ‖ʰₘ ⊔ ‖ md ‖ʰₘ
compose-middle-height c d {0} {m} = ⊥-elim (¬size-two-mcoercions≤0 c d m)
compose-middle-height id d {suc _} {s≤s _} = n≤m⊔n 1 ‖ d ‖ʰₘ
compose-middle-height fail d {suc _} = m≤m⊔n 1 ‖ d ‖ʰₘ
compose-middle-height (fun _ _) id {suc _} = m≤m⊔n _ 1
compose-middle-height (fun c d) (fun c' d') {suc n} {s≤s m}
  with compose-normal-form-height c' c {n} {a+c+1+b+d≤n⇒b+a≤n{‖ c ‖} m}
     | compose-normal-form-height d d' {n} {c+a+1+d+b≤n⇒a+b≤n{‖ d ‖} m}
...  | l | r =
  begin
    suc
    (‖ compose-normal-form c' c {n} {a+c+1+b+d≤n⇒b+a≤n{‖ c ‖} m} ‖ʰ ⊔
     ‖ compose-normal-form d d' {n} {c+a+1+d+b≤n⇒a+b≤n{‖ d ‖} m} ‖ʰ)
      ≤⟨ +-monoʳ-≤ 1 ((⊔-mono-≤ l r)) ⟩
    suc (‖ c' ‖ʰ ⊔ ‖ c ‖ʰ ⊔ (‖ d ‖ʰ ⊔ ‖ d' ‖ʰ))
      ≤⟨ 1+b⊔a⊔c⊔d≤1+a⊔c⊔b⊔d{‖ c ‖ʰ}{‖ c' ‖ʰ} ⟩
    suc (‖ c ‖ʰ ⊔ ‖ d ‖ʰ ⊔ (‖ c' ‖ʰ ⊔ ‖ d' ‖ʰ))
  ∎
compose-middle-height (fun _ _) fail {suc _} = m≤m+n 1 _
compose-middle-height (prod _ _) id {suc _} = m≤m⊔n _ 1
compose-middle-height (prod c d) (prod c' d') {suc n} {s≤s m}
  with compose-normal-form-height c c' {n} {a+c+1+b+d≤n⇒a+b≤n{‖ c ‖} m}
     | compose-normal-form-height d d' {n} {c+a+1+d+b≤n⇒a+b≤n{‖ d ‖} m}
...  | l | r =
  begin
    suc
    (‖ compose-normal-form c c' {n} {a+c+1+b+d≤n⇒a+b≤n{‖ c ‖} m} ‖ʰ ⊔
     ‖ compose-normal-form d d' {n} {c+a+1+d+b≤n⇒a+b≤n{‖ d ‖} m} ‖ʰ)
      ≤⟨ +-monoʳ-≤ 1 ((⊔-mono-≤ l r)) ⟩
    suc (‖ c ‖ʰ ⊔ ‖ c' ‖ʰ ⊔ (‖ d ‖ʰ ⊔ ‖ d' ‖ʰ))
      ≤⟨ 1+a⊔b⊔c⊔d≤1+a⊔c⊔b⊔d{‖ c ‖ʰ}{‖ c' ‖ʰ} ⟩
    suc (‖ c ‖ʰ ⊔ ‖ d ‖ʰ ⊔ (‖ c' ‖ʰ ⊔ ‖ d' ‖ʰ))
  ∎
compose-middle-height (prod _ _) fail {suc _} = m≤m+n 1 _
compose-middle-height (Ref _ _) id {suc _} = m≤m⊔n _ 1
compose-middle-height (Ref A _) (Ref B _) {suc _} {s≤s _}
  with ∼-decidable A B
... | yes p = s≤s (A⊓B≤A⊔B p)
... | no _ = m≤m+n 1 _
compose-middle-height (Ref _ _) fail {suc _} = m≤m+n 1 _
