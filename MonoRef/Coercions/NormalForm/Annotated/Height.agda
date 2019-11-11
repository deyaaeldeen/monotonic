module MonoRef.Coercions.NormalForm.Annotated.Height where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ ; suc ; _+_ ; _*_ ; _≤_ ; _⊔_ ; z≤n ; s≤s)
open import Data.Nat.Properties
open ≤-Reasoning
open import Relation.Binary.PropositionalEquality using (refl ; sym)
open import Relation.Nullary using (yes ; no)

open import MonoRef.Coercions.NormalForm.Annotated.Compose
open import MonoRef.Coercions.NormalForm.Annotated.Height.Lemmas
open import MonoRef.Coercions.NormalForm.Annotated.Make
open import MonoRef.Coercions.NormalForm.Annotated.Size
open import MonoRef.Coercions.NormalForm.Annotated.Syntax
open import MonoRef.Coercions.NormalForm.InEqReasoning
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


compose-middle-height : ∀ {A B C}
  → (mc : MiddleCoercion A B) → (md : MiddleCoercion B C)
  → {n : ℕ} {m : ‖ mc ‖ₘ + ‖ md ‖ₘ ≤ n }
  → ‖ compose-middle-internal mc md {n} {m} ‖ʰₘ ≤ ‖ mc ‖ʰₘ ⊔ ‖ md ‖ʰₘ

compose-final-height : ∀ {A B C}
  → (fc : FinalCoercion A B) → (nd : NormalFormCoercion B C)
  → {n : ℕ} {m : ‖ fc ‖ᶠ + ‖ nd ‖ ≤ n }
  → ‖ compose-final-internal fc nd {n} {m} ‖ʰ ≤ ‖ fc ‖ʰᶠ ⊔ ‖ nd ‖ʰ

compose-normal-form-height : ∀ {A B C}
  → (nc : NormalFormCoercion A B) → (nd : NormalFormCoercion B C)
  → {n : ℕ} {m : ‖ nc ‖ + ‖ nd ‖ ≤ n }
  → ‖ compose-normal-form nc nd {n} {m} ‖ʰ ≤ ‖ nc ‖ʰ ⊔ ‖ nd ‖ʰ
compose-normal-form-height (prjSeq A≢⋆ i) d {suc n} {s≤s m}
  with compose-final-internal i d {n} {1+c+a+b≤n⇒a+b≤n{‖ i ‖ᶠ} m}
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

{- The height of compose-final-internal -}
compose-final-height c d {0} {m} = ⊥-elim (¬size-two-nf&fcoercions≤0 c d m)
compose-final-height (injSeq B≢⋆ g) (prjSeq A≢⋆ i) {suc n} {s≤s m}
  with compose-final-height (make-final-coercion B≢⋆ A≢⋆) (final i) {n} {m'}
    where m' = make-coercion+i≤n g i n m
... | fst
  with compose-final-height (middle g) i⨟c {n} {injPrj≤n g i n m m'}
    where
      c   = make-final-coercion B≢⋆ A≢⋆
      m'  = make-coercion+i≤n g i n m
      i⨟c = compose-final-internal c (final i) {n} {m'}
... | snd =
  begin
    ‖ compose-final-internal (middle g) i⨟c {n} {injPrj≤n g i n m m'} ‖ʰ
      ≤⟨ snd ⟩
    ‖ g ‖ʰₘ ⊔ ‖ compose-final-internal c (final i) {n} {m'} ‖ʰ
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
    i⨟c = compose-final-internal c (final i) {n} {m'}
compose-final-height (injSeq A x) (final (injSeq B (fail _ _))) {suc n} {s≤s m} =
  begin
   1
      ≤⟨ n≤m⊔n _ 1 ⟩
    ((‖ A ‖ʰᵢₜ ⊔ ‖ x ‖ʰₘ) ⊔ ‖ B ‖ʰᵢₜ) ⊔ 1
      ≡⟨ ⊔-assoc (‖ A ‖ʰᵢₜ ⊔ ‖ x ‖ʰₘ) ‖ B ‖ʰᵢₜ 1 ⟩
    ‖ A ‖ʰᵢₜ ⊔ ‖ x ‖ʰₘ ⊔ (‖ B ‖ʰᵢₜ ⊔ 1)
  ∎
compose-final-height (injSeq _ _) (final (injSeq B≢⋆ (id _))) {suc _} {s≤s _} = ⊥-elim (Injectable⋆⇒⊥ B≢⋆)
compose-final-height (injSeq _ _) (final (middle (id _))) {suc _} {s≤s _} = m≤m⊔n _ 1
compose-final-height (injSeq _ _) (final (middle (fail _ _))) {suc _} {s≤s _} = n≤m⊔n _ 1
compose-final-height (middle x) (final (middle y)) {suc n} {s≤s m} = compose-middle-height x y {n} {a+2+b≤n⇒a+b≤n m}
compose-final-height (middle x) (final (injSeq B y)) {suc n} {s≤s m} =
  begin
    ‖ B ‖ʰᵢₜ ⊔ ‖ compose-middle-internal x y {n} {a+3+c+b≤n⇒a+b≤n m} ‖ʰₘ
      ≤⟨ ⊔-monoʳ-≤ ‖ B ‖ʰᵢₜ (compose-middle-height x y {n} {a+3+c+b≤n⇒a+b≤n m}) ⟩
    ‖ B ‖ʰᵢₜ ⊔ (‖ x ‖ʰₘ ⊔ ‖ y ‖ʰₘ)
      ≡⟨ sym (⊔-assoc ‖ B ‖ʰᵢₜ ‖ x ‖ʰₘ _)  ⟩
    (‖ B ‖ʰᵢₜ ⊔ ‖ x ‖ʰₘ) ⊔ ‖ y ‖ʰₘ
      ≤⟨ ⊔-monoˡ-≤ _ (≤-reflexive (⊔-comm ‖ B ‖ʰᵢₜ _)) ⟩
    (‖ x ‖ʰₘ ⊔ ‖ B ‖ʰᵢₜ) ⊔ ‖ y ‖ʰₘ
      ≡⟨ ⊔-assoc ‖ x ‖ʰₘ _ _ ⟩
    ‖ x ‖ʰₘ ⊔ (‖ B ‖ʰᵢₜ ⊔ ‖ y ‖ʰₘ)
  ∎
compose-final-height (middle (id _)) (prjSeq _ _) {suc _} {s≤s _} = n≤m⊔n 1 _
compose-final-height (middle (fail _ _)) (prjSeq A c) {suc _} {s≤s _}
  with get-target-type/final c | get-target-type/final-wt c
... | _ | refl = m≤m⊔n 1 (‖ A ‖ʰᵢₜ ⊔ ‖ c ‖ʰᶠ)

compose-middle-height c d {0} {m} = ⊥-elim (¬size-two-mcoercions≤0 c d m)
compose-middle-height (id _) d {suc _} {s≤s _} = n≤m⊔n 1 ‖ d ‖ʰₘ
compose-middle-height (fail _ _) d {suc _}
  with get-target-type/middle d | get-target-type/middle-wt d
... | _ | refl = m≤m⊔n 1 ‖ d ‖ʰₘ
compose-middle-height (fun _ _) (id _) {suc _} = m≤m⊔n _ 1
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
compose-middle-height c@(fun _ _) (fail _ _) {suc _}
  with get-source-type/middle c | get-source-type/middle-wt c
... | _ | refl = m≤m+n 1 _
compose-middle-height (prod _ _) (id _) {suc _} = m≤m⊔n _ 1
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
compose-middle-height c@(prod _ _) (fail _ _) {suc _}
  with get-source-type/middle c | get-source-type/middle-wt c
... | _ | refl = m≤m+n 1 _
compose-middle-height (Ref _ _ _ _) (id _) {suc _} = m≤m⊔n _ 1
compose-middle-height (Ref _ _ A _) (Ref _ _ B _) {suc _} {s≤s _}
  with ∼-decidable A B
... | yes p = s≤s (A⊓B≤A⊔B p)
... | no _ = m≤m+n 1 _
compose-middle-height (Ref _ _ _ _) (fail _ _) {suc _} = m≤m+n 1 _
