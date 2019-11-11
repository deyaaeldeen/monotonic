module MonoRef.Coercions.NormalForm.Annotated.Compose where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ ; suc ; _+_ ; _*_ ; _≤_ ; s≤s ; z≤n)
open import Data.Nat.Properties
open ≤-Reasoning
open import Relation.Binary.PropositionalEquality using (refl ; sym ; cong₂)
open import Relation.Nullary using (yes ; no)

open import MonoRef.Coercions.NormalForm.InEqReasoning
open import MonoRef.Coercions.NormalForm.Annotated.Make
open import MonoRef.Coercions.NormalForm.Annotated.Size
open import MonoRef.Coercions.NormalForm.Annotated.Syntax
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


compose-middle-internal : ∀ {A B C}
  → (mc : MiddleCoercion A B) → (md : MiddleCoercion B C)
  → {n : ℕ} → {m : ‖ mc ‖ₘ + ‖ md ‖ₘ ≤ n }
  → MiddleCoercion A C

compose-final-internal : ∀ {A B C}
  → (fc : FinalCoercion A B) → (nd : NormalFormCoercion B C)
  → {n : ℕ} → {m : ‖ fc ‖ᶠ + ‖ nd ‖ ≤ n }
  → NormalFormCoercion A C

compose-normal-form : ∀ {A B C}
  → (nc : NormalFormCoercion A B) → (nd : NormalFormCoercion B C)
  → {n : ℕ} → {m : ‖ nc ‖ + ‖ nd ‖ ≤ n }
  → NormalFormCoercion A C

make-coercion+i≤n : ∀ {A B C D} {B≢⋆ : Injectable B} {C≢⋆ : Injectable C}
  → (g : MiddleCoercion A B) → (i : FinalCoercion C D)
  → (n : ℕ) → (m : 2 + (‖ B≢⋆ ‖ᵢₜ + (‖ B≢⋆ ‖ᵢₜ + 0) + ‖ g ‖ₘ + (3 + (‖ C≢⋆ ‖ᵢₜ + (‖ C≢⋆ ‖ᵢₜ + 0) + ‖ i ‖ᶠ))) ≤ n)
  → ‖ make-final-coercion B≢⋆ C≢⋆ ‖ᶠ + suc ‖ i ‖ᶠ ≤ n

injPrj≤n : ∀ {A B C D} {B≢⋆ : Injectable B} {C≢⋆ : Injectable C}
  → (g : MiddleCoercion A B) → (i : FinalCoercion C D)
  → (n : ℕ) → (m : 2 + (‖ B ‖ₜ + (‖ B ‖ₜ + 0) + ‖ g ‖ₘ + (3 + (‖ C ‖ₜ + (‖ C ‖ₜ + 0) + ‖ i ‖ᶠ))) ≤ n)
  → (m' : ‖ make-final-coercion B≢⋆ C≢⋆ ‖ᶠ + suc ‖ i ‖ᶠ ≤ n)
  → 1 + (‖ g ‖ₘ + ‖ compose-final-internal (make-final-coercion B≢⋆ C≢⋆) (final i) {n} {m'} ‖) ≤ n


{- Composing middle coercions -}

compose-middle-internal c d {0} {m} = ⊥-elim (¬size-two-mcoercions≤0 c d m)

compose-middle-internal (fun c d)  (fun c' d')  {suc n} {s≤s m}
  with compose-normal-form c' c {n} {a+c+1+b+d≤n⇒b+a≤n{‖ c ‖} m}
     | compose-normal-form d d' {n} {c+a+1+d+b≤n⇒a+b≤n{‖ d ‖} m}
...  | c'⨟c | d⨟d' = fun c'⨟c d⨟d'

compose-middle-internal (prod c d) (prod c' d') {suc n} {s≤s m}
  with compose-normal-form c c' {n} {a+c+1+b+d≤n⇒a+b≤n{‖ c ‖} m}
     | compose-normal-form d d' {n} {c+a+1+d+b≤n⇒a+b≤n{‖ d ‖} m}
...  | c⨟c' | d⨟d' = prod c⨟c' d⨟d'

compose-middle-internal (Ref A B D x) (Ref .B C E y) {suc n}
  with ∼-decidable D E
... | yes p = Ref A C (⊓ p) (⊑-trans (⊓⟹⊑ᵣ p) y)
... | no _ = fail (Ref A) (Ref C)

{- id cases -}

compose-middle-internal (id _)          c      {suc n} = c
compose-middle-internal c@(fun _ _)     (id _) {suc n} = c
compose-middle-internal c@(Ref _ _ _ _) (id _) {suc n} = c
compose-middle-internal c@(prod _ _)    (id _) {suc n} = c

compose-middle-internal (fail A _)    d          {suc n}
  with get-target-type/middle d | get-target-type/middle-wt d
... | T | refl = (fail A T)
compose-middle-internal c@(fun _ _)   (fail _ B) {suc n}
    with get-source-type/middle c | get-source-type/middle-wt c
... | T | refl = fail T B
compose-middle-internal (Ref A _ _ _) (fail _ B) {suc n} = fail (Ref A) B
compose-middle-internal c@(prod _ _)  (fail _ B) {suc n}
    with get-source-type/middle c | get-source-type/middle-wt c
... | T | refl = fail T B


{- Composing final coercions -}

compose-final-internal c d {0} {m} = ⊥-elim (¬size-two-nf&fcoercions≤0 c d m)

compose-final-internal (injSeq B≢⋆ g) (prjSeq A≢⋆ i) {suc n} {s≤s m} =
  compose-final-internal (middle g) c⨟i {n} {injPrj≤n g i n m m'}
  where
    c   = make-final-coercion B≢⋆ A≢⋆
    m'  = make-coercion+i≤n g i n m
    c⨟i = compose-final-internal c (final i) {n} {m'}

compose-final-internal (middle g) (final (injSeq B≢⋆ g')) {suc n} {s≤s m} =
  final (injSeq B≢⋆ (compose-middle-internal g g' {n} {a+3+c+b≤n⇒a+b≤n m}))

compose-final-internal (middle g) (final (middle g')) {suc n} {s≤s m} =
  final (middle (compose-middle-internal g g' {n} {a+2+b≤n⇒a+b≤n m}))

{- id cases -}

-- this case forces me to return a normal form coercion because this is id on ⋆
compose-final-internal (middle (id _)) i@(prjSeq _ _) {suc _} = i
compose-final-internal (middle (fail A _)) (prjSeq _ c) {suc _}
  with get-target-type/final c | get-target-type/final-wt c
... | T | refl = final (middle (fail A T))
compose-final-internal i@(injSeq _ _) (final (middle (id _))) {suc _} = final i
compose-final-internal (injSeq _ _) (final (middle (fail _ _))) {suc _} = final (middle (fail _ _))

{- Failure cases -}

compose-final-internal (injSeq _ _) (final (injSeq _ (fail _ _))) {suc _} = final (middle (fail _ _))
compose-final-internal (injSeq _ _) (final (injSeq () (id _))) {suc _}


{- Composing normal form coercions -}

compose-normal-form c d {0} {m} = ⊥-elim (¬size-two-nfcoercions≤0 c d m)

compose-normal-form (prjSeq A≢⋆ i) c {suc n} {s≤s m}
  with compose-final-internal i c {n} {1+c+a+b≤n⇒a+b≤n{‖ i ‖ᶠ} m}
compose-normal-form (prjSeq () _) _ | prjSeq _ _
...  | final i⨟c = prjSeq A≢⋆ i⨟c
compose-normal-form (final c) d {suc n} {s≤s m} = compose-final-internal c d {n} {m}


{-
  The following lemmas are needed to reason about the termination of compose
-}

mk-nfcoercion-size : ∀ A B
  → ‖ (make-normal-form-coercion A B) ‖ ≤ 3 + (2 * (‖ A ‖ₜ + ‖ B ‖ₜ))
mk-nfcoercion-size A B with ⌣-decidable A B
... | no _            = m≤m+n 3 _
... | yes ⌣-ℕ-refl    = s≤s (s≤s (s≤s z≤n))
... | yes ⌣-Unit-refl = s≤s (s≤s (s≤s z≤n))
mk-nfcoercion-size .⋆ B | yes ⌣-⋆L
  with T≡⋆? B
...  | yes refl = s≤s (s≤s (s≤s z≤n))
...  | no _     = 3+2*c+2≤4+c+1+c+0
mk-nfcoercion-size A .⋆ | yes ⌣-⋆R
  with T≡⋆? A
...  | yes refl = s≤s (s≤s (s≤s z≤n))
...  | no _     = 4+2*c+1≤3+c+1+c+1{‖ A ‖ₜ}
mk-nfcoercion-size (A ⇒ B) (A' ⇒ B') | yes ⌣-⇒
  with make-normal-form-coercion A' A | mk-nfcoercion-size A' A
     | make-normal-form-coercion B B' | mk-nfcoercion-size B B'
...  | c | l | d | r =
  begin
    3 + (‖ c ‖ + ‖ d ‖)
      ≤⟨ +-monoʳ-≤ 3 (+-mono-≤ l r) ⟩
    6 + (‖ A' ‖ₜ + ‖ A ‖ₜ + (‖ A' ‖ₜ + ‖ A ‖ₜ + 0)
         + (3 + (‖ B ‖ₜ + ‖ B' ‖ₜ + (‖ B ‖ₜ + ‖ B' ‖ₜ + 0))))
      ≤⟨ 6+b+a+b+a+0+3+c+d+c+d+0≤6+a+c+3+b+d+3+a+c+3+b+d+0{‖ A ‖ₜ} ⟩
    6 + (‖ A ‖ₜ + ‖ B ‖ₜ + (3 + (‖ A' ‖ₜ + ‖ B' ‖ₜ))
         + (3 + (‖ A ‖ₜ + ‖ B ‖ₜ + (3 + (‖ A' ‖ₜ + ‖ B' ‖ₜ)) + 0)))
  ∎
mk-nfcoercion-size (A `× B) (A' `× B') | yes ⌣-×
  with make-normal-form-coercion A A' | mk-nfcoercion-size A A'
     | make-normal-form-coercion B B' | mk-nfcoercion-size B B'
...  | c | l | d | r =
  begin
    3 + (‖ c ‖ + ‖ d ‖)
      ≤⟨ +-monoʳ-≤ 3 (+-mono-≤ l r) ⟩
    6 + (‖ A ‖ₜ + ‖ A' ‖ₜ + (‖ A ‖ₜ + ‖ A' ‖ₜ + 0) +
            (3 + (‖ B ‖ₜ + ‖ B' ‖ₜ + (‖ B ‖ₜ + ‖ B' ‖ₜ + 0))))
      ≤⟨ 6+a+b+a+b+0+3+c+d+c+d+0≤6+a+c+3+b+d+3+a+c+3+b+d+0{‖ A ‖ₜ} ⟩
    (6 + (‖ A ‖ₜ + ‖ B ‖ₜ + (3 + (‖ A' ‖ₜ + ‖ B' ‖ₜ)) +
            (3 + (‖ A ‖ₜ + ‖ B ‖ₜ + (3 + (‖ A' ‖ₜ + ‖ B' ‖ₜ)) + 0))))
  ∎
mk-nfcoercion-size .(Ref _) .(Ref _) | yes ⌣-ref = 3+b≤4+a+1+b+1+a+1+b+0

mk-fcoercion-size : ∀ {A B} → (A≢⋆ : Injectable A) → (B≢⋆ : Injectable B)
  → ‖ (make-final-coercion A≢⋆ B≢⋆) ‖ᶠ ≤ 3 + (2 * (‖ A≢⋆ ‖ᵢₜ + ‖ B≢⋆ ‖ᵢₜ))
mk-fcoercion-size A B with ⌣-decidableᵢ A B
... | no _            = s≤s (s≤s z≤n)
... | yes ⌣-ℕ-refl    = s≤s (s≤s z≤n)
... | yes ⌣-Unit-refl = s≤s (s≤s z≤n)
mk-fcoercion-size () _ | yes ⌣-⋆L
mk-fcoercion-size _ () | yes ⌣-⋆R
mk-fcoercion-size {A ⇒ B} {A' ⇒ B'} _ _ | yes ⌣-⇒
  with make-normal-form-coercion A' A | mk-nfcoercion-size A' A
     | make-normal-form-coercion B B' | mk-nfcoercion-size B B'
...  | c | l | d | r =
  begin
    2 + (‖ c ‖ + ‖ d ‖)
      ≤⟨ +-monoʳ-≤ 2 (+-mono-≤ l r) ⟩
    5 + (‖ A' ‖ₜ + ‖ A ‖ₜ + (‖ A' ‖ₜ + ‖ A ‖ₜ + 0)
        + (3 + (‖ B ‖ₜ + ‖ B' ‖ₜ + (‖ B ‖ₜ + ‖ B' ‖ₜ + 0))))
      ≤⟨ 5+b+a+b+a+0+3+c+d+c+d+0≤6+a+c+3+b+d+3+a+c+3+b+d+0{‖ A ‖ₜ} ⟩
    6 + (‖ A ‖ₜ + ‖ B ‖ₜ + (3 + (‖ A' ‖ₜ + ‖ B' ‖ₜ))
        + (3 + (‖ A ‖ₜ + ‖ B ‖ₜ + (3 + (‖ A' ‖ₜ + ‖ B' ‖ₜ)) + 0)))
  ∎
mk-fcoercion-size {A `× B} {A' `× B'} _ _ | yes ⌣-×
  with make-normal-form-coercion A A' | mk-nfcoercion-size A A'
     | make-normal-form-coercion B B' | mk-nfcoercion-size B B'
...  | c | l | d | r =
  begin
    2 + (‖ c ‖ + ‖ d ‖)
      ≤⟨ +-monoʳ-≤ 2 (+-mono-≤ l r) ⟩
    5 + (‖ A ‖ₜ + ‖ A' ‖ₜ + (‖ A ‖ₜ + ‖ A' ‖ₜ + 0)
        + (3 + (‖ B ‖ₜ + ‖ B' ‖ₜ + (‖ B ‖ₜ + ‖ B' ‖ₜ + 0))))
      ≤⟨ 5+a+b+a+b+0+3+c+d+c+d+0≤6+a+c+3+b+d+3+a+c+3+b+d+0{‖ A ‖ₜ} ⟩
    6 + (‖ A ‖ₜ + ‖ B ‖ₜ + (3 + (‖ A' ‖ₜ + ‖ B' ‖ₜ))
        + (3 + (‖ A ‖ₜ + ‖ B ‖ₜ + (3 + (‖ A' ‖ₜ + ‖ B' ‖ₜ)) + 0)))
  ∎
mk-fcoercion-size {.(Ref _)} {.(Ref _)} _ _ | yes ⌣-ref = 2+b≤4+a+1+b+1+a+1+b+0

compose-normal-form-size : ∀ {A B C}
  → (nc : NormalFormCoercion A B) → (nd : NormalFormCoercion B C)
  → {n : ℕ} {m : ‖ nc ‖ + ‖ nd ‖ ≤ n }
  → ‖ compose-normal-form nc nd {n} {m} ‖ ≤ ‖ nc ‖ + ‖ nd ‖

compose-final-size : ∀ {A B C}
  → (fc : FinalCoercion A B) → (nd : NormalFormCoercion B C)
  → {n : ℕ} {m : ‖ fc ‖ᶠ + ‖ nd ‖ ≤ n }
  → ‖ compose-final-internal fc nd {n} {m} ‖ ≤ ‖ fc ‖ᶠ + ‖ nd ‖

compose-middle-size : ∀ {A B C}
  → (mc : MiddleCoercion A B) → (md : MiddleCoercion B C)
  → {n : ℕ} {m : ‖ mc ‖ₘ + ‖ md ‖ₘ ≤ n }
  → ‖ compose-middle-internal mc md {n} {m} ‖ₘ ≤ ‖ mc ‖ₘ + ‖ md ‖ₘ

compose-normal-form-size c d {0} {m} = ⊥-elim (¬size-two-nfcoercions≤0 c d m)

compose-normal-form-size (prjSeq A≢⋆ i) d {suc n} {s≤s m}
  with compose-final-internal i d {n} {1+c+a+b≤n⇒a+b≤n{‖ i ‖ᶠ} m}
     | compose-final-size i d {n} {1+c+a+b≤n⇒a+b≤n{‖ i ‖ᶠ} m}
...  | final x    | w =
  begin
    3 + (2 * ‖ A≢⋆ ‖ᵢₜ + ‖ x ‖ᶠ)
      ≤⟨ +-monoʳ-≤ 3 (+-monoʳ-≤ _ (n≤1+n ‖ x ‖ᶠ)) ⟩
    3 + (2 * ‖ A≢⋆ ‖ᵢₜ + suc ‖ x ‖ᶠ)
      ≤⟨ +-monoʳ-≤ 3 (+-monoʳ-≤ _ w) ⟩
    3 + ((2 * ‖ A≢⋆ ‖ᵢₜ) + (‖ i ‖ᶠ + ‖ d ‖))
      ≡⟨ cong₂ (_+_) (refl{x = 3}) (sym (+-assoc (2 * ‖ A≢⋆ ‖ᵢₜ) _ _)) ⟩
    3 + (((2 * ‖ A≢⋆ ‖ᵢₜ) + ‖ i ‖ᶠ) + ‖ d ‖)
  ∎
compose-normal-form-size (prjSeq () _) _ | prjSeq _ _ | _

compose-normal-form-size (final c) d {suc n} {s≤s m} =
  begin
    ‖ compose-final-internal c d {n} {m} ‖ ≤⟨ compose-final-size c d {n} {m} ⟩
    ‖ c ‖ᶠ + ‖ d ‖                 ≤⟨ n≤1+n (‖ c ‖ᶠ + ‖ d ‖) ⟩
    suc (‖ c ‖ᶠ + ‖ d ‖)
  ∎

A⊓B≤A+B : ∀ {A B} → (A∼B : A ∼ B) → ‖ ⊓ A∼B ‖ₜ ≤ ‖ A ‖ₜ + ‖ B ‖ₜ
A⊓B≤A+B ∼-ℕ-refl = s≤s z≤n
A⊓B≤A+B ∼-Unit-refl = s≤s z≤n
A⊓B≤A+B ∼-⋆-refl = s≤s z≤n
A⊓B≤A+B (∼-⋆R _) = m≤m+n _ _
A⊓B≤A+B (∼-⋆L _) = n≤1+n _
A⊓B≤A+B {A ⇒ B} {A' ⇒ B'} (~-⇒ x y)
  with A⊓B≤A+B x | A⊓B≤A+B y
... | l | r =
  begin
    3 + (‖ ⊓ x ‖ₜ + ‖ ⊓ y ‖ₜ)
      ≤⟨ +-monoʳ-≤ 3 (+-mono-≤ l r) ⟩
    3 + (‖ A ‖ₜ + ‖ A' ‖ₜ + (‖ B ‖ₜ + ‖ B' ‖ₜ))
      ≤⟨ 3+a+b+c+d≤3+a+c+3+b+d{‖ A ‖ₜ} ⟩
    3 + (‖ A ‖ₜ + ‖ B ‖ₜ + (3 + (‖ A' ‖ₜ + ‖ B' ‖ₜ)))
  ∎
A⊓B≤A+B {A `× B} {A' `× B'} (~-× x y)
  with A⊓B≤A+B x | A⊓B≤A+B y
... | l | r =
  begin
    3 + (‖ ⊓ x ‖ₜ + ‖ ⊓ y ‖ₜ)
      ≤⟨ +-monoʳ-≤ 3 (+-mono-≤ l r) ⟩
    3 + (‖ A ‖ₜ + ‖ A' ‖ₜ + (‖ B ‖ₜ + ‖ B' ‖ₜ))
      ≤⟨ 3+a+b+c+d≤3+a+c+3+b+d{‖ A ‖ₜ} ⟩
    3 + (‖ A ‖ₜ + ‖ B ‖ₜ + (3 + (‖ A' ‖ₜ + ‖ B' ‖ₜ)))
  ∎
A⊓B≤A+B {Ref A}{Ref B} (~-ref p) with A⊓B≤A+B p
... | w =
  begin
    suc ‖ ⊓ p ‖ₜ           ≤⟨ +-monoʳ-≤ 1 w ⟩
    suc (‖ A ‖ₜ + ‖ B ‖ₜ) ≤⟨ +-monoʳ-≤ 1 (+-monoʳ-≤ _ (n≤1+n _)) ⟩
    suc (‖ A ‖ₜ + suc ‖ B ‖ₜ)
  ∎

compose-middle-size c d {0} {m} = ⊥-elim (¬size-two-mcoercions≤0 c d m)

compose-middle-size (fun c d) (fun c' d') {suc n} {s≤s m}
  with compose-normal-form-size c' c {n} {a+c+1+b+d≤n⇒b+a≤n{‖ c ‖} m}
     | compose-normal-form-size d d' {n} {c+a+1+d+b≤n⇒a+b≤n{‖ d ‖} m}
...  | l | r =
  begin
    suc
    (‖ compose-normal-form c' c {n} {a+c+1+b+d≤n⇒b+a≤n{‖ c ‖} m} ‖ +
     ‖ compose-normal-form d d' {n} {c+a+1+d+b≤n⇒a+b≤n{‖ d ‖} m} ‖)
      ≤⟨ +-monoʳ-≤ 1 (+-mono-≤ l r) ⟩
    suc (‖ c' ‖ + ‖ c ‖ + (‖ d ‖ + ‖ d' ‖))
      ≤⟨ 1+b+a+c+d≤1+a+c+1+b+d{‖ c ‖}{‖ c' ‖} ⟩
    suc (‖ c ‖ + ‖ d ‖ + suc (‖ c' ‖ + ‖ d' ‖))
  ∎

compose-middle-size (prod c d) (prod c' d') {suc n} {s≤s m}
  with compose-normal-form-size c c' {n} {a+c+1+b+d≤n⇒a+b≤n{‖ c ‖} m}
     | compose-normal-form-size d d' {n} {c+a+1+d+b≤n⇒a+b≤n{‖ d ‖} m}
...  | l | r =
  begin
    suc
    (‖ compose-normal-form c c' {n} {a+c+1+b+d≤n⇒a+b≤n{‖ c ‖} m} ‖ +
     ‖ compose-normal-form d d' {n} {c+a+1+d+b≤n⇒a+b≤n{‖ d ‖} m} ‖)
      ≤⟨ +-monoʳ-≤ 1 (+-mono-≤ l r) ⟩
    suc (‖ c ‖ + ‖ c' ‖ + (‖ d ‖ + ‖ d' ‖))
      ≤⟨ 1+a+b+c+d≤1+a+c+1+b+d{‖ c ‖} ⟩
    suc (‖ c ‖ + ‖ d ‖ + suc (‖ c' ‖ + ‖ d' ‖))
  ∎

compose-middle-size (Ref _ _ A _) (Ref _ _ B _) {suc n}
  with ∼-decidable A B
... | yes p = s≤s
  (begin
    ‖ ⊓ p ‖ₜ           ≤⟨ A⊓B≤A+B p ⟩
    ‖ A ‖ₜ + ‖ B ‖ₜ    ≤⟨ +-monoʳ-≤ ‖ A ‖ₜ (n≤1+n _) ⟩
    (‖ A ‖ₜ + suc ‖ B ‖ₜ)
  ∎)
... | no  _ = s≤s z≤n

{- Composing with failure -}

compose-middle-size (fail _ _)    d          {suc _}
  rewrite get-target-type/middle-wt d = m≤m+n _ _
compose-middle-size c@(fun _ _)     (fail _ _) {suc _}
  with get-source-type/middle c | get-source-type/middle-wt c
... | T | refl = m≤m+n _ _
compose-middle-size c@(prod _ _)    (fail _ _) {suc _}
  with get-source-type/middle c | get-source-type/middle-wt c
... | T | refl = m≤m+n _ _
compose-middle-size (Ref _ _ _ _) (fail _ _) {suc _} = m≤m+n _ _

{- Composing with id -}

compose-middle-size (id _)        d      {suc _} = n≤1+n ‖ d ‖ₘ
compose-middle-size (fun _ _)     (id _) {suc _} = m≤m+n _ 1
compose-middle-size (prod _ _)    (id _) {suc _} = m≤m+n _ 1
compose-middle-size (Ref _ _ _ _) (id _) {suc _} = m≤m+n _ 1


compose-final-size c d {0} {m} = ⊥-elim (¬size-two-nf&fcoercions≤0 c d m)

compose-final-size (injSeq B≢⋆ g) (prjSeq A≢⋆ i) {suc n} {s≤s m}
  with compose-final-size (make-final-coercion B≢⋆ A≢⋆) (final i) {n} {m'}
    where m' = make-coercion+i≤n g i n m
... | fst
  with compose-final-size (middle g) i⨟c {n} {injPrj≤n g i n m m'}
    where
      c   = make-final-coercion B≢⋆ A≢⋆
      m'  = make-coercion+i≤n g i n m
      i⨟c = compose-final-internal c (final i) {n} {m'}
... | snd =
  begin
    ‖ compose-final-internal (middle g) i⨟c {n} {injPrj≤n g i n m m'} ‖
      ≤⟨ snd ⟩
    1 + (‖ g ‖ₘ + ‖ compose-final-internal c (final i) {n} {m'} ‖)
      ≤⟨ +-monoʳ-≤ 1 (+-monoʳ-≤ _ fst) ⟩
    suc (‖ g ‖ₘ + (‖ c ‖ᶠ + suc ‖ i ‖ᶠ))
      ≤⟨ +-monoʳ-≤ 1 (+-monoʳ-≤ _ (+-monoˡ-≤ _ (mk-fcoercion-size B≢⋆ A≢⋆))) ⟩
    suc (‖ g ‖ₘ + ((3 + 2 * (‖ B≢⋆ ‖ᵢₜ + ‖ A≢⋆ ‖ᵢₜ)) + suc ‖ i ‖ᶠ))
      ≤⟨ 1+c+3+b+a+b+a+0+1+d≤3+2*b+c+3+2*a+d{‖ A≢⋆ ‖ᵢₜ}{‖ B≢⋆ ‖ᵢₜ} ⟩
    (3 + (2 * ‖ B≢⋆ ‖ᵢₜ) + ‖ g ‖ₘ) + (3 + (2 * ‖ A≢⋆ ‖ᵢₜ) + ‖ i ‖ᶠ)
  ∎
  where
    c   = make-final-coercion B≢⋆ A≢⋆
    m'  = make-coercion+i≤n g i n m
    i⨟c = compose-final-internal c (final i) {n} {m'}

compose-final-size (middle g) (final (injSeq B≢⋆ g')) {suc n} {s≤s m} =
  begin
    4 + (2 * ‖ B≢⋆ ‖ᵢₜ + ‖ compose-middle-internal g g' {n} {a+3+c+b≤n⇒a+b≤n m} ‖ₘ)
      ≤⟨ +-monoʳ-≤ 4 (+-monoʳ-≤ _ (compose-middle-size g g' {n} {a+3+c+b≤n⇒a+b≤n m})) ⟩
    4 + (2 * ‖ B≢⋆ ‖ᵢₜ + (‖ g ‖ₘ + ‖ g' ‖ₘ))
      ≤⟨ 4+2*a+b+c≤1+b+4+2*a+c{‖ B≢⋆ ‖ᵢₜ} ⟩
    1 + (‖ g ‖ₘ + (4 + (2 * ‖ B≢⋆ ‖ᵢₜ + ‖ g' ‖ₘ)))
  ∎

compose-final-size (middle g) (final (middle g')) {suc n} {s≤s m} =
  begin
    2 + ‖ compose-middle-internal g g' {n} {a+2+b≤n⇒a+b≤n m} ‖ₘ
      ≤⟨ +-monoʳ-≤ 2 (compose-middle-size g g' {n} {a+2+b≤n⇒a+b≤n m}) ⟩
    2 + (‖ g ‖ₘ + ‖ g' ‖ₘ)
      ≤⟨ 2+a+b≤1+a+2+b ⟩
    suc (‖ g ‖ₘ + (2 + ‖ g' ‖ₘ))
  ∎

{- id cases -}

compose-final-size (injSeq B≢⋆ _) (final (middle (id _))) {suc _} =
  4+2*a+b≤3+2*a+b+3{‖ B≢⋆ ‖ᵢₜ}

compose-final-size (injSeq _ _) (final (middle (fail _ _))) {suc _} = s≤s (s≤s (s≤s z≤n))

compose-final-size (middle (id _))    (prjSeq _ _)        {suc _} = n≤m+n 2 _

{- Failure cases -}

compose-final-size (middle (fail _ _)) (prjSeq _ c) {suc _}
  with get-target-type/final c | get-target-type/final-wt c
... | _ | refl = s≤s (s≤s (s≤s z≤n))
compose-final-size (injSeq _ _)  (final (injSeq B≢⋆ (fail _ _))) {suc _} = s≤s (s≤s (s≤s z≤n))
compose-final-size (injSeq _ _) (final (injSeq () (id _)))

injPrj≤n {B≢⋆ = B≢⋆}{C≢⋆} g i n m m' =
  begin
    1 + (‖ g ‖ₘ + ‖ i⨟c ‖)
       ≤⟨ +-monoʳ-≤ 1 (+-monoʳ-≤ _ (compose-final-size c (final i) {n} {m'})) ⟩
    1 + (‖ g ‖ₘ + (‖ c ‖ᶠ + suc ‖ i ‖ᶠ))
       ≤⟨ +-monoʳ-≤ 1 (+-monoʳ-≤ _ (+-monoˡ-≤ _ (mk-fcoercion-size B≢⋆ C≢⋆))) ⟩
    1 + (‖ g ‖ₘ + (3 + 2 * (‖ B≢⋆ ‖ᵢₜ + ‖ C≢⋆ ‖ᵢₜ) + suc ‖ i ‖ᶠ))
       ≤⟨ 2+2*a+c+3+2*b+d≤n⇒1+c+3+a+b+a+b+0+1+d≤n{‖ B≢⋆ ‖ᵢₜ} m ⟩
    n
  ∎
  where
    c   = make-final-coercion B≢⋆ C≢⋆
    i⨟c = compose-final-internal c (final i) {n} {m'}

make-coercion+i≤n {B≢⋆ = B≢⋆} {C≢⋆} g i n m =
  begin
    ‖ make-final-coercion B≢⋆ C≢⋆ ‖ᶠ + suc ‖ i ‖ᶠ
        ≤⟨ +-monoˡ-≤ (suc ‖ i ‖ᶠ) (mk-fcoercion-size B≢⋆ C≢⋆) ⟩
    3 + (‖ B≢⋆ ‖ᵢₜ + ‖ C≢⋆ ‖ᵢₜ + (‖ B≢⋆ ‖ᵢₜ + ‖ C≢⋆ ‖ᵢₜ + 0) + suc ‖ i ‖ᶠ)
        ≤⟨ 2+2*a+c+3+2*b+d≤n⇒3+a+b+a+b+0+1+d≤n{‖ B≢⋆ ‖ᵢₜ} m ⟩
    n
  ∎

compose : ∀ {A B C}
  → NormalFormCoercion A B → NormalFormCoercion B C → NormalFormCoercion A C
compose c d = compose-normal-form c d {_} {≤-refl}

compose-final : ∀ {A B C}
  → FinalCoercion A B → NormalFormCoercion B C → NormalFormCoercion A C
compose-final c d = compose-final-internal c d {_} {≤-refl}

compose-middle : ∀ {A B C}
  → MiddleCoercion A B → MiddleCoercion B C → MiddleCoercion A C
compose-middle c d = compose-middle-internal c d {_} {≤-refl}
