module MonoRef.Coercions.NormalForm.Plain.Compose where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ ; suc ; _+_ ; _*_ ; _≤_ ; s≤s ; z≤n)
open import Data.Nat.Properties
open ≤-Reasoning
open import Relation.Binary.PropositionalEquality using (refl ; sym ; cong₂)
open import Relation.Nullary using (yes ; no)

open import MonoRef.Coercions.NormalForm.InEqReasoning
open import MonoRef.Coercions.NormalForm.Plain.Make
open import MonoRef.Coercions.NormalForm.Plain.Size
open import MonoRef.Coercions.NormalForm.Plain.Syntax
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


compose-middle-internal : ∀ {A B C}
  → (mc : MiddleCoercion A B) → (md : MiddleCoercion B C)
  → {n : ℕ} → {m : ‖ mc ‖ₘ + ‖ md ‖ₘ ≤ n }
  → MiddleCoercion A C

compose-middle-final-internal : ∀ {A B C}
  → (mc : MiddleCoercion A B) → (nd : FinalCoercion B C)
  → {n : ℕ} → {m : ‖ mc ‖ₘ + ‖ nd ‖ᶠ ≤ n }
  → FinalCoercion A C

compose-final-normal-internal : ∀ {A B C}
  → (fc : FinalCoercion A B) → (nd : NormalFormCoercion B C)
  → {n : ℕ} → {m : ‖ fc ‖ᶠ + ‖ nd ‖ ≤ n }
  → NormalFormCoercion A C

compose-normal-form : ∀ {A B C}
  → (nc : NormalFormCoercion A B) → (nd : NormalFormCoercion B C)
  → {n : ℕ} → {m : ‖ nc ‖ + ‖ nd ‖ ≤ n }
  → NormalFormCoercion A C

make-coercion+i≤n : ∀ {A B C D} {B≢⋆ : Injectable B} {C≢⋆ : Injectable C}
  → (g : MiddleCoercion A B) → (i : FinalCoercion C D)
  → (n : ℕ)
  → (m : 1 + (2 * (‖ B≢⋆ ‖ᵢₜ) + ‖ g ‖ₘ + (1 + (2 * (‖ C≢⋆ ‖ᵢₜ) + ‖ i ‖ᶠ))) ≤ n)
  → ‖ make-middle-coercion B≢⋆ C≢⋆ ‖ₘ + ‖ i ‖ᶠ ≤ n

injPrj≤n : ∀ {A B C D} {B≢⋆ : Injectable B} {C≢⋆ : Injectable C}
  → (g : MiddleCoercion A B) → (i : FinalCoercion C D)
  → (n : ℕ)
  → (m : 1 + (2 * ‖ B ‖ₜ + ‖ g ‖ₘ + (1 + (2 * ‖ C ‖ₜ + ‖ i ‖ᶠ))) ≤ n)
  → (m' : ‖ make-middle-coercion B≢⋆ C≢⋆ ‖ₘ + ‖ i ‖ᶠ ≤ n)
  → (‖ g ‖ₘ + ‖ compose-middle-final-internal (make-middle-coercion B≢⋆ C≢⋆) i {n} {m'} ‖ᶠ) ≤ n


{- Composing middle coercions -}

compose-middle-internal (fun c d)  (fun c' d')  {n} {m}
  with compose-normal-form c' c {n} {1+a+c+1+b+d≤n⇒b+a≤n{‖ c ‖} m}
     | compose-normal-form d d' {n} {1+c+a+1+d+b≤n⇒a+b≤n{‖ d ‖} m}
...  | c'⨟c | d⨟d' = fun c'⨟c d⨟d'

compose-middle-internal (prod c d) (prod c' d') {n} {m}
  with compose-normal-form c c' {n} {1+a+c+1+b+d≤n⇒a+b≤n{‖ c ‖} m}
     | compose-normal-form d d' {n} {1+c+a+1+d+b≤n⇒a+b≤n{‖ d ‖} m}
...  | c⨟c' | d⨟d' = prod c⨟c' d⨟d'

compose-middle-internal (Ref A x) (Ref B y) {n}
  with ∼-decidable A B
... | yes p = Ref (⊓ p) (⊑-trans (⊓⟹⊑ᵣ p) y)
... | no _ = fail

{- id cases -}

compose-middle-internal id           c  = c
compose-middle-internal c@(fun _ _)  id = c
compose-middle-internal c@(Ref _ _)  id = c
compose-middle-internal c@(prod _ _) id = c

compose-middle-internal fail         d  = fail
compose-middle-internal (fun _ _)  fail = fail
compose-middle-internal (Ref _ _)  fail = fail
compose-middle-internal (prod _ _) fail = fail

compose-middle-final-internal c (injSeq {B = B} B≢⋆ d) {n} {m} =
  injSeq B≢⋆ (compose-middle-internal c d {n} {a+1+c+b≤n⇒a+b≤n{‖ c ‖ₘ}{‖ d ‖ₘ}{2 * ‖ B ‖ₜ} m})
compose-middle-final-internal c (middle d) {n} {m} =
  middle (compose-middle-internal c d {n} {a+1+b≤n⇒a+b≤n{‖ c ‖ₘ} m})

{- Composing final coercions -}

compose-final-normal-internal (injSeq B≢⋆ g) (prjSeq A≢⋆ i) {n} {m} =
  final (compose-middle-final-internal g c⨟i {n} {injPrj≤n g i n m m'})
  where
    c   = make-middle-coercion B≢⋆ A≢⋆
    m'  = make-coercion+i≤n g i n m
    c⨟i = compose-middle-final-internal c i {n} {m'}

compose-final-normal-internal (middle g) (final i) {n} {m} =
  final (compose-middle-final-internal g i {n} {1+a+1+b≤n⇒a+b≤n m})

{- id cases -}

-- this case forces me to return a normal form coercion because this is id on ⋆
compose-final-normal-internal (middle id) i@(prjSeq _ _) = i
compose-final-normal-internal i@(injSeq _ _) (final (middle id)) = final i

{- Failure cases -}

compose-final-normal-internal (middle fail) (prjSeq _ c) = final (middle fail)
compose-final-normal-internal (injSeq _ _) (final (injSeq _ fail)) = final (middle fail)
compose-final-normal-internal (injSeq _ _) (final (middle fail)) = final (middle fail)
compose-final-normal-internal (injSeq _ _) (final (injSeq () id))


{- Composing normal form coercions -}

compose-normal-form c d {0} {m} = ⊥-elim (¬size-two-nfcoercions≤0 c d m)

compose-normal-form (prjSeq A≢⋆ i) c {suc n} {s≤s m}
  with compose-final-normal-internal i c {n} {c+a+b≤n⇒a+b≤n{‖ i ‖ᶠ} m}
compose-normal-form (prjSeq () _) _ | prjSeq _ _
...  | final i⨟c = prjSeq A≢⋆ i⨟c
compose-normal-form (final c) d {suc n} {s≤s m} = compose-final-normal-internal c d {n} {m}


{-
  The following lemmas are needed to reason about the termination of compose
-}

1≤‖A‖ₜ : ∀ A → 1 ≤ ‖ A ‖ₜ
1≤‖A‖ₜ (_ ⇒ _)  = m≤m+n 1 _
1≤‖A‖ₜ (Ref _)  = m≤m+n 1 _
1≤‖A‖ₜ (_ `× _) = m≤m+n 1 _
1≤‖A‖ₜ `ℕ       = ≤-refl
1≤‖A‖ₜ Unit     = ≤-refl
1≤‖A‖ₜ ⋆        = ≤-refl

mk-nfcoercion-size : ∀ A B
  → ‖ (make-normal-form-coercion A B) ‖ ≤ 1 + 2 * ( ‖ A ‖ₜ + ‖ B ‖ₜ)
mk-nfcoercion-size A B with ⌣-decidable A B
... | no _            = 3≤1+2*a+b (1≤‖A‖ₜ A) (1≤‖A‖ₜ B) 
... | yes ⌣-ℕ-refl    = s≤s (s≤s (s≤s z≤n))
... | yes ⌣-Unit-refl = s≤s (s≤s (s≤s z≤n))
mk-nfcoercion-size .⋆ B | yes ⌣-⋆L
  with T≡⋆? B
...  | yes refl = s≤s (s≤s (s≤s z≤n))
...  | no _     = 1+2*c+2≤2+c+1+c+0
mk-nfcoercion-size A .⋆ | yes ⌣-⋆R
  with T≡⋆? A
...  | yes refl = s≤s (s≤s (s≤s z≤n))
...  | no _     = 2+2*c+1≤1+c+1+c+1{‖ A ‖ₜ}
mk-nfcoercion-size (A ⇒ B) (A' ⇒ B') | yes ⌣-⇒
  with make-normal-form-coercion A' A | mk-nfcoercion-size A' A
     | make-normal-form-coercion B B' | mk-nfcoercion-size B B'
...  | c | l | d | r =
  begin
    3 + (‖ c ‖ + ‖ d ‖)
      ≤⟨ +-monoʳ-≤ 3 (+-mono-≤ l r) ⟩
    4 + (‖ A' ‖ₜ + ‖ A ‖ₜ + (‖ A' ‖ₜ + ‖ A ‖ₜ + 0)
         + (1 + (‖ B ‖ₜ + ‖ B' ‖ₜ + (‖ B ‖ₜ + ‖ B' ‖ₜ + 0))))
      ≡⟨ 4+b+a+b+a+0+1+c+d+c+d+0≤2+a+c+1+b+d+1+a+c+1+b+d+0{‖ A ‖ₜ} ⟩
    2 + (‖ A ‖ₜ + ‖ B ‖ₜ + (1 + (‖ A' ‖ₜ + ‖ B' ‖ₜ))
         + (1 + (‖ A ‖ₜ + ‖ B ‖ₜ + (1 + (‖ A' ‖ₜ + ‖ B' ‖ₜ)) + 0)))
  ∎
mk-nfcoercion-size (A `× B) (A' `× B') | yes ⌣-×
  with make-normal-form-coercion A A' | mk-nfcoercion-size A A'
     | make-normal-form-coercion B B' | mk-nfcoercion-size B B'
...  | c | l | d | r =
  begin
    3 + (‖ c ‖ + ‖ d ‖)
      ≤⟨ +-monoʳ-≤ 3 (+-mono-≤ l r) ⟩
    4 + (‖ A ‖ₜ + ‖ A' ‖ₜ + (‖ A ‖ₜ + ‖ A' ‖ₜ + 0) +
            (1 + (‖ B ‖ₜ + ‖ B' ‖ₜ + (‖ B ‖ₜ + ‖ B' ‖ₜ + 0))))
      ≡⟨ 4+a+b+a+b+0+1+c+d+c+d+0≤2+a+c+1+b+d+1+a+c+1+b+d+0{‖ A ‖ₜ} ⟩
    2 + (‖ A ‖ₜ + ‖ B ‖ₜ + (1 + (‖ A' ‖ₜ + ‖ B' ‖ₜ)) +
            (1 + (‖ A ‖ₜ + ‖ B ‖ₜ + (1 + (‖ A' ‖ₜ + ‖ B' ‖ₜ)) + 0)))
  ∎
mk-nfcoercion-size .(Ref _) .(Ref _) | yes ⌣-ref = 3+b≤2+a+1+b+1+a+1+b+0

mk-fcoercion-size : ∀ {A B} → (A≢⋆ : Injectable A) → (B≢⋆ : Injectable B)
  → ‖ (make-middle-coercion A≢⋆ B≢⋆) ‖ₘ ≤ 2 * (‖ A≢⋆ ‖ᵢₜ + ‖ B≢⋆ ‖ᵢₜ)
mk-fcoercion-size A B with ⌣-decidableᵢ A B
... | no _            = 1≤2*a+b (1≤‖A‖ₜ (injectable-to-type A))
... | yes ⌣-ℕ-refl    = s≤s z≤n
... | yes ⌣-Unit-refl = s≤s z≤n
mk-fcoercion-size () _ | yes ⌣-⋆L
mk-fcoercion-size _ () | yes ⌣-⋆R
mk-fcoercion-size {A ⇒ B} {A' ⇒ B'} _ _ | yes ⌣-⇒
  with make-normal-form-coercion A' A | mk-nfcoercion-size A' A
     | make-normal-form-coercion B B' | mk-nfcoercion-size B B'
...  | c | l | d | r =
  begin
    1 + (‖ c ‖ + ‖ d ‖)
      ≤⟨ +-monoʳ-≤ 1 (+-mono-≤ l r) ⟩
    2 + (2 * (‖ A' ‖ₜ + ‖ A ‖ₜ) + (1 + (2 * (‖ B ‖ₜ + ‖ B' ‖ₜ))))
      ≤⟨ 2+b+a+b+a+0+1+c+d+c+d+0≤1+a+c+1+b+d+1+a+c+1+b+d+0{‖ A ‖ₜ} ⟩
    1 + (‖ A ‖ₜ + ‖ B ‖ₜ + (1 + (‖ A' ‖ₜ + ‖ B' ‖ₜ))
        + (1 + (‖ A ‖ₜ + ‖ B ‖ₜ + (1 + (‖ A' ‖ₜ + ‖ B' ‖ₜ)) + 0)))
  ∎
mk-fcoercion-size {A `× B} {A' `× B'} _ _ | yes ⌣-×
  with make-normal-form-coercion A A' | mk-nfcoercion-size A A'
     | make-normal-form-coercion B B' | mk-nfcoercion-size B B'
...  | c | l | d | r =
  begin
    1 + (‖ c ‖ + ‖ d ‖)
      ≤⟨ +-monoʳ-≤ 1 (+-mono-≤ l r) ⟩
    2 + (‖ A ‖ₜ + ‖ A' ‖ₜ + (‖ A ‖ₜ + ‖ A' ‖ₜ + 0)
        + (1 + (‖ B ‖ₜ + ‖ B' ‖ₜ + (‖ B ‖ₜ + ‖ B' ‖ₜ + 0))))
      ≤⟨ 2+a+b+a+b+0+1+c+d+c+d+0≤1+a+c+1+b+d+1+a+c+1+b+d+0{‖ A ‖ₜ} ⟩
    1 + (‖ A ‖ₜ + ‖ B ‖ₜ + (1 + (‖ A' ‖ₜ + ‖ B' ‖ₜ))
        + (1 + (‖ A ‖ₜ + ‖ B ‖ₜ + (1 + (‖ A' ‖ₜ + ‖ B' ‖ₜ)) + 0)))
  ∎
mk-fcoercion-size {Ref A} {Ref B} _ _ | yes ⌣-ref = 1+a≤2*1+b+1+a{‖ B ‖ₜ}{‖ A ‖ₜ}

compose-normal-form-size : ∀ {A B C}
  → (nc : NormalFormCoercion A B) → (nd : NormalFormCoercion B C)
  → {n : ℕ} {m : ‖ nc ‖ + ‖ nd ‖ ≤ n }
  → ‖ compose-normal-form nc nd {n} {m} ‖ ≤ ‖ nc ‖ + ‖ nd ‖

compose-final-normal-size : ∀ {A B C}
  → (fc : FinalCoercion A B) → (nd : NormalFormCoercion B C)
  → {n : ℕ} {m : ‖ fc ‖ᶠ + ‖ nd ‖ ≤ n }
  → ‖ compose-final-normal-internal fc nd {n} {m} ‖ ≤ ‖ fc ‖ᶠ + ‖ nd ‖

compose-middle-final-size : ∀ {A B C}
  → (fc : MiddleCoercion A B) → (nd : FinalCoercion B C)
  → {n : ℕ} {m : ‖ fc ‖ₘ + ‖ nd ‖ᶠ ≤ n }
  → ‖ compose-middle-final-internal fc nd {n} {m} ‖ᶠ ≤ ‖ fc ‖ₘ + ‖ nd ‖ᶠ

compose-middle-size : ∀ {A B C}
  → (mc : MiddleCoercion A B) → (md : MiddleCoercion B C)
  → {n : ℕ} {m : ‖ mc ‖ₘ + ‖ md ‖ₘ ≤ n }
  → ‖ compose-middle-internal mc md {n} {m} ‖ₘ ≤ ‖ mc ‖ₘ + ‖ md ‖ₘ

compose-normal-form-size c d {0} {m} = ⊥-elim (¬size-two-nfcoercions≤0 c d m)

compose-normal-form-size (prjSeq A≢⋆ i) d {suc n} {s≤s m}
  with compose-final-normal-internal i d {n} {c+a+b≤n⇒a+b≤n{‖ i ‖ᶠ} m}
     | compose-final-normal-size i d {n} {c+a+b≤n⇒a+b≤n{‖ i ‖ᶠ} m}
...  | final x | w =
  begin
    1 + (2 * ‖ A≢⋆ ‖ᵢₜ + ‖ x ‖ᶠ)
      ≤⟨ +-monoʳ-≤ 1 (+-monoʳ-≤ _ (n≤1+n ‖ x ‖ᶠ)) ⟩
    1 + (2 * ‖ A≢⋆ ‖ᵢₜ + suc ‖ x ‖ᶠ)
      ≤⟨ +-monoʳ-≤ 1 (+-monoʳ-≤ _ w) ⟩
    1 + ((2 * ‖ A≢⋆ ‖ᵢₜ) + (‖ i ‖ᶠ + ‖ d ‖))
      ≡⟨ cong₂ (_+_) (refl{x = 1}) (sym (+-assoc (2 * ‖ A≢⋆ ‖ᵢₜ) _ _)) ⟩
    1 + (((2 * ‖ A≢⋆ ‖ᵢₜ) + ‖ i ‖ᶠ) + ‖ d ‖)
  ∎
compose-normal-form-size (prjSeq () _) _ | prjSeq _ _ | _

compose-normal-form-size (final c) d {suc n} {s≤s m} =
  begin
    ‖ compose-final-normal-internal c d {n} {m} ‖ ≤⟨ compose-final-normal-size c d {n} {m} ⟩
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
    1 + (‖ ⊓ x ‖ₜ + ‖ ⊓ y ‖ₜ)
      ≤⟨ +-monoʳ-≤ 1 (+-mono-≤ l r) ⟩
    1 + (‖ A ‖ₜ + ‖ A' ‖ₜ + (‖ B ‖ₜ + ‖ B' ‖ₜ))
      ≤⟨ 1+a+b+c+d≤1+a+c+1+b+d{‖ A ‖ₜ} ⟩
    1 + (‖ A ‖ₜ + ‖ B ‖ₜ + (1 + (‖ A' ‖ₜ + ‖ B' ‖ₜ)))
  ∎
A⊓B≤A+B {A `× B} {A' `× B'} (~-× x y)
  with A⊓B≤A+B x | A⊓B≤A+B y
... | l | r =
  begin
    1 + (‖ ⊓ x ‖ₜ + ‖ ⊓ y ‖ₜ)
      ≤⟨ +-monoʳ-≤ 1 (+-mono-≤ l r) ⟩
    1 + (‖ A ‖ₜ + ‖ A' ‖ₜ + (‖ B ‖ₜ + ‖ B' ‖ₜ))
      ≤⟨ 1+a+b+c+d≤1+a+c+1+b+d{‖ A ‖ₜ} ⟩
    1 + (‖ A ‖ₜ + ‖ B ‖ₜ + (1 + (‖ A' ‖ₜ + ‖ B' ‖ₜ)))
  ∎
A⊓B≤A+B {Ref A}{Ref B} (~-ref p) with A⊓B≤A+B p
... | w =
  begin
    suc ‖ ⊓ p ‖ₜ           ≤⟨ +-monoʳ-≤ 1 w ⟩
    suc (‖ A ‖ₜ + ‖ B ‖ₜ) ≤⟨ +-monoʳ-≤ 1 (+-monoʳ-≤ _ (n≤1+n _)) ⟩
    suc (‖ A ‖ₜ + suc ‖ B ‖ₜ)
  ∎

compose-middle-size (fun c d) (fun c' d') {n} {m}
  with compose-normal-form-size c' c {n} {1+a+c+1+b+d≤n⇒b+a≤n{‖ c ‖} m}
     | compose-normal-form-size d d' {n} {1+c+a+1+d+b≤n⇒a+b≤n{‖ d ‖} m}
...  | l | r =
  begin
    suc
    (‖ compose-normal-form c' c {n} {1+a+c+1+b+d≤n⇒b+a≤n{‖ c ‖} m} ‖ +
     ‖ compose-normal-form d d' {n} {1+c+a+1+d+b≤n⇒a+b≤n{‖ d ‖} m} ‖)
      ≤⟨ +-monoʳ-≤ 1 (+-mono-≤ l r) ⟩
    suc (‖ c' ‖ + ‖ c ‖ + (‖ d ‖ + ‖ d' ‖))
      ≤⟨ 1+b+a+c+d≤1+a+c+1+b+d{‖ c ‖}{‖ c' ‖} ⟩
    suc (‖ c ‖ + ‖ d ‖ + suc (‖ c' ‖ + ‖ d' ‖))
  ∎

compose-middle-size (prod c d) (prod c' d') {n} {m}
  with compose-normal-form-size c c' {n} {1+a+c+1+b+d≤n⇒a+b≤n{‖ c ‖} m}
     | compose-normal-form-size d d' {n} {1+c+a+1+d+b≤n⇒a+b≤n{‖ d ‖} m}
...  | l | r =
  begin
    suc
    (‖ compose-normal-form c c' {n} {1+a+c+1+b+d≤n⇒a+b≤n{‖ c ‖} m} ‖ +
     ‖ compose-normal-form d d' {n} {1+c+a+1+d+b≤n⇒a+b≤n{‖ d ‖} m} ‖)
      ≤⟨ +-monoʳ-≤ 1 (+-mono-≤ l r) ⟩
    suc (‖ c ‖ + ‖ c' ‖ + (‖ d ‖ + ‖ d' ‖))
      ≤⟨ 1+a+b+c+d≤1+a+c+1+b+d{‖ c ‖} ⟩
    suc (‖ c ‖ + ‖ d ‖ + suc (‖ c' ‖ + ‖ d' ‖))
  ∎

compose-middle-size (Ref A _) (Ref B _)
  with ∼-decidable A B
... | yes p = s≤s
  (begin
    ‖ ⊓ p ‖ₜ           ≤⟨ A⊓B≤A+B p ⟩
    ‖ A ‖ₜ + ‖ B ‖ₜ    ≤⟨ +-monoʳ-≤ ‖ A ‖ₜ (n≤1+n _) ⟩
    (‖ A ‖ₜ + suc ‖ B ‖ₜ)
  ∎)
... | no  _ = s≤s z≤n

{- Composing with failure -}

compose-middle-size fail       d    = m≤m+n _ _
compose-middle-size (fun _ _)  fail = m≤m+n _ _
compose-middle-size (prod _ _) fail = m≤m+n _ _
compose-middle-size (Ref _ _)  fail = m≤m+n _ _

{- Composing with id -}

compose-middle-size id         d  = n≤1+n ‖ d ‖ₘ
compose-middle-size (fun _ _)  id = m≤m+n _ 1
compose-middle-size (prod _ _) id = m≤m+n _ 1
compose-middle-size (Ref _ _)  id = m≤m+n _ 1

compose-middle-final-size c (injSeq {B = B} iB d) {n} {m} =
  begin
    1 + (2 * ‖ B ‖ₜ + ‖ compose-middle-internal c d {n} {a+1+c+b≤n⇒a+b≤n{‖ c ‖ₘ}{‖ d ‖ₘ}{2 * ‖ B ‖ₜ} m} ‖ₘ)
      ≤⟨ +-monoʳ-≤ 1 (+-monoʳ-≤ (2 * ‖ B ‖ₜ) (compose-middle-size c d {n} {a+1+c+b≤n⇒a+b≤n{‖ c ‖ₘ}{‖ d ‖ₘ}{2 * ‖ B ‖ₜ} m} )) ⟩
    1 + (2 * ‖ B ‖ₜ + (‖ c ‖ₘ + ‖ d ‖ₘ))
      ≡⟨ 1+a+b+c≡b+1+a+c{2 * ‖ B ‖ₜ}{‖ c ‖ₘ}{‖ d ‖ₘ} ⟩
    ‖ c ‖ₘ + (1 + 2 * ‖ B ‖ₜ + ‖ d ‖ₘ)
  ∎
compose-middle-final-size c (middle d) {n} {m} =
  begin
    1 + ‖ compose-middle-internal c d {n} {a+1+b≤n⇒a+b≤n{‖ c ‖ₘ} m} ‖ₘ
      ≤⟨ +-monoʳ-≤ 1 (compose-middle-size c d {n} {a+1+b≤n⇒a+b≤n{‖ c ‖ₘ} m} ) ⟩
    1 + (‖ c ‖ₘ + ‖ d ‖ₘ)
      ≡⟨ 1+a+b≡a+1+b {‖ c ‖ₘ} ⟩
    ‖ c ‖ₘ + suc ‖ d ‖ₘ
  ∎

compose-final-normal-size (injSeq B≢⋆ g) (prjSeq A≢⋆ i) {n} {m}
  with compose-middle-final-size (make-middle-coercion B≢⋆ A≢⋆) i {n} {make-coercion+i≤n g i n m}
... | fst
  with compose-middle-final-size g i⨟c {n} {injPrj≤n g i n m m'}
    where
      c   = make-middle-coercion B≢⋆ A≢⋆
      m'  = make-coercion+i≤n g i n m
      i⨟c = compose-middle-final-internal c i {n} {m'}
... |   snd =
  begin
    1 + ‖ compose-middle-final-internal g i⨟c {n} {injPrj≤n g i n m m'} ‖ᶠ
      ≤⟨ +-monoʳ-≤ 1 snd ⟩
    1 + ‖ g ‖ₘ + ‖ compose-middle-final-internal c i {n} {m'} ‖ᶠ
      ≤⟨ +-monoʳ-≤ 1 (+-monoʳ-≤ _ fst) ⟩
    1 + (‖ g ‖ₘ + (‖ c ‖ₘ + ‖ i ‖ᶠ))
      ≤⟨ +-monoʳ-≤ 1 (+-monoʳ-≤ ‖ g ‖ₘ (+-monoˡ-≤ _ (mk-fcoercion-size B≢⋆ A≢⋆))) ⟩
    1 + (‖ g ‖ₘ + ((2 * (‖ B≢⋆ ‖ᵢₜ + ‖ A≢⋆ ‖ᵢₜ)) + ‖ i ‖ᶠ))
      ≤⟨ 1+c+2*b+a+d≤1+2*b+c+1+2*a+d{‖ A≢⋆ ‖ᵢₜ}{‖ B≢⋆ ‖ᵢₜ} ⟩
    (1 + (2 * ‖ B≢⋆ ‖ᵢₜ) + ‖ g ‖ₘ) + (1 + (2 * ‖ A≢⋆ ‖ᵢₜ) + ‖ i ‖ᶠ)
  ∎
  where
    c   = make-middle-coercion B≢⋆ A≢⋆
    m'  = make-coercion+i≤n g i n m
    i⨟c = compose-middle-final-internal c i {n} {m'}

compose-final-normal-size (injSeq _ _) (final (injSeq () id))
compose-final-normal-size (injSeq {B = B} _ x) (final (injSeq {B = B'} _ fail)) = 3≤1+2*a+b+2+2*c+1{‖ B ‖ₜ}{‖ x ‖ₘ}{‖ B' ‖ₜ}
compose-final-normal-size (injSeq {B = B} _ _) (final (middle id)) = 2+2*a+b≤1+2*a+b+3{‖ B ‖ₜ}
compose-final-normal-size (injSeq {B = B} _ _) (final (middle fail)) = 3≤1+2*a+b+3{‖ B ‖ₜ}
compose-final-normal-size (middle g) (final i) {n} {m} =
  begin
    suc ‖ compose-middle-final-internal g i ‖ᶠ
      ≤⟨ +-monoʳ-≤ 1 (compose-middle-final-size g i {n} {1+a+1+b≤n⇒a+b≤n m}) ⟩
    suc (‖ g ‖ₘ + ‖ i ‖ᶠ)
      ≤⟨ +-monoʳ-≤ 1 (+-monoʳ-≤ ‖ g ‖ₘ (n≤1+n _)) ⟩
    suc (‖ g ‖ₘ + suc ‖ i ‖ᶠ)
  ∎
compose-final-normal-size (middle id) (prjSeq _ _) = n≤m+n 2 _
compose-final-normal-size (middle fail) (prjSeq _ _) = s≤s (s≤s (s≤s z≤n))

injPrj≤n {B≢⋆ = B≢⋆}{C≢⋆} g i n m m' =
  begin
    ‖ g ‖ₘ + ‖ compose-middle-final-internal c i {n} {m'} ‖ᶠ
       ≤⟨ (+-monoʳ-≤ _ (compose-middle-final-size c i {n} {m'})) ⟩
    ‖ g ‖ₘ + (‖ c ‖ₘ + ‖ i ‖ᶠ)
       ≤⟨ +-monoʳ-≤ ‖ g ‖ₘ (+-monoˡ-≤ _ (mk-fcoercion-size B≢⋆ C≢⋆)) ⟩
    ‖ g ‖ₘ + (2 * (‖ B≢⋆ ‖ᵢₜ + ‖ C≢⋆ ‖ᵢₜ) + ‖ i ‖ᶠ)
       ≤⟨ 1+2*b+a+1+2*c+d≤n⇒a+2*b+c+d≤n{‖ g ‖ₘ}{‖ B≢⋆ ‖ᵢₜ}{‖ C≢⋆ ‖ᵢₜ}{‖ i ‖ᶠ} m ⟩
    n
  ∎
  where
    c = make-middle-coercion B≢⋆ C≢⋆

make-coercion+i≤n {B≢⋆ = B≢⋆} {C≢⋆} g i n m =
  begin
    ‖ make-middle-coercion B≢⋆ C≢⋆ ‖ₘ + ‖ i ‖ᶠ
        ≤⟨ +-monoˡ-≤ (‖ i ‖ᶠ) (mk-fcoercion-size B≢⋆ C≢⋆) ⟩
    2 * (‖ B≢⋆ ‖ᵢₜ + ‖ C≢⋆ ‖ᵢₜ) + ‖ i ‖ᶠ
        ≤⟨ 1+2*a+c+1+2*b+d≤n⇒2*a+b+d≤n{‖ B≢⋆ ‖ᵢₜ} m ⟩
    n
  ∎

compose : ∀ {A B C}
  → NormalFormCoercion A B → NormalFormCoercion B C → NormalFormCoercion A C
compose c d = compose-normal-form c d {_} {≤-refl}

compose-final : ∀ {A B C}
  → FinalCoercion A B → NormalFormCoercion B C → NormalFormCoercion A C
compose-final c d = compose-final-normal-internal c d {_} {≤-refl}

compose-middle : ∀ {A B C}
  → MiddleCoercion A B → MiddleCoercion B C → MiddleCoercion A C
compose-middle c d = compose-middle-internal c d {_} {≤-refl}
