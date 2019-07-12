module MonoRef.Coercions.NormalForm.Faithful.Height.Lemmas where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ ; suc ; _+_ ; _*_ ; _≤_ ; _⊔_ ; z≤n ; s≤s)
open import Data.Nat.Properties
open ≤-Reasoning
open import Relation.Binary.PropositionalEquality using (refl ; sym ; cong₂)
open import Relation.Nullary using (yes ; no)

open import MonoRef.Coercions.NormalForm.Faithful.Compose
open import MonoRef.Coercions.NormalForm.Faithful.Make
open import MonoRef.Coercions.NormalForm.Faithful.Size
open import MonoRef.Coercions.NormalForm.Faithful.Syntax
open import MonoRef.Coercions.NormalForm.InEqReasoning
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


‖_‖ʰₜ : Type → ℕ
‖ (A ⇒ B)  ‖ʰₜ = 1 + (‖ A ‖ʰₜ ⊔ ‖ B ‖ʰₜ)
‖ (Ref A)  ‖ʰₜ = 1 + ‖ A ‖ʰₜ
‖ (A `× B) ‖ʰₜ = 1 + (‖ A ‖ʰₜ ⊔ ‖ B ‖ʰₜ)
‖ `ℕ       ‖ʰₜ = 1
‖ Unit     ‖ʰₜ = 1
‖ ⋆        ‖ʰₜ = 1

‖_‖ʰᵢₜ : ∀ {A} → Injectable A → ℕ
‖_‖ʰᵢₜ {A} _ = ‖ A ‖ʰₜ

‖_‖ʰ : ∀{A B} → NormalFormCoercion A B → ℕ
‖_‖ʰᶠ : ∀{A B} → FinalCoercion A B → ℕ
‖_‖ʰₘ : ∀{A B} → MiddleCoercion A B → ℕ
  
‖ id         ‖ʰₘ = 1
‖ (fun c d)  ‖ʰₘ = 1 + (‖ c ‖ʰ ⊔ ‖ d ‖ʰ)
‖ (prod c d) ‖ʰₘ = 1 + (‖ c ‖ʰ ⊔ ‖ d ‖ʰ)
‖ (Ref t _)  ‖ʰₘ = 1 + ‖ t ‖ʰₜ
‖ fail       ‖ʰₘ = 1

‖ fail         ‖ʰᶠ = 1
‖ (injSeq B g) ‖ʰᶠ = ‖ B ‖ʰᵢₜ ⊔ ‖ g ‖ʰₘ
‖ (middle g)   ‖ʰᶠ = ‖ g ‖ʰₘ

‖ (prjSeq A i) ‖ʰ = ‖ A ‖ʰᵢₜ ⊔ ‖ i ‖ʰᶠ
‖ (final i)    ‖ʰ = ‖ i ‖ʰᶠ

1≤‖A‖ʰ : ∀ A → 1 ≤ ‖ A ‖ʰₜ
1≤‖A‖ʰ (_ ⇒ _)  = m≤m+n 1 _
1≤‖A‖ʰ (Ref _)  = m≤m+n 1 _
1≤‖A‖ʰ (_ `× _) = m≤m+n 1 _
1≤‖A‖ʰ `ℕ       = ≤-refl
1≤‖A‖ʰ Unit     = ≤-refl
1≤‖A‖ʰ ⋆        = ≤-refl

mk-nfcoercion-height : ∀ A B
  → ‖ (make-normal-form-coercion A B) ‖ʰ ≤ (‖ A ‖ʰₜ ⊔ ‖ B ‖ʰₜ)
mk-nfcoercion-height A B with ⌣-decidable A B
... | no _ =
  begin
    1
      ≤⟨ 1≤‖A‖ʰ A ⟩
    ‖ A ‖ʰₜ
      ≤⟨ m≤m⊔n _ ‖ B ‖ʰₜ  ⟩
    ‖ A ‖ʰₜ ⊔ ‖ B ‖ʰₜ
  ∎
mk-nfcoercion-height .`ℕ .`ℕ | yes ⌣-ℕ-refl = s≤s z≤n
mk-nfcoercion-height .Unit .Unit | yes ⌣-Unit-refl = s≤s z≤n
mk-nfcoercion-height .⋆ B | yes ⌣-⋆L
  with T≡⋆? B
... | yes refl = s≤s z≤n
... | no _ = ≤-reflexive (⊔-comm _ 1)
mk-nfcoercion-height A .⋆ | yes ⌣-⋆R
  with T≡⋆? A
... | yes refl = s≤s z≤n
... | no _ = ≤-refl
mk-nfcoercion-height (A ⇒ B) (A' ⇒ B') | yes ⌣-⇒
  with make-normal-form-coercion A' A | mk-nfcoercion-height A' A
     | make-normal-form-coercion B B' | mk-nfcoercion-height B B'
...  | c | l | d | r =
  begin
    suc (‖ c ‖ʰ ⊔ ‖ d ‖ʰ)
      ≤⟨ +-monoʳ-≤ 1 (⊔-mono-≤ l r) ⟩
    suc ((‖ A' ‖ʰₜ ⊔ ‖ A ‖ʰₜ) ⊔ (‖ B ‖ʰₜ ⊔ ‖ B' ‖ʰₜ))
      ≤⟨ (1+b⊔a⊔c⊔d≤1+a⊔c⊔b⊔d{‖ A ‖ʰₜ}{‖ A' ‖ʰₜ}) ⟩
    suc ((‖ A ‖ʰₜ ⊔ ‖ B ‖ʰₜ ⊔ (‖ A' ‖ʰₜ ⊔ ‖ B' ‖ʰₜ)))
  ∎
mk-nfcoercion-height (A `× B) (A' `× B') | yes ⌣-×
  with make-normal-form-coercion A A' | mk-nfcoercion-height A A'
     | make-normal-form-coercion B B' | mk-nfcoercion-height B B'
...  | c | l | d | r =
  begin
    suc (‖ c ‖ʰ ⊔ ‖ d ‖ʰ)
      ≤⟨ +-monoʳ-≤ 1 (⊔-mono-≤ l r) ⟩
    suc ((‖ A ‖ʰₜ ⊔ ‖ A' ‖ʰₜ) ⊔ (‖ B ‖ʰₜ ⊔ ‖ B' ‖ʰₜ))
      ≤⟨ (1+a⊔b⊔c⊔d≤1+a⊔c⊔b⊔d{‖ A ‖ʰₜ}{‖ A' ‖ʰₜ}) ⟩
    suc ((‖ A ‖ʰₜ ⊔ ‖ B ‖ʰₜ ⊔ (‖ A' ‖ʰₜ ⊔ ‖ B' ‖ʰₜ)))
  ∎
mk-nfcoercion-height .(Ref _) (Ref B) | yes ⌣-ref = s≤s (n≤m⊔n _ ‖ B ‖ʰₜ)

mk-fcoercion-height : ∀ {A B} → (A≢⋆ : Injectable A) → (B≢⋆ : Injectable B)
  → ‖ (make-final-coercion A≢⋆ B≢⋆) ‖ʰᶠ ≤ (‖ A≢⋆ ‖ʰᵢₜ ⊔ ‖ B≢⋆ ‖ʰᵢₜ)
mk-fcoercion-height {A} A≢⋆ B≢⋆ with ⌣-decidableᵢ A≢⋆ B≢⋆
... | no _ =
  begin
    1
      ≤⟨ 1≤‖A‖ʰ A ⟩
    ‖ A ‖ʰₜ
      ≤⟨ m≤m⊔n _ ‖ B≢⋆ ‖ʰᵢₜ  ⟩
    ‖ A ‖ʰₜ ⊔ ‖ B≢⋆ ‖ʰᵢₜ
  ∎
... | yes ⌣-ℕ-refl = s≤s z≤n
... | yes ⌣-Unit-refl = s≤s z≤n
mk-fcoercion-height () _ | yes ⌣-⋆L
mk-fcoercion-height _ () | yes ⌣-⋆R
mk-fcoercion-height {A ⇒ B} {A' ⇒ B'} _ _ | yes ⌣-⇒
  with make-normal-form-coercion A' A | mk-nfcoercion-height A' A
     | make-normal-form-coercion B B' | mk-nfcoercion-height B B'
...  | c | l | d | r =
  begin
    suc (‖ c ‖ʰ ⊔ ‖ d ‖ʰ)
      ≤⟨ +-monoʳ-≤ 1 (⊔-mono-≤ l r) ⟩
    suc ((‖ A' ‖ʰₜ ⊔ ‖ A ‖ʰₜ) ⊔ (‖ B ‖ʰₜ ⊔ ‖ B' ‖ʰₜ))
      ≤⟨ (1+b⊔a⊔c⊔d≤1+a⊔c⊔b⊔d{‖ A ‖ʰₜ}{‖ A' ‖ʰₜ}) ⟩
    suc ((‖ A ‖ʰₜ ⊔ ‖ B ‖ʰₜ ⊔ (‖ A' ‖ʰₜ ⊔ ‖ B' ‖ʰₜ)))
  ∎
mk-fcoercion-height {A `× B} {A' `× B'} _ _ | yes ⌣-×
  with make-normal-form-coercion A A' | mk-nfcoercion-height A A'
     | make-normal-form-coercion B B' | mk-nfcoercion-height B B'
...  | c | l | d | r =
  begin
    suc (‖ c ‖ʰ ⊔ ‖ d ‖ʰ)
      ≤⟨ +-monoʳ-≤ 1 (⊔-mono-≤ l r) ⟩
    suc ((‖ A ‖ʰₜ ⊔ ‖ A' ‖ʰₜ) ⊔ (‖ B ‖ʰₜ ⊔ ‖ B' ‖ʰₜ))
      ≤⟨ (1+a⊔b⊔c⊔d≤1+a⊔c⊔b⊔d{‖ A ‖ʰₜ}{‖ A' ‖ʰₜ}) ⟩
    suc ((‖ A ‖ʰₜ ⊔ ‖ B ‖ʰₜ ⊔ (‖ A' ‖ʰₜ ⊔ ‖ B' ‖ʰₜ)))
  ∎
mk-fcoercion-height {Ref A} {Ref B} _ _ | yes ⌣-ref = s≤s (n≤m⊔n _ ‖ B ‖ʰₜ)

A⊓B≤A⊔B : ∀ {A B} → (A∼B : A ∼ B) → ‖ ⊓ A∼B ‖ʰₜ ≤ ‖ A ‖ʰₜ ⊔ ‖ B ‖ʰₜ
A⊓B≤A⊔B ∼-ℕ-refl = s≤s z≤n
A⊓B≤A⊔B ∼-Unit-refl = s≤s z≤n
A⊓B≤A⊔B ∼-⋆R = m≤m⊔n _ 1
A⊓B≤A⊔B ∼-⋆L = n≤m⊔n 1 _
A⊓B≤A⊔B {A ⇒ B} {A' ⇒ B'} (~-⇒ x y)
  with A⊓B≤A⊔B x | A⊓B≤A⊔B y
... | l | r =
  begin
    1 + (‖ ⊓ x ‖ʰₜ ⊔ ‖ ⊓ y ‖ʰₜ)
      ≤⟨ +-monoʳ-≤ 1 (⊔-mono-≤ l r) ⟩
    1 + (‖ A ‖ʰₜ ⊔ ‖ A' ‖ʰₜ ⊔ (‖ B ‖ʰₜ ⊔ ‖ B' ‖ʰₜ))
      ≤⟨ 1+a⊔b⊔c⊔d≤1+a⊔c⊔b⊔d{‖ A ‖ʰₜ} ⟩
    1 + (‖ A ‖ʰₜ ⊔ ‖ B ‖ʰₜ ⊔ (‖ A' ‖ʰₜ ⊔ ‖ B' ‖ʰₜ))
  ∎
A⊓B≤A⊔B {A `× B} {A' `× B'} (~-× x y)
  with A⊓B≤A⊔B x | A⊓B≤A⊔B y
... | l | r =
  begin
    1 + (‖ ⊓ x ‖ʰₜ ⊔ ‖ ⊓ y ‖ʰₜ)
      ≤⟨ +-monoʳ-≤ 1 (⊔-mono-≤ l r) ⟩
    1 + (‖ A ‖ʰₜ ⊔ ‖ A' ‖ʰₜ ⊔ (‖ B ‖ʰₜ ⊔ ‖ B' ‖ʰₜ))
      ≤⟨ 1+a⊔b⊔c⊔d≤1+a⊔c⊔b⊔d{‖ A ‖ʰₜ} ⟩
    1 + (‖ A ‖ʰₜ ⊔ ‖ B ‖ʰₜ ⊔ (‖ A' ‖ʰₜ ⊔ ‖ B' ‖ʰₜ))
  ∎
A⊓B≤A⊔B {Ref A}{Ref B} (~-ref p) with A⊓B≤A⊔B p
... | w =
  begin
    suc ‖ ⊓ p ‖ʰₜ           ≤⟨ +-monoʳ-≤ 1 w ⟩
    suc (‖ A ‖ʰₜ ⊔ ‖ B ‖ʰₜ)
  ∎
