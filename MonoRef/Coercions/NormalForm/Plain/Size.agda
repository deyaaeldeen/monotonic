module MonoRef.Coercions.NormalForm.Plain.Size where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ ; _+_ ; _*_ ; _≤_)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary.Negation using (contradiction)

open import MonoRef.Coercions.NormalForm.Plain.Syntax
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


‖_‖ₜ : Type → ℕ
‖ (A ⇒ B)  ‖ₜ = 1 + ‖ A ‖ₜ + ‖ B ‖ₜ
‖ (Ref A)  ‖ₜ = 1 + ‖ A ‖ₜ
‖ (A `× B) ‖ₜ = 1 + ‖ A ‖ₜ + ‖ B ‖ₜ
‖ `ℕ       ‖ₜ = 1
‖ Unit     ‖ₜ = 1
‖ ⋆        ‖ₜ = 1

‖_‖ᵢₜ : ∀ {A} → Injectable A → ℕ
‖_‖ᵢₜ {A} _ = ‖ A ‖ₜ

‖_‖ : ∀{A B} → NormalFormCoercion A B → ℕ
‖_‖ᶠ : ∀{A B} → FinalCoercion A B → ℕ
‖_‖ₘ : ∀{A B} → MiddleCoercion A B → ℕ
  
‖ id         ‖ₘ = 1
‖ (fun c d)  ‖ₘ = 1 + ‖ c ‖ + ‖ d ‖
‖ (prod c d) ‖ₘ = 1 + ‖ c ‖ + ‖ d ‖
‖ (Ref t _)  ‖ₘ = 1 + ‖ t ‖ₜ
‖ fail       ‖ₘ = 1

‖ (injSeq B g) ‖ᶠ = 1 + (2 * ‖ B ‖ᵢₜ) + ‖ g ‖ₘ
‖ (middle g)   ‖ᶠ = 1 + ‖ g ‖ₘ

‖ (prjSeq A i) ‖ = 1 + (2 * ‖ A ‖ᵢₜ) + ‖ i ‖ᶠ
‖ (final i)    ‖ = 1 + ‖ i ‖ᶠ


size-nfcoercion≢0 : ∀{A B} → (nc : NormalFormCoercion A B) → ‖ nc ‖ ≢ 0
size-nfcoercion≢0 (prjSeq _ _) = λ ()
size-nfcoercion≢0 (final _   ) = λ ()

size-fcoercion≢0 : ∀{A B} → (fc : FinalCoercion A B) → ‖ fc ‖ᶠ ≢ 0
size-fcoercion≢0 (injSeq _ _) = λ ()
size-fcoercion≢0 (middle _  ) = λ ()

size-mcoercion≢0 : ∀{A B} → (mc : MiddleCoercion A B) → ‖ mc ‖ₘ ≢ 0
size-mcoercion≢0 id         = λ ()
size-mcoercion≢0 (fun _ _ ) = λ ()
size-mcoercion≢0 (prod _ _) = λ ()
size-mcoercion≢0 (Ref _ _)  = λ ()
size-mcoercion≢0 fail       = λ ()

¬size-two-nfcoercions≤0 : ∀{A B C}
  → (nc : NormalFormCoercion A B) → (nd : NormalFormCoercion B C)
  → ‖ nc ‖ + ‖ nd ‖ ≤ 0 → ⊥
¬size-two-nfcoercions≤0 c _ m =
  contradiction (i+j≡0⇒i≡0 (‖ c ‖) (n≤0⇒n≡0 m)) (size-nfcoercion≢0 c)
