module MonoRef.Dynamics.Original.TypeSafety where

open import Data.List.Membership.Propositional
  using (_∈_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl) 
open import Relation.Binary using (Decidable)
open import Relation.Nullary using
  (Dec ; yes ; no)

-- standard library++
open import Data.List.Prefix
  using (∷ʳ-⊒)

open import MonoRef.Coercions.NoSpaceEfficiency.Reduction
open import MonoRef.Coercions.NoSpaceEfficiency.Syntax
open import MonoRef.Language.TargetWithoutBlame
open import MonoRef.Dynamics.EvalCtx
open import MonoRef.Dynamics.Original.Reduction
open import MonoRef.Dynamics.Original.Store
open import MonoRef.Dynamics.PureReduction
open import MonoRef.Dynamics.Substitution
open import MonoRef.Static.Context
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations


data Progress {Σ A} (M : Σ ∣ ∅ ⊢ A) : (ν : Store Σ) → Set where

  step : ∀ {Σ' ν ν'} {N : Σ' ∣ ∅ ⊢ A}
    → M , ν ⟶ₛ N , ν'
    → StoreTypingProgress Σ Σ'
      ------------------------
    → Progress M ν

  done :
      Value M
    → (μ : Store Σ)
    → NormalStore μ
      -------------
    → Progress M μ

  error : ∀ {ν}
    → M ≡ error
      ------------
    → Progress M ν

progress : ∀ {Σ A} → (M : Σ ∣ ∅ ⊢ A) → (μ : Store Σ) → NormalStore μ → Progress M μ
progress (` ()) _ _
progress (ƛ e) ν μ-evd = done (V-ƛ e) ν μ-evd
progress (e₁ · e₂) ν μ-evd with progress e₁ ν μ-evd
... | step (prog-reduce μ-evd' e⟶e') prec = step (prog-reduce μ-evd' (cong (□-·ₗ e₂) (□-·ₗ (embed-expr-with-Σ prec e₂)) e⟶e')) prec
... | step (cast-reduce e⟶e') prec = step (cast-reduce (cong (□-·ₗ e₂) (□-·ₗ (embed-expr-with-Σ prec e₂)) e⟶e')) prec
... | step (error mem x) prec = step (error mem x) prec
... | step (hcast mem x y z cv) prec = step (hcast mem x y z cv) prec
... | step (hdrop mem x y z) prec = step (hdrop mem x y z) prec
... | done v ν' μ-evd' with progress e₂ ν' μ-evd'
... | step (prog-reduce μ-evd'' e⟶e') prec = step (prog-reduce μ-evd'' (cong (□-·ᵣ v) (□-·ᵣ (embed-val-with-Σ prec v)) e⟶e')) prec
... | step (cast-reduce e⟶e') prec = step (cast-reduce (cong (□-·ᵣ v) (□-·ᵣ (embed-val-with-Σ prec v)) e⟶e')) prec
... | step (error mem x) prec = step (error mem x) prec
... | step (hcast mem x y z cv) prec = step (hcast mem x y z cv) prec
... | step (hdrop mem x y z) prec = step (hdrop mem x y z) prec
progress (_ · _) _ _ | done (V-ƛ _) _ _ | done v' _ μ-evd'' = step (prog-reduce μ-evd'' (β-pure (β-ƛ v'))) StoreTypingProgress-refl
... | error refl = step (prog-reduce μ-evd' (cong-error (□-·ᵣ v))) StoreTypingProgress-refl
progress (.error · e₂) ν μ-evd | error refl = step (prog-reduce μ-evd (cong-error (□-·ₗ e₂))) StoreTypingProgress-refl
progress `zero ν μ-evd = done V-zero ν μ-evd
progress (`suc e) ν μ-evd with progress e ν μ-evd
... | step (prog-reduce μ-evd₁ e⟶e') prec = step (prog-reduce μ-evd₁ (cong □-suc □-suc e⟶e')) prec
... | step (cast-reduce e⟶e') prec = step (cast-reduce (cong □-suc □-suc e⟶e')) prec
... | step (error mem x) prec = step (error mem x) prec
... | step (hcast mem red x x₁ CV') prec = step (hcast mem red x x₁ CV') prec
... | step (hdrop mem red x x₁) prec = step (hdrop mem red x x₁) prec
... | done x .ν μ-evd' = done (V-suc x) ν μ-evd'
... | error refl = step (prog-reduce μ-evd (cong-error □-suc)) StoreTypingProgress-refl
progress (case p z s) ν μ-evd with progress p ν μ-evd
... | step (prog-reduce μ-evd' e⟶e') prec = step (prog-reduce μ-evd' (cong (□-caseₚ z s) (□-caseₚ (embed-expr-with-Σ prec z) (embed-expr-with-Σ prec s)) e⟶e')) prec
... | step (cast-reduce e⟶e') prec = step (cast-reduce (cong (□-caseₚ z s) (□-caseₚ (embed-expr-with-Σ prec z) (embed-expr-with-Σ prec s)) e⟶e')) prec
... | step (error mem x) prec = step (error mem x) prec
... | step (hcast mem red x x₁ CV') prec = step (hcast mem red x x₁ CV') prec
... | step (hdrop mem red x x₁) prec = step (hdrop mem red x x₁) prec
... | error refl = step (prog-reduce μ-evd (cong-error (□-caseₚ z s))) StoreTypingProgress-refl
... | done V-zero .ν μ-evd' = step (prog-reduce μ-evd' (β-pure β-zero)) StoreTypingProgress-refl
... | done (V-suc v) .ν μ-evd' = step (prog-reduce μ-evd' (β-pure (β-suc v))) StoreTypingProgress-refl
progress (ref e) ν μ-evd with progress e ν μ-evd
... | step (prog-reduce μ-evd' e⟶e') prec = step (prog-reduce μ-evd' (cong □-ref □-ref e⟶e')) prec
... | step (cast-reduce e⟶e') prec = step (cast-reduce (cong □-ref □-ref e⟶e')) prec
... | step (error mem x) prec = step (error mem x) prec
... | step (hcast mem red x x₁ CV') prec = step (hcast mem red x x₁ CV') prec
... | step (hdrop mem red x x₁) prec = step (hdrop mem red x x₁) prec
progress {Σ = Σ} {A = Ref A} (ref e) ν μ-evd | done v .ν μ-evd' = step (prog-reduce μ-evd' (β-ref v)) (from⊑ₗ (∷ʳ-⊒ A Σ))
... | error refl = step (prog-reduce μ-evd (cong-error □-ref)) StoreTypingProgress-refl
progress (e₁ `× e₂) ν μ-evd with progress e₁ ν μ-evd
... | step (prog-reduce μ-evd' e⟶e') prec = step (prog-reduce μ-evd' (cong (□-×ₗ e₂) (□-×ₗ (embed-expr-with-Σ prec e₂)) e⟶e')) prec
... | step (cast-reduce e⟶e') prec = step (cast-reduce (cong (□-×ₗ e₂) (□-×ₗ (embed-expr-with-Σ prec e₂)) e⟶e')) prec
... | step (error mem x) μ-evd' = step (error mem x) μ-evd'
... | step (hcast mem red x x₁ CV') prec = step (hcast mem red x x₁ CV') prec
... | step (hdrop mem red x x₁) prec = step (hdrop mem red x x₁) prec
... | error refl = step (prog-reduce μ-evd (cong-error (□-×ₗ e₂))) StoreTypingProgress-refl
... | done v₁ .ν μ-evd' with progress e₂ ν μ-evd'
... | step (prog-reduce μ-evd'' e⟶e') prec = step (prog-reduce μ-evd'' (cong (□-×ᵣ v₁) (□-×ᵣ (embed-val-with-Σ prec v₁)) e⟶e')) prec
... | step (cast-reduce e⟶e') prec = step (cast-reduce (cong (□-×ᵣ v₁) (□-×ᵣ (embed-val-with-Σ prec v₁)) e⟶e')) prec
... | step (error mem x) prec = step (error mem x) prec
... | step (hcast mem red x x₁ CV') prec = step (hcast mem red x x₁ CV') prec
... | step (hdrop mem red x x₁) prec = step (hdrop mem red x x₁) prec
... | done v₂ .ν μ-evd'' = done (V-pair v₁ v₂) ν μ-evd''
... | error refl = step (prog-reduce μ-evd (cong-error (□-×ᵣ v₁))) StoreTypingProgress-refl
progress (π₁ e) ν μ-evd with progress e ν μ-evd
... | step (prog-reduce μ-evd' e⟶e') prec = step (prog-reduce μ-evd' (cong □-π₁ □-π₁ e⟶e')) prec
... | step (cast-reduce e⟶e') prec = step (cast-reduce (cong □-π₁ □-π₁ e⟶e')) prec
... | step (error mem x) prec = step (error mem x) prec
... | step (hcast mem red x x₁ CV') prec = step (hcast mem red x x₁ CV') prec
... | step (hdrop mem red x x₁) prec = step (hdrop mem red x x₁) prec
... | done (V-pair v₁ v₂) .ν μ-evd' = step (prog-reduce μ-evd' (β-pure (β-π₁ v₁ v₂))) StoreTypingProgress-refl
... | error refl = step (prog-reduce μ-evd (cong-error □-π₁)) StoreTypingProgress-refl
progress (π₂ e) ν μ-evd with progress e ν μ-evd
... | step (prog-reduce μ-evd' e⟶e') prec = step (prog-reduce μ-evd' (cong □-π₂ □-π₂ e⟶e')) prec
... | step (cast-reduce e⟶e') prec = step (cast-reduce (cong □-π₂ □-π₂ e⟶e')) prec
... | step (error mem x) prec = step (error mem x) prec
... | step (hcast mem red x x₁ CV') prec = step (hcast mem red x x₁ CV') prec
... | step (hdrop mem red x x₁) prec = step (hdrop mem red x x₁) prec
... | done (V-pair v₁ v₂) .ν μ-evd' = step (prog-reduce μ-evd' (β-pure (β-π₂ v₁ v₂))) StoreTypingProgress-refl
... | error refl = step (prog-reduce μ-evd (cong-error □-π₂)) StoreTypingProgress-refl
progress (addr mem prec) ν μ-evd = done (V-addr mem prec) ν μ-evd
progress ((!ₛ e) x) ν μ-evd with progress e ν μ-evd
... | step (prog-reduce μ-evd' e⟶e') prec = step (prog-reduce μ-evd' (cong (□-!ₛ x) (□-!ₛ x) e⟶e')) prec
... | step (cast-reduce e⟶e') prec = step (cast-reduce (cong (□-!ₛ x) (□-!ₛ x) e⟶e')) prec
... | step (error mem x₁) prec = step (error mem x₁) prec
... | step (hcast mem red x₁ x₂ CV') prec = step (hcast mem red x₁ x₂ CV') prec
... | step (hdrop mem red x₁ x₂) prec = step (hdrop mem red x₁ x₂) prec
... | done v .ν μ-evd' = step (prog-reduce μ-evd' (β-!ₛ v)) StoreTypingProgress-refl
... | error refl = step (prog-reduce μ-evd (cong-error (□-!ₛ x))) StoreTypingProgress-refl
progress ((e₁ :=ₛ e₂) x) ν μ-evd with progress e₁ ν μ-evd
... | step (prog-reduce μ-evd' e⟶e') prec = step (prog-reduce μ-evd' (cong (□-:=ₛₗ e₂ x) (□-:=ₛₗ (embed-expr-with-Σ prec e₂) x) e⟶e')) prec
... | step (cast-reduce e⟶e') prec = step (cast-reduce (cong (□-:=ₛₗ e₂ x) (□-:=ₛₗ (embed-expr-with-Σ prec e₂) x) e⟶e')) prec
... | step (error mem x₁) prec = step (error mem x₁) prec
... | step (hcast mem red x₁ x₂ CV') prec = step (hcast mem red x₁ x₂ CV') prec
... | step (hdrop mem red x₁ x₂) prec = step (hdrop mem red x₁ x₂) prec
... | error refl = step (prog-reduce μ-evd (cong-error (□-:=ₛₗ e₂ x))) StoreTypingProgress-refl
... | done v₁ .ν μ-evd' with progress e₂ ν μ-evd'
... | step (prog-reduce μ-evd'' e⟶e') prec = step (prog-reduce μ-evd'' (cong (□-:=ₛᵣ v₁ x) (□-:=ₛᵣ (embed-val-with-Σ prec v₁) x) e⟶e')) prec
... | step (cast-reduce e⟶e') prec = step (cast-reduce (cong (□-:=ₛᵣ v₁ x) (□-:=ₛᵣ (embed-val-with-Σ prec v₁) x) e⟶e')) prec
... | step (error mem x₁) prec = step (error mem x₁) prec
... | step (hcast mem red x₁ x₂ CV') prec = step (hcast mem red x₁ x₂ CV') prec
... | step (hdrop mem red x₁ x₂) prec = step (hdrop mem red x₁ x₂) prec
... | done v₂ .ν μ-evd'' = step (prog-reduce μ-evd'' (β-:=ₛ v₁ v₂)) StoreTypingProgress-refl
... | error refl = step (prog-reduce μ-evd (cong-error (□-:=ₛᵣ v₁ x))) StoreTypingProgress-refl
progress (! e) ν μ-evd with progress e ν μ-evd
... | step (prog-reduce μ-evd' e⟶e') prec = step (prog-reduce μ-evd' (cong □-! □-! e⟶e')) prec
... | step (cast-reduce e⟶e') prec = step (cast-reduce (cong □-! □-! e⟶e')) prec
... | step (error mem x) μ-evd' = step (error mem x) μ-evd'
... | step (hcast mem red x x₁ CV') prec = step (hcast mem red x x₁ CV') prec
... | step (hdrop mem red x x₁) prec = step (hdrop mem red x x₁) prec
... | done v .ν μ-evd' = step (prog-reduce μ-evd' (β-! v)) StoreTypingProgress-refl
... | error refl = step (prog-reduce μ-evd (cong-error □-!)) StoreTypingProgress-refl
progress (e₁ := e₂) ν μ-evd with progress e₁ ν μ-evd
... | step (prog-reduce μ-evd' e⟶e') prec = step (prog-reduce μ-evd' (cong (□-:=ₗ e₂) (□-:=ₗ (embed-expr-with-Σ prec e₂)) e⟶e')) prec
... | step (cast-reduce e⟶e') prec = step (cast-reduce (cong (□-:=ₗ e₂) (□-:=ₗ (embed-expr-with-Σ prec e₂)) e⟶e')) prec
... | step (error mem x₁) prec = step (error mem x₁) prec
... | step (hcast mem red x₁ x₂ CV') prec = step (hcast mem red x₁ x₂ CV') prec
... | step (hdrop mem red x₁ x₂) prec = step (hdrop mem red x₁ x₂) prec
... | error refl = step (prog-reduce μ-evd (cong-error (□-:=ₗ e₂))) StoreTypingProgress-refl
... | done v₁ .ν μ-evd' with progress e₂ ν μ-evd'
... | step (prog-reduce μ-evd'' e⟶e') prec = step (prog-reduce μ-evd'' (cong (□-:=ᵣ v₁) (□-:=ᵣ (embed-val-with-Σ prec v₁)) e⟶e')) prec
... | step (cast-reduce e⟶e') prec = step (cast-reduce (cong (□-:=ᵣ v₁) (□-:=ᵣ (embed-val-with-Σ prec v₁)) e⟶e')) prec
... | step (error mem x₁) prec = step (error mem x₁) prec
... | step (hcast mem red x₁ x₂ CV') prec = step (hcast mem red x₁ x₂ CV') prec
... | step (hdrop mem red x₁ x₂) prec = step (hdrop mem red x₁ x₂) prec
... | done v₂ .ν μ-evd'' = step (prog-reduce μ-evd'' (β-:= v₁ v₂)) StoreTypingProgress-refl
... | error refl = step (prog-reduce μ-evd (cong-error (□-:=ᵣ v₁))) StoreTypingProgress-refl
progress unit ν μ-evd = done V-unit ν μ-evd
progress (e < c >) ν μ-evd with progress e ν μ-evd
... | step (prog-reduce μ-evd' e⟶e') prec = step (prog-reduce μ-evd' (cong (□-<> c) (□-<> c) e⟶e')) prec
... | step (cast-reduce e⟶e') prec = step (cast-reduce (cong (□-<> c) (□-<> c) e⟶e')) prec
... | step (error mem x) prec = step (error mem x) prec
... | step (hcast mem red x₁ x₂ CV') prec = step (hcast mem red x₁ x₂ CV') prec
... | step (hdrop mem red x₁ x₂) prec = step (hdrop mem red x₁ x₂) prec
progress (e < ι >) ν μ-evd | done v .ν μ-evd' = step (cast-reduce (pure (ι v))) StoreTypingProgress-refl
progress ((_ < A ! >) < B `? >) ν μ-evd | done (V-inj v) .ν μ-evd' with ∼P A B
... | yes p = step (cast-reduce (pure (!?₁ v p))) StoreTypingProgress-refl
... | no ¬p = step (cast-reduce (pure (!?₂ v ¬p))) StoreTypingProgress-refl
progress (e < A ! >) ν μ-evd | done v .ν μ-evd' = done (V-inj v) ν μ-evd'
progress (e < c ▹ c₁ >) ν μ-evd | done v .ν μ-evd' = step (cast-reduce (pure (▹ v))) StoreTypingProgress-refl
progress (e < c ⇒ c₁ >) ν μ-evd | done v .ν μ-evd' = step (cast-reduce (pure (⇒ v))) StoreTypingProgress-refl
progress ((_ `× _) < c `× c₁ >) ν μ-evd | done (V-pair v₁ v₂) .ν μ-evd' = step (cast-reduce (pure (`× v₁ v₂))) StoreTypingProgress-refl
progress (e < Ref B >) ν μ-evd | done v .ν μ-evd' with ∼P (store-lookup-rtti/ref v ν) B
... | yes rtti∼B with ∼≡P rtti∼B
... | yes p rewrite p = step (cast-reduce (castref2 v (≡⟹∼ p) (≡⟹⊓∼ p))) StoreTypingProgress-refl
... | no ¬p with ∼⊑P rtti∼B
... | yes p = step (cast-reduce (castref1 v rtti∼B (¬≡⟹¬⊓∼ ¬p p rtti∼B))) (helper1 (StoreTypingProgress-⊑ₕ (ref⟹∈ v) (helper2 rtti∼B)))
  where
    helper2 : store-lookup-rtti/ref v ν ∼ B → ref⟹T v ∼ B
    helper2 c rewrite ref-rtti-preserves-Σ v ν = c

    postulate ⊓helper2-refl : ⊓ (helper2 rtti∼B) ≡ ⊓ rtti∼B

    helper1 : ∀ {Σ} {mem : ref⟹T v ∈ Σ}
      → StoreTypingProgress Σ (Σ-cast mem (⊓ (helper2 rtti∼B)))
      → StoreTypingProgress Σ (Σ-cast mem (⊓ rtti∼B))
    helper1 w rewrite ⊓helper2-refl = w

    StoreTypingProgress-⊑ₕ : ∀ {Σ A B} → (mem : A ∈ Σ) → (c : A ∼ B) → StoreTypingProgress Σ (Σ-cast mem (⊓ c))
    StoreTypingProgress-⊑ₕ mem c = from⊑ₕ (build-prec mem (⊓⟹⊑ₗ c))
... | no ¬p₁ = step (cast-reduce (castref2 v rtti∼B (¬⊑⟹⊓≡ rtti∼B ¬p₁))) StoreTypingProgress-refl
progress (e < Ref B >) ν μ-evd | done v .ν μ-evd' | no ¬p = step (cast-reduce (castref3 v ¬p)) StoreTypingProgress-refl
progress (e < `⊥ >) ν μ-evd | done v .ν μ-evd' = step (cast-reduce (pure (`⊥ v))) StoreTypingProgress-refl
progress (.error < c >) ν μ-evd | error refl = step (prog-reduce μ-evd (cong-error (□-<> c))) StoreTypingProgress-refl
progress error _ _ = error refl
