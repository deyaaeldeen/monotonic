module MonoRef.Dynamics.Original.Store where

open import Data.List
  using (_∷_ ; _∷ʳ_ ; length)
open import Data.List.All
  using (All ; map ; lookup)
open import Data.List.Any using (here; there)
open import Data.List.Membership.Propositional
  using (_∈_)
open import Data.List.Relation.Pointwise
  using (Pointwise ; _∷_) renaming (refl to pw-refl ; transitive to pw-trans)
open import Data.Product
  using (∃-syntax ; -,_) renaming (_,_ to _`,_)
open import Relation.Binary
  using (Transitive ; Rel)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; subst)

-- standard library++
open import Data.List.Prefix
  using (∷ʳ-⊒ ; ∈-⊒) renaming (_⊑_ to _⊑ₗ_)
open import Data.List.All.Properties.Extra
  using (_All[_]≔'_ ; _all-∷ʳ_)

open import MonoRef.Coercions.NoSpaceEfficiency.Syntax
open import MonoRef.Language.TargetWithoutBlame
open import MonoRef.Static.Context
open import MonoRef.Static.Types
open import MonoRef.Static.Types.Relations

infix 5 v⇑_
infix 3  _⊑ₕ_
infix  3 _,_∈_


data CastedValue {Σ Γ} : ∀ {A} → Σ ∣ Γ ⊢ A → Set where

  v⇑_ : ∀ {A} {t : Σ ∣ Γ ⊢ A}
    → Value t
      -------------
    → CastedValue t

  _<_> : ∀ {A B} {t : Σ ∣ Γ ⊢ A}
    → CastedValue t
    → (c : A ⟹ B)
      ---------------------
    → CastedValue (t < c >)

  <_,_> : ∀ {A B} {V₁ : Σ ∣ Γ ⊢ A} {V₂ : Σ ∣ Γ ⊢ B}
    → CastedValue V₁
    → CastedValue V₂
      ----------------------
    → CastedValue (V₁ `× V₂)

data NormalStoreValue : (A : Type) → (Σ : StoreTyping) → Set where

  intro : ∀ {Σ A} {V : Σ ∣ ∅ ⊢ A}
    → Value V
    → Ty A
      --------------------
    → NormalStoreValue A Σ

data EvolvingStoreValue : (A : Type) → (Σ : StoreTyping) → Set where

  intro : ∀ {Σ A} {V : Σ ∣ ∅ ⊢ A}
    → CastedValue V
    → Ty A
      ----------------------
    → EvolvingStoreValue A Σ

data StoreValue (A : Type) (Σ : StoreTyping) :  Set where

  fromNormalValue : NormalStoreValue A Σ → StoreValue A Σ

  fromCastedValue : EvolvingStoreValue A Σ → StoreValue A Σ

Store : (Σ : StoreTyping) → Set
Store Σ = All (λ ty → StoreValue ty Σ) Σ

toNormalStoreValue : ∀ {Σ A} {v : Σ ∣ ∅ ⊢ A} → Value v → NormalStoreValue A Σ
toNormalStoreValue {A = A} v = intro v (Type⇑ A)

prefix-weaken-expr : ∀ {Σ Σ' Γ A} → Σ ⊑ₗ Σ'
  → Σ  ∣ Γ ⊢ A
  → Σ' ∣ Γ ⊢ A
prefix-weaken-expr _   (` x) = ` x
prefix-weaken-expr ext (ƛ e) = ƛ prefix-weaken-expr ext e
prefix-weaken-expr ext (ƛₚ e c) = ƛₚ (prefix-weaken-expr ext e) c
prefix-weaken-expr ext (e · e₁) =
  prefix-weaken-expr ext e · prefix-weaken-expr ext e₁
prefix-weaken-expr _   `zero = `zero
prefix-weaken-expr ext (`suc e) = `suc prefix-weaken-expr ext e
prefix-weaken-expr ext (case e e₁ e₂) =
  case (prefix-weaken-expr ext e)
       (prefix-weaken-expr ext e₁)
       (prefix-weaken-expr ext e₂)
prefix-weaken-expr ext (ref e) = ref prefix-weaken-expr ext e
prefix-weaken-expr ext (e `× e₁) =
  prefix-weaken-expr ext e `× prefix-weaken-expr ext e₁
prefix-weaken-expr ext (π₁ e) = π₁ prefix-weaken-expr ext e
prefix-weaken-expr ext (π₂ e) = π₂ prefix-weaken-expr ext e
prefix-weaken-expr ext (addr mem prec) = addr (∈-⊒ mem ext) prec
prefix-weaken-expr ext ((!ₛ e) x) = (!ₛ prefix-weaken-expr ext e) x
prefix-weaken-expr ext ((e :=ₛ e₁) x) =
  (prefix-weaken-expr ext e :=ₛ prefix-weaken-expr ext e₁) x
prefix-weaken-expr ext (! e) = ! prefix-weaken-expr ext e
prefix-weaken-expr ext (e := e₁) =
  prefix-weaken-expr ext e := prefix-weaken-expr ext e₁
prefix-weaken-expr _   unit = unit
prefix-weaken-expr ext (e < x >) = prefix-weaken-expr ext e < x >
prefix-weaken-expr _   error = error

prefix-weaken-val : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A} → (ext : Σ ⊑ₗ Σ')
  → Value v
  → Value (prefix-weaken-expr ext v)
prefix-weaken-val ext (V-ƛ N) = V-ƛ (prefix-weaken-expr ext N)
prefix-weaken-val ext (V-ƛₚ e c) = V-ƛₚ (prefix-weaken-val ext e) c
prefix-weaken-val _   V-zero = V-zero
prefix-weaken-val ext (V-suc v) = V-suc (prefix-weaken-val ext v)
prefix-weaken-val _   V-unit = V-unit
prefix-weaken-val ext (V-addr mem prec) = V-addr (∈-⊒ mem ext) prec 
prefix-weaken-val ext (V-pair v v₁) =
  V-pair (prefix-weaken-val ext v) (prefix-weaken-val ext v₁)
prefix-weaken-val ext (V-inj v) = V-inj (prefix-weaken-val ext v)

prefix-weaken-cv : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A} → (ext : Σ ⊑ₗ Σ')
  → CastedValue v
  → CastedValue (prefix-weaken-expr ext v)
prefix-weaken-cv ext (v⇑ x) = v⇑ (prefix-weaken-val ext x)
prefix-weaken-cv ext (cv < c >) = prefix-weaken-cv ext cv < c >
prefix-weaken-cv ext < cv , cv₁ > =
  < prefix-weaken-cv ext cv , prefix-weaken-cv ext cv₁ >

prefix-weaken-storeval  : ∀ {t} {Σ Σ' : StoreTyping} → Σ ⊑ₗ Σ'
  → StoreValue t Σ
  → StoreValue t Σ'
prefix-weaken-storeval ext (fromNormalValue (intro v t)) =
  fromNormalValue (intro (prefix-weaken-val ext v) t)
prefix-weaken-storeval ext (fromCastedValue (intro cv t)) =
  fromCastedValue (intro (prefix-weaken-cv ext cv) t)

lookup-store : ∀ {Σ t} → t ∈ Σ → Store Σ → StoreValue t Σ
lookup-store mem ν = lookup ν mem

update-store : ∀ {Σ t} → t ∈ Σ → NormalStoreValue t Σ → Store Σ → Store Σ
update-store ptr v μ = μ All[ ptr ]≔' fromNormalValue v

store : ∀ {Σ A} {v : Σ ∣ ∅ ⊢ A} → Value v → Store Σ → Store (Σ ∷ʳ A)
store {Σ} {A = A} v ν =
  (map (prefix-weaken-storeval ext) ν) all-∷ʳ (prefix-weaken-storeval ext v')
  where
    v' = fromNormalValue (toNormalStoreValue v)
    ext = ∷ʳ-⊒ A Σ

-- an evidence that a store does not contain any casted values i.e. a normal store
data NormalStore : ∀ {Σ} → Store Σ → Set where

  Z :
    NormalStore All.[]

  S : ∀ {Σ A} {ν : Store Σ} {v : Σ ∣ ∅ ⊢ A}
    → NormalStore ν
    → (V : Value v)
    → NormalStore (store V ν)

∈⟹T : ∀ {Σ A} → A ∈ Σ → Type
∈⟹T {A = A} _ = A

ref⟹T : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : Value v) → Type
ref⟹T (V-addr mem _) = ∈⟹T mem

ref⟹∈ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : Value v) → ref⟹T V ∈ Σ
ref⟹∈ (V-addr mem _) = mem

ref⟹⊑ : ∀ {Σ Γ A} {v : Σ ∣ Γ ⊢ Ref A} → (V : Value v) → ref⟹T V ⊑ A
ref⟹⊑ (V-addr _ prec) = prec

store-lookup-v : ∀ {Σ t} → t ∈ Σ → Store Σ → Σ ∣ ∅ ⊢ t
store-lookup-v mem ν with lookup-store mem ν
... | fromNormalValue (intro {V = V} _ _) = V
... | fromCastedValue (intro {V = V} _ _) = V

store-lookup-v/ref : ∀ {Σ Γ B} {r : Σ ∣ Γ ⊢ Ref B}
  → (R : Value r) → Store Σ → Σ ∣ ∅ ⊢ ref⟹T R
store-lookup-v/ref (V-addr mem _) ν = store-lookup-v mem ν

store-lookup-rtti : ∀ {Σ t} → t ∈ Σ → Store Σ → Type
store-lookup-rtti mem ν with lookup-store mem ν
... | fromNormalValue (intro _ ty) = Ty⇓ ty
... | fromCastedValue (intro _ ty) = Ty⇓ ty

store-lookup-rtti/ref : ∀ {Σ Γ T}
                          {v : Σ ∣ Γ ⊢ Ref T}
  → (R : Value v) → Store Σ → Type
store-lookup-rtti/ref (V-addr mem _) ν = store-lookup-rtti mem ν

ref-static-type : ∀ {Σ Γ B} {r : Σ ∣ Γ ⊢ Ref B}
  → (R : Value r) → static B → ref⟹T R ≡ B
ref-static-type (V-addr _ prec) x = ⊑-respect-static prec x

μ-static-lookup : ∀ {Σ Γ B} {r : Σ ∣ Γ ⊢ Ref B}
  → (R : Value r) → static B → Store Σ → Σ ∣ ∅ ⊢ B
μ-static-lookup r x ν with ref⟹T r | ref-static-type r x | store-lookup-v/ref r ν
... | _ | refl | res = res

μ-static-update : ∀ {Σ B}
             {r : Σ ∣ ∅ ⊢ Ref B}
  → (R : Value r)
  → static B
  → Store Σ
  → ∀ {v : Σ ∣ ∅ ⊢ B}
  → Value v
  → Store Σ
μ-static-update r@(V-addr mem prec) x μ v =
  update-store mem (subst (λ x₁ → x₁) (helper r x) (toNormalStoreValue v)) μ
   where
     helper : ∀ {Σ Γ B} {r : Σ ∣ Γ ⊢ Ref B}
       → (R : Value r)
       → static B
       → NormalStoreValue B Σ ≡ NormalStoreValue (ref⟹T R) Σ
     helper r x rewrite ref-static-type r x = refl

update-evolvingstore : ∀ {Σ t} → t ∈ Σ → EvolvingStoreValue t Σ → Store Σ → Store Σ
update-evolvingstore ptr v μ = μ All[ ptr ]≔' fromCastedValue v

toEvolvingStoreValue : ∀ {Σ A} {v : Σ ∣ ∅ ⊢ A} → CastedValue v → EvolvingStoreValue A Σ
toEvolvingStoreValue {A = A} v = intro v (Type⇑ A)

ν-update : ∀ {Σ t}
  → t ∈ Σ
  → Store Σ
  → ∀ {v : Σ ∣ ∅ ⊢ t}
  → CastedValue v
  → Store Σ
ν-update mem ν v = update-evolvingstore mem (toEvolvingStoreValue v) ν

ν-update/ref : ∀ {Σ Γ B}
             {r : Σ ∣ Γ ⊢ Ref B}
  → (R : Value r)
  → Store Σ
  → ∀ {v : Σ ∣ ∅ ⊢ (ref⟹T R)}
  → CastedValue v
  → Store Σ
ν-update/ref (V-addr mem _) ν v = ν-update mem ν v

-- Definition 1 (Precision relation on heap typings)
_⊑ₕ_ : (Σ Σ' : StoreTyping) → Set
_⊑ₕ_ Σ' Σ = Pointwise _⊑_ Σ' Σ

⊑ₕ-refl : ∀ {Σ} → Σ ⊑ₕ Σ
⊑ₕ-refl = pw-refl ⊑-refl

⊑ₕ-trans : Transitive _⊑ₕ_
⊑ₕ-trans = pw-trans ⊑-trans

-- Views

data _,_∈_ (t' t : Type) : ∀ {Σ' Σ} → Σ' ⊑ₕ Σ → Set where

  here : ∀ {Σ' Σ} {t'⊑t : t' ⊑ t} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ}
      -------------------------
    → _,_∈_ t' t (t'⊑t ∷ Σ'⊑ₕΣ)

  there : ∀ {x y Σ' Σ} {y⊑x : y ⊑ x} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ}
    → _,_∈_ t' t Σ'⊑ₕΣ
      ------------------------
    → _,_∈_ t' t (y⊑x ∷ Σ'⊑ₕΣ)

data _⊑∈_ (t : Type) : ∀ {Σ' Σ} → Σ' ⊑ₕ Σ → Set where

  here : ∀ {Σ' Σ t'} {t'⊑t : t' ⊑ t} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ}
      -------------------
    → t ⊑∈ (t'⊑t ∷ Σ'⊑ₕΣ)

  there : ∀ {x y Σ' Σ} {y⊑x : y ⊑ x} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ}
    → t ⊑∈ Σ'⊑ₕΣ
      ------------------
    → t ⊑∈ (y⊑x ∷ Σ'⊑ₕΣ)

⊒-⊒ₕ : ∀ {Σ' Σ t' t} {prec : Σ' ⊑ₕ Σ} →  _,_∈_ t' t prec → t' ⊑ t
⊒-⊒ₕ {prec = x∼y ∷ _} here = x∼y
⊒-⊒ₕ (there mem) = ⊒-⊒ₕ mem

∈-⊒ₕ : ∀ {Σ' Σ t} {prec : Σ' ⊑ₕ Σ} → t ⊑∈ prec → ∃[ t' ] _,_∈_ t' t prec
∈-⊒ₕ here = -, here
∈-⊒ₕ (there mem) with ∈-⊒ₕ mem
... | fst `, snd = fst `, there snd

pw-lift-∈ : ∀ {Σ' Σ t} → (prec : Σ' ⊑ₕ Σ) → t ∈ Σ → t ⊑∈ prec
pw-lift-∈ (x∼y ∷ prec) (here refl) = here
pw-lift-∈ (x∼y ∷ prec) (there mem) = there (pw-lift-∈ prec mem)

∈⇒⊑ₕ∈ : ∀ {Σ' Σ t} → (prec : Σ' ⊑ₕ Σ) → t ∈ Σ → ∃[ t' ] _,_∈_ t' t prec
∈⇒⊑ₕ∈ prec mem = ∈-⊒ₕ (pw-lift-∈ prec mem)

⊑ₕ∈⇒∈ : ∀ {Σ' Σ t' t} {prec : Σ' ⊑ₕ Σ}
  → _,_∈_ t' t prec → t' ∈ Σ'
⊑ₕ∈⇒∈ here = here refl
⊑ₕ∈⇒∈ (there mem) = there (⊑ₕ∈⇒∈ mem)

-- Lemma 1 (Strengthening wrt. the heap typing)
typeprecise-strenthen-expr : ∀ {Σ Σ' Γ A} → Σ' ⊑ₕ Σ
  → Σ  ∣ Γ ⊢ A
  → Σ' ∣ Γ ⊢ A
typeprecise-strenthen-expr _    (` x) = ` x
typeprecise-strenthen-expr prec (ƛ e) = ƛ typeprecise-strenthen-expr prec e
typeprecise-strenthen-expr prec (ƛₚ e c) = ƛₚ (typeprecise-strenthen-expr prec e) c
typeprecise-strenthen-expr prec (e · e₁) =
  typeprecise-strenthen-expr prec e · typeprecise-strenthen-expr prec e₁
typeprecise-strenthen-expr _    `zero = `zero
typeprecise-strenthen-expr prec (`suc e) = `suc typeprecise-strenthen-expr prec e
typeprecise-strenthen-expr prec (case e e₁ e₂) =
  case (typeprecise-strenthen-expr prec e)
       (typeprecise-strenthen-expr prec e₁)
       (typeprecise-strenthen-expr prec e₂)
typeprecise-strenthen-expr prec (ref e) = ref typeprecise-strenthen-expr prec e
typeprecise-strenthen-expr prec (e `× e₁) =
  typeprecise-strenthen-expr prec e `× typeprecise-strenthen-expr prec e₁
typeprecise-strenthen-expr prec (π₁ e) = π₁ typeprecise-strenthen-expr prec e
typeprecise-strenthen-expr prec (π₂ e) = π₂ typeprecise-strenthen-expr prec e
typeprecise-strenthen-expr prec (addr mem prec') with ∈⇒⊑ₕ∈ prec mem
... | _ `, tt'∈prec = addr (⊑ₕ∈⇒∈ tt'∈prec) (⊑-trans (⊒-⊒ₕ tt'∈prec) prec')
typeprecise-strenthen-expr prec ((!ₛ e) x) =
  (!ₛ typeprecise-strenthen-expr prec e) x
typeprecise-strenthen-expr prec ((e :=ₛ e₁) x) =
  (typeprecise-strenthen-expr prec e :=ₛ typeprecise-strenthen-expr prec e₁) x
typeprecise-strenthen-expr prec (! e) = ! typeprecise-strenthen-expr prec e
typeprecise-strenthen-expr prec (e := e₁) =
  typeprecise-strenthen-expr prec e := typeprecise-strenthen-expr prec e₁
typeprecise-strenthen-expr _    unit = unit
typeprecise-strenthen-expr prec (e < x >) = typeprecise-strenthen-expr prec e < x >
typeprecise-strenthen-expr _    error = error

typeprecise-strenthen-val : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A} → (prec : Σ' ⊑ₕ Σ)
  → Value v
  → Value (typeprecise-strenthen-expr prec v)
typeprecise-strenthen-val prec (V-ƛ N) = V-ƛ (typeprecise-strenthen-expr prec N)
typeprecise-strenthen-val prec (V-ƛₚ e c) = V-ƛₚ (typeprecise-strenthen-val prec e) c
typeprecise-strenthen-val _    V-zero = V-zero
typeprecise-strenthen-val prec (V-suc v) = V-suc (typeprecise-strenthen-val prec v)
typeprecise-strenthen-val _    V-unit = V-unit
typeprecise-strenthen-val prec (V-addr mem prec') with ∈⇒⊑ₕ∈ prec mem
... | _ `, tt'∈prec = V-addr (⊑ₕ∈⇒∈ tt'∈prec) (⊑-trans (⊒-⊒ₕ tt'∈prec) prec')
typeprecise-strenthen-val prec (V-pair v v₁) = V-pair (typeprecise-strenthen-val prec v)
                                                 (typeprecise-strenthen-val prec v₁)
typeprecise-strenthen-val prec (V-inj v) = V-inj (typeprecise-strenthen-val prec v)

typeprecise-strenthen-cv : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A} → (prec : Σ' ⊑ₕ Σ)
  → CastedValue v
  → CastedValue (typeprecise-strenthen-expr prec v)
typeprecise-strenthen-cv prec (v⇑ x) = v⇑ typeprecise-strenthen-val prec x
typeprecise-strenthen-cv prec (cv < c >) = typeprecise-strenthen-cv prec cv < c >
typeprecise-strenthen-cv prec < cv , cv₁ > = < typeprecise-strenthen-cv prec cv ,
                                               typeprecise-strenthen-cv prec cv₁ >

typeprecise-strenthen-evolvingstoreval : ∀ {Σ Σ' t} → Σ' ⊑ₕ Σ
  → EvolvingStoreValue t Σ
  → EvolvingStoreValue t Σ'
typeprecise-strenthen-evolvingstoreval prec (intro cv ty) =
  intro (typeprecise-strenthen-cv prec cv) ty

typeprecise-strenthen-storeval : ∀ {Σ Σ' t} → Σ' ⊑ₕ Σ
  → StoreValue t Σ
  → StoreValue t Σ'
typeprecise-strenthen-storeval prec (fromNormalValue (intro v ty)) =
  fromNormalValue (intro (typeprecise-strenthen-val prec v) ty)
typeprecise-strenthen-storeval prec (fromCastedValue (intro cv ty)) =
  fromCastedValue (intro (typeprecise-strenthen-cv prec cv) ty)

all-⊑ₕ : ∀ {Σ Σ' : StoreTyping}
  → All (λ ty → StoreValue ty Σ') Σ
  → Σ' ⊑ₕ Σ
  → All (λ ty → StoreValue ty Σ') Σ'
all-⊑ₕ ν prec = pw-map' f prec ν
  where
    f : ∀ {t' t : Type} {Σ} → t' ⊑ t → StoreValue t Σ → StoreValue t' Σ
    f {t'} {t} prec (fromNormalValue (intro v ty)) =
      fromCastedValue (intro ((v⇑ v) < coerce t t' >) (Type⇑ t'))
    f {t'} {t} prec (fromCastedValue (intro cv ty)) =
      fromCastedValue (intro (cv < coerce t t' >) (Type⇑ t'))

    -- a modified version of pw-map where the relation is anti-symmetric and
    -- points left
    pw-map' : ∀ {a ℓ}{A : Set a}{_∼_ : Rel A ℓ} {l m p}{P : A → Set p}
      → (∀ {a b} → a ∼ b → P b → P a) → Pointwise _∼_ m l → All P l → All P m
    pw-map' f Pointwise.[] All.[] = All.[]
    pw-map' f (x∼y ∷ r) (px All.∷ xs) = f x∼y px All.∷ pw-map' f r xs

Σ-cast : ∀ {Σ T} → T ∈ Σ → Type → StoreTyping
Σ-cast {x ∷ Σ} (here refl) t = t ∷ Σ
Σ-cast {x ∷ Σ} (there mem) t = x ∷ Σ-cast mem t

Σ-cast⟹∈ : ∀ {Σ Γ T T'}
             {v : Σ ∣ Γ ⊢ Ref T}
  → (R : Value v)
  → T' ∈ Σ-cast (ref⟹∈ R) T'
Σ-cast⟹∈ {T' = T'} (V-addr mem _) = helper mem T'
  where
    helper : ∀ {Σ t} → (mem : t ∈ Σ) → (t' : Type) → t' ∈ Σ-cast mem t'
    helper (here refl) t' = here refl
    helper (there mem) t' = there (helper mem t')

ref-rtti-preserves-Σ : ∀ {Σ Γ T}
                         {v : Σ ∣ Γ ⊢ Ref T}
  → (R : Value v)
  → (ν : Store Σ)
  → (store-lookup-rtti/ref R ν) ≡ (ref⟹T R)
ref-rtti-preserves-Σ (V-addr mem prec) ν with lookup-store mem ν
... | fromNormalValue (intro _ _) = refl
... | fromCastedValue (intro _ _) = refl

build-prec : ∀ {Σ t t'}
      → (mem : t ∈ Σ)
      → t' ⊑ t
      → (Σ-cast mem t') ⊑ₕ Σ
build-prec (here refl) prec = prec ∷ ⊑ₕ-refl
build-prec (there mem) prec = ⊑-refl ∷ build-prec mem prec

-- FIXME: There is a typo in the paper in this part when it says Σ' ⊢ ν
-- Corollary 1 (Monotonic heap update).
ν-cast : ∀ {Σ Γ T t'} {v : Σ ∣ Γ ⊢ Ref T}
  → (R : Value v)
  → (ν : Store Σ)
  → t' ⊑ (store-lookup-rtti/ref R ν)
  → Store (Σ-cast (ref⟹∈ R) t')
ν-cast {Σ} {t' = t'} r@(V-addr mem _) ν tprec =
  all-⊑ₕ (map (typeprecise-strenthen-storeval prec) ν) prec
  where
    prec : (Σ-cast (ref⟹∈ r) t') ⊑ₕ Σ
    prec rewrite (ref-rtti-preserves-Σ r ν) = build-prec mem tprec

ref-ν⟹∈ : ∀ {Σ Γ T} {v : Σ ∣ Γ ⊢ Ref T}
  → (R : Value v) → (ν : Store Σ) → store-lookup-rtti/ref R ν ∈ Σ
ref-ν⟹∈ r@(V-addr mem _) ν rewrite (ref-rtti-preserves-Σ r ν) = mem

ref-ν⟹⊑ : ∀ {Σ Γ T} {v : Σ ∣ Γ ⊢ Ref T}
  → (R : Value v) → (ν : Store Σ) → store-lookup-rtti/ref R ν ⊑ T
ref-ν⟹⊑ r@(V-addr _ prec) ν rewrite (ref-rtti-preserves-Σ r ν) = prec

-- The store can be more precise or bigger. Because this is a small-step
-- reduction semantics, this simple relation is enough for a single step
data StoreTypingProgress (Σ Σ' : StoreTyping) : Set where

  from⊑ₕ : Σ' ⊑ₕ Σ → StoreTypingProgress Σ Σ'

  from⊑ₗ : Σ ⊑ₗ Σ' → StoreTypingProgress Σ Σ'

data SameStoreValueType {A} :
  ∀ {Σ Σ'} → Σ' ⊑ₕ Σ → A ∈ Σ → A ∈ Σ' → Set where

  here : ∀ {Σ' Σ} {A⊑ : A ⊑ A} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ}
    → SameStoreValueType (A⊑ ∷ Σ'⊑ₕΣ) (here refl) (here refl)

  there : ∀ {Σ' Σ x y}
            {y⊑x : y ⊑ x} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ}
            {mem : A ∈ Σ} {mem' : A ∈ Σ'}
    → SameStoreValueType Σ'⊑ₕΣ mem mem'
    → SameStoreValueType (y⊑x ∷ Σ'⊑ₕΣ) (there mem) (there mem')

data DistinctStoreValueTypes {A B} :
  ∀ {Σ Σ'} → Σ' ⊑ₕ Σ → A ∈ Σ → B ∈ Σ' → Set where

  here : ∀ {Σ' Σ} {B⊑A : B ⊑ A} {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ}
    → A ≢ B
    → DistinctStoreValueTypes (B⊑A ∷ Σ'⊑ₕΣ) (here refl) (here refl)

  there : ∀ {Σ' Σ x y}
            {y⊑x : y ⊑ x}
            {Σ'⊑ₕΣ : Σ' ⊑ₕ Σ}
            {mem : A ∈ Σ} {mem' : B ∈ Σ'}
    → DistinctStoreValueTypes Σ'⊑ₕΣ mem mem'
    → DistinctStoreValueTypes (y⊑x ∷ Σ'⊑ₕΣ) (there mem) (there mem')

embed-expr-with-Σ : ∀ {Σ Σ' Γ A} → StoreTypingProgress Σ Σ'
  → Σ  ∣ Γ ⊢ A
  → Σ' ∣ Γ ⊢ A
embed-expr-with-Σ (from⊑ₕ prec) e = typeprecise-strenthen-expr prec e
embed-expr-with-Σ (from⊑ₗ ext) e = prefix-weaken-expr ext e

embed-val-with-Σ : ∀ {Σ Σ' Γ A} {v : Σ ∣ Γ ⊢ A} → (ext : StoreTypingProgress Σ Σ')
  → Value v
  → Value (embed-expr-with-Σ ext v)
embed-val-with-Σ (from⊑ₕ prec) v = typeprecise-strenthen-val prec v
embed-val-with-Σ (from⊑ₗ ext) v = prefix-weaken-val ext v

StoreTypingProgress-refl : ∀ {Σ} → StoreTypingProgress Σ Σ
StoreTypingProgress-refl = from⊑ₕ ⊑ₕ-refl
