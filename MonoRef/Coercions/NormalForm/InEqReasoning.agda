module MonoRef.Coercions.NormalForm.InEqReasoning where

open import Data.Nat using (ℕ ; suc ; _*_ ; _+_ ; _≤_ ; _⊔_)
open import Data.Nat.Properties
open ≤-Reasoning
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong₂)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver


2≤1+2*a+b+3 : ∀ {a b} → 2 ≤ 1 + (2 * a) + b + 3
2≤1+2*a+b+3 {a}{b} =
  begin
    2
      ≤⟨ n≤m+n ((1 + (2 * a) + b) + 1) _ ⟩
    1 + ((((2 * a) + b) + 1) + 2)
      ≡⟨ cong₂ (_+_) (refl{x = 1}) (+-assoc ((2 * a) + b) 1 2) ⟩
    1 + (((2 * a) + b) + 3)
  ∎

2≤1+2*a+b+2+2*c+1 : ∀ {a b c} → 2 ≤ 1 + 2 * a + b + (2 + (2 * c + 1))
2≤1+2*a+b+2+2*c+1 {a}{b}{c} = 
  begin
    1 + 1
      ≤⟨ +-mono-≤ (m≤m+n 1 (2 * a + b)) (m≤m+n 1 (1 + (2 * c + 1))) ⟩
    1 + 2 * a + b + (2 + (2 * c + 1))
  ∎

1+a≤2*1+b+1+a : ∀ {a b} → 1 + a ≤ 2 * (1 + b + (1 + a))
1+a≤2*1+b+1+a {a}{b} = 
  begin
    1 + a
      ≤⟨ n≤m+n (1 + b) _ ⟩
    1 + b + (1 + a)
      ≤⟨ m≤m+n _ (1 + b + (1 + a) + 0) ⟩
    1 + b + (1 + a) + (1 + b + (1 + a) + 0)
  ∎

1≤2*a+b : ∀ {a b} → 1 ≤ a → 1 ≤ 2 * (a + b)
1≤2*a+b {a}{b} 1≤a =
  begin
    1
      ≤⟨ 1≤a ⟩
    a
      ≤⟨ m≤m+n _ (b + (a + b + 0)) ⟩
    a + (b + (a + b + 0))
      ≡⟨ sym (+-assoc a b (a + b + 0)) ⟩
    a + b + (a + b + 0)
  ∎

3≤1+2*a+b : ∀ {a b} → 1 ≤ a → 1 ≤ b → 3 ≤ 1 + 2 * (a + b)
3≤1+2*a+b {a} {b} 1≤a 1≤b =
  begin
    3
      ≤⟨ +-monoʳ-≤ 1 (+-mono-≤ 1≤a 1≤b) ⟩
    1 + a + b
      ≤⟨ +-monoʳ-≤ 1 (m≤m+n _ (a + b + 0)) ⟩
    1 + 2 * (a + b)
  ∎

1+2*a+c+1+2*b+d≤n⇒2*a+b+d≤n : ∀ {a b c d n}
  → 1 + (2 * a + c + (1 + (2 * b + d))) ≤ n
  → 2 * (a + b) + d ≤ n
1+2*a+c+1+2*b+d≤n⇒2*a+b+d≤n {a} {b} {c} {d} {n} m =
  begin
    2 * (a + b) + d
      ≡⟨ solve 4 (λ a b c d → con 2 :* (a :+ b) :+ d
                                :=
                              con 2 :* a :+ (con 2 :* b :+ d))
               refl a b c d ⟩
    2 * a + (2 * b + d)
      ≤⟨ +-monoʳ-≤ _ (n≤1+n _) ⟩
    2 * a + (1 + (2 * b + d))
      ≤⟨ +-monoˡ-≤ (1 + (2 * b + d)) (m≤m+n _ c) ⟩
    2 * a + c + (1 + (2 * b + d))
      ≤⟨ n≤m+n 1 _ ⟩
    1 + (2 * a + c + (1 + (2 * b + d)))
      ≤⟨ m ⟩
    n
  ∎

1+2*b+a+1+2*c+d≤n⇒a+2*b+c+d≤n : ∀ {a b c d n}
  → 1 + (2 * b) + a + (1 + (2 * c) + d) ≤ n → a + (2 * (b + c) + d) ≤ n
1+2*b+a+1+2*c+d≤n⇒a+2*b+c+d≤n {a} {b} {c} {d} {n} m =
  begin
    a + (2 * (b + c) + d)
      ≡⟨ solve 4 (λ a b c d → a :+ (con 2 :* (b :+ c) :+ d)
                                :=
                              con 2 :* b :+ a :+ (con 2 :* c :+ d))
               refl a b c d ⟩
    2 * b + a + (2 * c + d)
      ≤⟨ +-monoʳ-≤ _ (n≤1+n _)  ⟩
    (2 * b + a) + (1 + 2 * c + d)
      ≤⟨ n≤m+n 1 _ ⟩
    1 + 2 * b + a + (1 + 2 * c + d)
      ≤⟨ m ⟩
    n
  ∎

1+a+b≡a+1+b : ∀ {a b} → 1 + (a + b) ≡ a + (1 + b)
1+a+b≡a+1+b {a} {b} =
  solve 2 (λ a b → con 1 :+ (a :+ b) := (a :+ (con 1 :+ b))) refl a b

a+1+b≤n⇒a+b≤n : ∀ {a b n} → a + (1 + b) ≤ n → a + b ≤ n
a+1+b≤n⇒a+b≤n {a} {b} {n} m =
  begin
    a + b
      ≤⟨ +-monoʳ-≤ _ (n≤1+n _) ⟩
    a + (1 + b)
      ≤⟨ m ⟩
    n
  ∎

1+a+1+b≤n⇒a+b≤n : ∀ {a b n} → 1 + a + (1 + b) ≤ n → a + b ≤ n
1+a+1+b≤n⇒a+b≤n {a} {b} {n} m =
  begin
    a + b
      ≤⟨ +-monoʳ-≤ _ (n≤1+n _) ⟩
    a + (1 + b)
      ≤⟨ n≤1+n _ ⟩
    1 + a + (1 + b)
      ≤⟨ m ⟩
    n
  ∎

1+a+b+c≡b+1+a+c : ∀ {a b c} → 1 + (a + (b + c)) ≡ b + (1 + (a + c))
1+a+b+c≡b+1+a+c {a} {b} {c} =
  solve 3 (λ a b c → con 1 :+ (a :+ (b :+ c)) := b :+ (con 1 :+ (a :+ c))) refl a b c

c+2*b+a+d≤1+2*b+c+1+2*a+d : ∀ {a b c d}
  → c + (2 * (b + a) + d)
  ≤ 1 + (2 * b + c + (1 + (2 * a + d)))
c+2*b+a+d≤1+2*b+c+1+2*a+d {a} {b} {c} {d} =
  begin
    c + (2 * (b + a) + d)
      ≡⟨ solve 4 (λ a b c d → c :+ (b :+ a :+ (b :+ a :+ con 0) :+ d)
                                :=
                              con 2 :* b :+ c :+ (con 2 :* a :+ d))
               refl a b c d ⟩
    (2 * b + c) + (2 * a + d)
      ≤⟨ +-mono-≤ (n≤1+n _) (n≤1+n _) ⟩
    1 + (2 * b + c + (1 + (2 * a + d)))
  ∎

1+a+b+c+d≤1+a+c+1+b+d : ∀ {a b c d}
  → suc (a + b + (c + d)) ≤ suc (a + c + suc (b + d))
1+a+b+c+d≤1+a+c+1+b+d {a} {b} {c} {d} =
  begin
    suc (a + b + (c + d))
      ≡⟨ solve 4 (λ a b c d → con 1 :+ (a :+ b :+ (c :+ d))
                                :=
                              (a :+ c :+ (con 1 :+ (b :+ d))))
               refl a b c d ⟩
    a + c + suc (b + d)
      ≤⟨ n≤1+n _ ⟩
    suc (a + c + suc (b + d))
  ∎

1+b+a+c+d≤1+a+c+1+b+d : ∀ {a b c d}
  → suc (b + a + (c + d)) ≤ suc (a + c + suc (b + d))
1+b+a+c+d≤1+a+c+1+b+d {a} {b} {c} {d} =
  begin
    suc (b + a + (c + d))
      ≡⟨ solve 4 (λ a b c d → con 1 :+ (b :+ a :+ (c :+ d))
                                :=
                              (a :+ c :+ (con 1 :+ (b :+ d))))
               refl a b c d ⟩
    (a + c + suc (b + d))
      ≤⟨ n≤1+n _ ⟩
    suc (a + c + suc (b + d))
  ∎

3+b≤2+a+1+b+1+a+1+b+0 : ∀ {a b} → 3 + b ≤ 2 + (a + suc b + suc (a + suc b + 0))
3+b≤2+a+1+b+1+a+1+b+0 {a} {b} =
  begin
    3 + b                         ≤⟨ m≤m+n _ (suc (a + suc b + 0))  ⟩
    (3 + b) + suc (a + suc b + 0) ≤⟨ +-monoˡ-≤ _ (+-monoʳ-≤ 2 (n≤m+n a _)) ⟩
    2 + (a + suc b + suc (a + suc b + 0))
  ∎

4+a+b+a+b+0+1+c+d+c+d+0≤2+a+c+1+b+d+1+a+c+1+b+d+0 : ∀ {a b c d}
  → 4 + (a + b + (a + b + 0) + (1 + (c + d + (c + d + 0))))
  ≡ 2 + (a + c + (1 + (b + d)) + (1 + (a + c + (1 + (b + d)) + 0)))
4+a+b+a+b+0+1+c+d+c+d+0≤2+a+c+1+b+d+1+a+c+1+b+d+0 {a} {b} {c} {d} =       
  solve 4 (λ a b c d → con 4 :+ (a :+ b :+ (a :+ b :+ con 0) :+ (con 1 :+ (c :+ d :+ (c :+ d :+ con 0))))
                                :=
                              con 2 :+ (a :+ c :+ (con 1 :+ (b :+ d)) :+ (con 1 :+ (a :+ c :+ (con 1 :+ (b :+ d)) :+ con 0))))
                 refl a b c d

2+a+b+a+b+0+1+c+d+c+d+0≤1+a+c+1+b+d+1+a+c+1+b+d+0 : ∀ {a b c d}
  → 2 + (a + b + (a + b + 0) + (1 + (c + d + (c + d + 0))))
  ≤ 1 + (a + c + (1 + (b + d)) + (1 + (a + c + (1 + (b + d)) + 0)))
2+a+b+a+b+0+1+c+d+c+d+0≤1+a+c+1+b+d+1+a+c+1+b+d+0{a}{b}{c}{d} =
  begin
    2 + (a + b + (a + b + 0) + (1 + (c + d + (c + d + 0))))
      ≡⟨ solve 4 (λ a b c d → con 2 :+ (a :+ b :+ (a :+ b :+ con 0) :+ (con 1 :+ (c :+ d :+ (c :+ d :+ con 0))))
                          :=
                        (a :+ c :+ (con 1 :+ (b :+ d)) :+ (con 1 :+ (a :+ c :+ (con 1 :+ (b :+ d)) :+ con 0))))
               refl a b c d ⟩
    a + c + (1 + (b + d)) + (1 + (a + c + (1 + (b + d)) + 0))
      ≤⟨ n≤1+n _ ⟩
    1 + a + c + (1 + (b + d)) + (1 + (a + c + (1 + (b + d)) + 0))
  ∎

4+b+a+b+a+0+1+c+d+c+d+0≤2+a+c+1+b+d+1+a+c+1+b+d+0 : ∀ {a b c d}
  → 4 + (b + a + (b + a + 0) + (1 + (c + d + (c + d + 0))))
  ≡ 2 + (a + c + (1 + (b + d)) + (1 + (a + c + (1 + (b + d)) + 0)))
4+b+a+b+a+0+1+c+d+c+d+0≤2+a+c+1+b+d+1+a+c+1+b+d+0 {a} {b} {c} {d} =
  solve 4 (λ a b c d → con 4 :+ (b :+ a :+ (b :+ a :+ con 0) :+ (con 1 :+ (c :+ d :+ (c :+ d :+ con 0))))
                          :=
                       con 2 :+ (a :+ c :+ (con 1 :+ (b :+ d)) :+ (con 1 :+ (a :+ c :+ (con 1 :+ (b :+ d)) :+ con 0))))
                 refl a b c d

2+b+a+b+a+0+1+c+d+c+d+0≤1+a+c+1+b+d+1+a+c+1+b+d+0 : ∀ {a b c d}
  → 2 + (b + a + (b + a + 0) + (1 + (c + d + (c + d + 0))))
  ≤ 1 + (a + c + (1 + (b + d)) + (1 + (a + c + (1 + (b + d)) + 0)))
2+b+a+b+a+0+1+c+d+c+d+0≤1+a+c+1+b+d+1+a+c+1+b+d+0{a}{b}{c}{d} =
  begin
    2 + (b + a + (b + a + 0) + (1 + (c + d + (c + d + 0))))
      ≡⟨ solve 4 (λ a b c d → con 2 :+ (b :+ a :+ (b :+ a :+ con 0) :+ (con 1 :+ (c :+ d :+ (c :+ d :+ con 0))))
                          :=
                        (a :+ c :+ (con 1 :+ (b :+ d)) :+ (con 1 :+ (a :+ c :+ (con 1 :+ (b :+ d)) :+ con 0))))
               refl a b c d ⟩
    a + c + (1 + (b + d)) + (1 + (a + c + (1 + (b + d)) + 0))
      ≤⟨ n≤1+n _ ⟩
    1 + a + c + (1 + (b + d)) + (1 + (a + c + (1 + (b + d)) + 0))
  ∎

2+2*c+1≤1+c+1+c+1 : ∀{c} →  2 + (2 * c + 1) ≤ 1 + (c + 1 + (c + 1 + 0))
2+2*c+1≤1+c+1+c+1 {c} =
  begin
    1 + (1 + ((c + (c + 0)) + 1))
      ≡⟨ solve 1 (λ c → con 2 :+ (con 2 :* c :+ con 1)
                          :=
                        con 1 :+ (c :+ con 1 :+ (c :+ con 1 :+ con 0)))
               refl c ⟩
    1 + ((c + 1) + ((c + 1) + 0))
  ∎

1+2*c+2≤2+c+1+c+0 : ∀ {c} → 1 + (2 * c + 2) ≤ 2 + (c + suc (c + 0))
1+2*c+2≤2+c+1+c+0 {c} =
  begin
    1 + (c + (c + 0) + 2)
      ≡⟨ solve 1 (λ c → con 1 :+ (con 2 :* c :+ con 2)
                          :=
                        con 2 :+ (c :+ (con 1 :+ (c :+ con 0))))
               refl c ⟩
    2 + (c + suc (c + 0))
  ∎

1+a+c+1+b+d≤n⇒a+b≤n : ∀ {a b c d n} → 1 + a + c + (1 + b + d) ≤ n → a + b ≤ n
1+a+c+1+b+d≤n⇒a+b≤n {a}{b}{c}{d}{n} m =
  begin
    a + b               ≤⟨ +-monoʳ-≤ _ (m≤m+n b _) ⟩
    a + (b + d)         ≤⟨ +-mono-≤ (m≤m+n _ c) (n≤1+n _) ⟩
    a + c + (1 + b + d) ≤⟨ n≤1+n _ ⟩
    1 + a + c + (1 + b + d) ≤⟨ m ⟩
    n
  ∎

1+a+c+1+b+d≤n⇒b+a≤n : ∀ {a b c d n} → 1 + a + c + (1 + b + d) ≤ n → b + a ≤ n
1+a+c+1+b+d≤n⇒b+a≤n {a}{b}{c}{d}{n} m =
  begin
    b + a ≡⟨ +-comm b a ⟩
    a + b ≤⟨ 1+a+c+1+b+d≤n⇒a+b≤n{a} m ⟩
    n
  ∎

1+c+a+1+d+b≤n⇒a+b≤n : ∀{a b c d n} → 1 + c + a + (1 + d + b) ≤ n → a + b ≤ n
1+c+a+1+d+b≤n⇒a+b≤n {a}{b}{c}{d}{n} m =
  begin
    a + b               ≤⟨ +-mono-≤ (n≤m+n c _) (n≤m+n (1 + d) _) ⟩
    c + a + (1 + d + b) ≤⟨ n≤1+n _ ⟩
    1 + c + a + (1 + d + b) ≤⟨ m ⟩
    n
  ∎

c+a+b≤n⇒a+b≤n : ∀ {a b c n} → c + a + b ≤ n → a + b ≤ n
c+a+b≤n⇒a+b≤n {a} {b} {c} {n} m =
  begin
    a + b       ≤⟨ n≤m+n c _ ⟩
    c + (a + b) ≡⟨ sym (+-assoc c _ _) ⟩
    c + a + b   ≤⟨ m ⟩
    n
  ∎

a+1+c+b≤n⇒a+b≤n : ∀ {a b c n} → a + (1 + c + b) ≤ n → a + b ≤ n
a+1+c+b≤n⇒a+b≤n {a}{b}{c}{n} m =
  begin
    a + b           ≤⟨ +-monoʳ-≤ _ (n≤m+n (1 + c) _) ⟩
    a + (1 + c + b) ≤⟨ m ⟩
    n
  ∎

1+b⊔a⊔c⊔d≤1+a⊔c⊔b⊔d : ∀ {a b c d}
  → suc (b ⊔ a ⊔ (c ⊔ d)) ≤ suc (a ⊔ c ⊔ (b ⊔ d))
1+b⊔a⊔c⊔d≤1+a⊔c⊔b⊔d {a} {b} {c} {d} =
  begin
    suc ((b ⊔ a) ⊔ (c ⊔ d))
       ≤⟨ +-monoʳ-≤ 1 (≤-reflexive (⊔-assoc b _ _)) ⟩
    suc (b ⊔ (a ⊔ (c ⊔ d)))
       ≤⟨ +-monoʳ-≤ 1 (⊔-monoʳ-≤ b (≤-reflexive (sym (⊔-assoc a c d))) ) ⟩
    suc (b ⊔ ((a ⊔ c) ⊔ d))
       ≤⟨ +-monoʳ-≤ 1 (⊔-monoʳ-≤ b (≤-reflexive (⊔-comm _ d)) ) ⟩
    suc (b ⊔ (d ⊔ (a ⊔ c)))
       ≤⟨ +-monoʳ-≤ 1 (≤-reflexive (sym (⊔-assoc b d _))) ⟩
    suc ((b ⊔ d) ⊔ (a ⊔ c))
       ≤⟨ +-monoʳ-≤ 1 (≤-reflexive (⊔-comm _ (a ⊔ c))) ⟩
    suc (a ⊔ c ⊔ (b ⊔ d))
  ∎

1+a⊔b⊔c⊔d≤1+a⊔c⊔b⊔d : ∀ {a b c d}
  → suc (a ⊔ b ⊔ (c ⊔ d)) ≤ suc (a ⊔ c ⊔ (b ⊔ d))
1+a⊔b⊔c⊔d≤1+a⊔c⊔b⊔d {a} {b} {c} {d} =
  begin
    suc ((a ⊔ b) ⊔ (c ⊔ d))
       ≤⟨ +-monoʳ-≤ 1 (⊔-monoˡ-≤ _ (≤-reflexive (⊔-comm a b))) ⟩
    suc ((b ⊔ a) ⊔ (c ⊔ d))
       ≤⟨ 1+b⊔a⊔c⊔d≤1+a⊔c⊔b⊔d{a}{b} ⟩
    suc (a ⊔ c ⊔ (b ⊔ d))
  ∎
