module MonoRef.Coercions.NormalForm.InEqReasoning where

open import Data.Nat using (ℕ ; suc ; _*_ ; _+_ ; _≤_)
open import Data.Nat.Properties
open ≤-Reasoning
open import Relation.Binary.PropositionalEquality using (refl ; sym ; cong₂)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver


2+2*a+c+3+2*b+d≤n⇒3+a+b+a+b+0+1+d≤n : ∀ {a b c d n}
  → 2 + (2 * a + c + (3 + (2 * b + d))) ≤ n
  → 3 + (a + b + (a + b + 0) + suc d)   ≤ n
2+2*a+c+3+2*b+d≤n⇒3+a+b+a+b+0+1+d≤n {a} {b} {c} {d} {n} m =
  begin
    3 + (a + b + (a + b + 0) + suc d)
      ≡⟨ solve 4 (λ a b c d → con 3 :+ (a :+ b :+ (a :+ b :+ con 0) :+ (con 1 :+ d))
                                :=
                              con 1 :+ (con 2 :* a :+ (con 3 :+ (con 2 :* b :+ d))))
               refl a b c d ⟩
    1 + (2 * a + (3 + (2 * b + d)))
      ≤⟨ +-mono-≤ (n≤1+n 1) (+-monoˡ-≤ (3 + (2 * b + d)) (m≤m+n _ c)) ⟩
    2 + (2 * a + c + (3 + (2 * b + d)))
      ≤⟨ m ⟩
    n
  ∎

2+2*a+c+3+2*b+d≤n⇒1+c+3+a+b+a+b+0+1+d≤n : ∀ {a b c d n}
  → 2 + (2 * a + c + (3 + (2 * b + d))) ≤ n
  → suc (c + (3 + (a + b + (a + b + 0) + suc d))) ≤ n
2+2*a+c+3+2*b+d≤n⇒1+c+3+a+b+a+b+0+1+d≤n {a} {b} {c} {d} {n} m =
  begin
    suc (c + (3 + (a + b + (a + b + 0) + suc d)))
      ≡⟨ solve 4 (λ a b c d → con 1 :+ (c :+ (con 3 :+ (a :+ b :+ (a :+ b :+ con 0) :+ (con 1 :+ d))))
                                :=
                              con 2 :+ (con 2 :* a :+ c :+ (con 3 :+ (con 2 :* b :+ d))))
               refl a b c d ⟩
    2 + (2 * a + c + (3 + (2 * b + d)))
      ≤⟨ m ⟩
    n
  ∎

2≤1+a+2 : ∀ {a} → 2 ≤ suc (a + 2)
2≤1+a+2 {a} =
  begin
    2     ≤⟨ n≤m+n a _ ⟩
    a + 2 ≤⟨ n≤1+n _ ⟩
    suc (a + 2)
  ∎

4+2*a+b≤3+2*a+b+3 : ∀ {a b} →  4 + (2 * a + b) ≤ 3 + (2 * a + b + 3)
4+2*a+b≤3+2*a+b+3 {a} {b} =
  begin
    4 + (2 * a + b)
      ≡⟨ solve 2 (λ a b → con 4 :+ (con 2 :* a :+ b)
                            :=
                          con 1 :+ (con 2 :* a :+ b :+ con 3))
               refl a b ⟩
    1 + (2 * a + b + 3)
      ≤⟨ n≤m+n 2 _ ⟩
    3 + (2 * a + b + 3)
  ∎

2+a+b≤1+a+2+b : ∀ {a b} → 2 + (a + b) ≤ suc (a + (2 + b))
2+a+b≤1+a+2+b {a} {b} =
  begin
    2 + (a + b)
      ≡⟨ solve 2 (λ a b → con 2 :+ (a :+ b)
                            :=
                          a :+ (con 2 :+ b))
               refl a b ⟩
    a + (2 + b)
      ≤⟨ n≤1+n _ ⟩
    suc (a + (2 + b))
  ∎

4+2*a+b+c≤1+b+4+2*a+c : ∀ {a b c}
  → 4 + (2 * a + (b + c)) ≤ suc (b + (4 + (2 * a + c)))
4+2*a+b+c≤1+b+4+2*a+c {a} {b} {c} =
  begin
    4 + (2 * a + (b + c))
      ≡⟨ solve 3 (λ a b c → con 4 :+ (con 2 :* a :+ (b :+ c))
                                :=
                            b :+ (con 4 :+ (con 2 :* a :+ c)))
               refl a b c ⟩
    b + (4 + (2 * a + c))
      ≤⟨ n≤1+n _ ⟩
    suc (b + (4 + (2 * a + c)))
  ∎

1+c+3+b+a+b+a+0+1+d≤3+2*b+c+3+2*a+d : ∀ {a b c d}
  → suc (c + (3 + (b + a + (b + a + 0) + suc d)))
  ≤ 3 + (2 * b + c + (3 + (2 * a + d)))
1+c+3+b+a+b+a+0+1+d≤3+2*b+c+3+2*a+d {a} {b} {c} {d} =
  begin
    suc (c + (3 + (b + a + (b + a + 0) + suc d)))
      ≡⟨ solve 4 (λ a b c d → con 1 :+ (c :+ (con 3 :+ (b :+ a :+ (b :+ a :+ con 0) :+ (con 1 :+ d))))
                                :=
                              con 2 :+ (con 2 :* b :+ c :+ (con 3 :+ (con 2 :* a :+ d))))
               refl a b c d ⟩
    2 + (2 * b + c + (3 + (2 * a + d)))
      ≤⟨ n≤1+n _ ⟩
    3 + (2 * b + c + (3 + (2 * a + d)))
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

3+b≤4+a+1+b+1+a+1+b+0 : ∀ {a b} → 3 + b ≤ 4 + (a + suc b + suc (a + suc b + 0))
3+b≤4+a+1+b+1+a+1+b+0 {a} {b} =
  begin
    3 + b               ≤⟨ +-mono-≤ (n≤1+n 1) (n≤m+n 1 _) ⟩
    4 + suc b           ≤⟨ +-monoʳ-≤ 4 (n≤m+n _ _) ⟩
    4 + a + suc b       ≤⟨ +-monoʳ-≤ 4 (m≤m+n _ _) ⟩
    4 + (a + suc b + suc (a + suc b + 0))
  ∎

2+b≤4+a+1+b+1+a+1+b+0 : ∀ {a b} → 2 + b ≤ 4 + (a + suc b + suc (a + suc b + 0))
2+b≤4+a+1+b+1+a+1+b+0 = ≤⇒pred≤ 3+b≤4+a+1+b+1+a+1+b+0

6+a+b+a+b+0+3+c+d+c+d+0≤6+a+c+3+b+d+3+a+c+3+b+d+0 : ∀ {a b c d}
  → 6 + (a + b + (a + b + 0) + (3 + (c + d + (c + d + 0))))
  ≤ 6 + (a + c + (3 + (b + d)) + (3 + (a + c + (3 + (b + d)) + 0)))
6+a+b+a+b+0+3+c+d+c+d+0≤6+a+c+3+b+d+3+a+c+3+b+d+0 {a} {b} {c} {d} =       
  begin
    6 + (((a + b) + (a + b + 0)) + (3 + ((c + d) + ((c + d) + 0))))
      ≡⟨ solve 4 (λ a b c d → con 6 :+ (a :+ b :+ (a :+ b :+ con 0) :+ (con 3 :+ (c :+ d :+ (c :+ d :+ con 0))))
                                :=
                              con 6 :+ (a :+ c :+ (b :+ d) :+ (con 3 :+ (a :+ c :+ (b :+ d) :+ con 0))))
                 refl a b c d ⟩
    6 + (a + c + (b + d) + (3 + (a + c + (b + d) + 0)))
      ≤⟨ +-monoʳ-≤ 6 (+-monoˡ-≤ _ (+-monoʳ-≤ (a + c) (n≤m+n 3 _))) ⟩
    6 + (a + c + (3 + (b + d)) + (3 + (a + c + (b + d) + 0)))
      ≤⟨ +-monoʳ-≤ 6 (+-monoʳ-≤ _ (+-monoʳ-≤ 3 (+-monoˡ-≤ 0 (+-monoʳ-≤ (a + c) (n≤m+n 3 _))))) ⟩
    6 + (a + c + (3 + (b + d)) + (3 + (a + c + (3 + (b + d)) + 0)))
  ∎

5+a+b+a+b+0+3+c+d+c+d+0≤6+a+c+3+b+d+3+a+c+3+b+d+0 : ∀ {a b c d}
  → 5 + (a + b + (a + b + 0) + (3 + (c + d + (c + d + 0))))
  ≤ 6 + (a + c + (3 + (b + d)) + (3 + (a + c + (3 + (b + d)) + 0)))
5+a+b+a+b+0+3+c+d+c+d+0≤6+a+c+3+b+d+3+a+c+3+b+d+0{a} =
  ≤⇒pred≤ (6+a+b+a+b+0+3+c+d+c+d+0≤6+a+c+3+b+d+3+a+c+3+b+d+0{a})

6+b+a+b+a+0+3+c+d+c+d+0≤6+a+c+3+b+d+3+a+c+3+b+d+0 : ∀ {a b c d}
  → 6 + (b + a + (b + a + 0) + (3 + (c + d + (c + d + 0))))
  ≤ 6 + (a + c + (3 + (b + d)) + (3 + (a + c + (3 + (b + d)) + 0)))
6+b+a+b+a+0+3+c+d+c+d+0≤6+a+c+3+b+d+3+a+c+3+b+d+0 {a} {b} {c} {d} =       
  begin
    6 + (((b + a) + (b + a + 0)) + (3 + ((c + d) + ((c + d) + 0))))
      ≡⟨ solve 4 (λ a b c d → con 6 :+ (b :+ a :+ (b :+ a :+ con 0) :+ (con 3 :+ (c :+ d :+ (c :+ d :+ con 0))))
                                :=
                              con 6 :+ (a :+ c :+ (b :+ d) :+ (con 3 :+ (a :+ c :+ (b :+ d) :+ con 0))))
                 refl a b c d ⟩
    6 + (a + c + (b + d) + (3 + (a + c + (b + d) + 0)))
      ≤⟨ +-monoʳ-≤ 6 (+-monoˡ-≤ _ (+-monoʳ-≤ (a + c) (n≤m+n 3 _))) ⟩
    6 + (a + c + (3 + (b + d)) + (3 + (a + c + (b + d) + 0)))
      ≤⟨ +-monoʳ-≤ 6 (+-monoʳ-≤ _ (+-monoʳ-≤ 3 (+-monoˡ-≤ 0 (+-monoʳ-≤ (a + c) (n≤m+n 3 _))))) ⟩
    6 + (a + c + (3 + (b + d)) + (3 + (a + c + (3 + (b + d)) + 0)))
  ∎

5+b+a+b+a+0+3+c+d+c+d+0≤6+a+c+3+b+d+3+a+c+3+b+d+0 : ∀ {a b c d}
  → 5 + (b + a + (b + a + 0) + (3 + (c + d + (c + d + 0))))
  ≤ 6 + (a + c + (3 + (b + d)) + (3 + (a + c + (3 + (b + d)) + 0)))
5+b+a+b+a+0+3+c+d+c+d+0≤6+a+c+3+b+d+3+a+c+3+b+d+0{a} =
  ≤⇒pred≤ (6+b+a+b+a+0+3+c+d+c+d+0≤6+a+c+3+b+d+3+a+c+3+b+d+0{a})

4+2*c+1≤3+c+1+c+1 : ∀{c} →  4 + (2 * c + 1) ≤ 3 + (c + 1 + (c + 1 + 0))
4+2*c+1≤3+c+1+c+1 {c} =
  begin
    3 + (1 + ((c + (c + 0)) + 1))
      ≡⟨ solve 1 (λ c → con 4 :+ (con 2 :* c :+ con 1)
                          :=
                        con 3 :+ (c :+ con 1 :+ (c :+ con 1 :+ con 0)))
               refl c ⟩
    3 + ((c + 1) + ((c + 1) + 0))
  ∎

3+2*c+2≤4+c+1+c+0 : ∀ {c} → 3 + (2 * c + 2) ≤ 4 + (c + suc (c + 0))
3+2*c+2≤4+c+1+c+0 {c} =
  begin
    3 + (c + (c + 0) + 2)
      ≡⟨ solve 1 (λ c → con 3 :+ (con 2 :* c :+ con 2)
                          :=
                        con 4 :+ (c :+ (con 1 :+ (c :+ con 0))))
               refl c ⟩
    4 + (c + suc (c + 0))
  ∎

3+a+b+c+d≤3+a+c+3+b+d : ∀ {a b c d} → 3 + (a + b + (c + d)) ≤ 3 + (a + c + (3 + (b + d)))
3+a+b+c+d≤3+a+c+3+b+d {a}{b}{c}{d} =
  begin
    3 + (a + b + (c + d))
      ≡⟨ solve 4 (λ a b c d → con 3 :+ (a :+ b :+ (c :+ d))
                          :=
                        (a :+ c :+ (con 3 :+ (b :+ d))))
               refl a b c d ⟩
    a + c + (3 + (b + d))
      ≤⟨ n≤m+n 3 _ ⟩
    3 + (a + c + (3 + (b + d)))
  ∎


a+c+1+b+d≤n⇒a+b≤n : ∀ {a b c d n} → a + c + (1 + b + d) ≤ n → a + b ≤ n
a+c+1+b+d≤n⇒a+b≤n {a}{b}{c}{d}{n} m =
  begin
    a + b               ≤⟨ +-monoʳ-≤ _ (m≤m+n b _) ⟩
    a + (b + d)         ≤⟨ +-mono-≤ (m≤m+n _ c) (n≤1+n _) ⟩
    a + c + (1 + b + d) ≤⟨ m ⟩
    n
  ∎

a+c+1+b+d≤n⇒b+a≤n : ∀ {a b c d n} → a + c + (1 + b + d) ≤ n → b + a ≤ n
a+c+1+b+d≤n⇒b+a≤n {a}{b}{c}{d}{n} m =
  begin
    b + a ≡⟨ +-comm b a ⟩
    a + b ≤⟨ a+c+1+b+d≤n⇒a+b≤n{a} m ⟩
    n
  ∎

c+a+1+d+b≤n⇒a+b≤n : ∀{a b c d n} → c + a + (1 + d + b) ≤ n → a + b ≤ n
c+a+1+d+b≤n⇒a+b≤n {a}{b}{c}{d}{n} m =
  begin
    a + b               ≤⟨ +-mono-≤ (n≤m+n c _) (n≤m+n (1 + d) _) ⟩
    c + a + (1 + d + b) ≤⟨ m ⟩
    n
  ∎

1+c+a+b≤n⇒a+b≤n : ∀ {a b c n} → 1 + (c + a + b) ≤ n → a + b ≤ n
1+c+a+b≤n⇒a+b≤n {a} {b} {c} {n} m =
  begin
    a + b           ≤⟨ n≤m+n (1 + c) _ ⟩
    1 + c + (a + b) ≡⟨ sym (+-assoc (1 + c) _ _) ⟩
    suc (c + a + b) ≤⟨ m ⟩
    n
  ∎

a+2+b≤n⇒a+b≤n : ∀ {a b n} → a + (2 + b) ≤ n → a + b ≤ n
a+2+b≤n⇒a+b≤n {a}{b}{n} m =
  begin
    a + b       ≤⟨ +-monoʳ-≤ _ (n≤m+n 2 _) ⟩
    a + (2 + b) ≤⟨ m ⟩
    n
  ∎

a+3+c+b≤n⇒a+b≤n : ∀ {a b c n} → a + (3 + c + b) ≤ n → a + b ≤ n
a+3+c+b≤n⇒a+b≤n {a}{b}{c}{n} m =
  begin
    a + b           ≤⟨ +-monoʳ-≤ _ (n≤m+n (3 + c) _) ⟩
    a + (3 + c + b) ≤⟨ m ⟩
    n
  ∎
