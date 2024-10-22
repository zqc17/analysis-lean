import Mathlib.Tactic --#

/-! # 整数的定义
用自然数对$(a, b)$表示“形式差”$a-b$。-/
structure NatPair where
  a : ℕ
  b : ℕ

/-! 定义自然数对的等价关系$(a,b)\sim(c,d)\iff a+d=c+b$。-/
def NatPair.diffEq : NatPair → NatPair → Prop
  | ⟨a, b⟩, ⟨c, d⟩ => a + d = c + b

/-! 可以验证`NatPair.diffEq`是一个等价关系（书中习题4.1.1）。-/
instance instSetoidNatPair : Setoid NatPair where
  r := NatPair.diffEq
  iseqv := {
    refl := by
      intro x; unfold NatPair.diffEq; omega
    symm := by
      intro x y; unfold NatPair.diffEq; omega
    trans := by
      intro x y z; unfold NatPair.diffEq; omega
  }

theorem NatPair.eqv_iff_diff_eq {n m : NatPair} : n ≈ m ↔ diffEq n m :=
  Eq.to_iff rfl

/-! 定义整数为自然数对$(a,b)$关于等价关系`NatPair.diffEq`的商类型（书中定义4.1.1）。-/
def Integer := Quotient instSetoidNatPair

/-! # 加法、乘法
整数的加法、乘法定义如下（书中定义4.1.2）：
$$(a,b)+(c,d) := (a+c, b+d)$$
$$(a,b)\times(c,d) := (ac+bd,ad+bc)$$
在Lean中定义自然数对的加法、乘法如下：
-/
def NatPair.add : NatPair → NatPair → NatPair
  | ⟨a, b⟩, ⟨c, d⟩ => ⟨a + c, b + d⟩

def NatPair.mul : NatPair → NatPair → NatPair
  | ⟨a, b⟩, ⟨c, d⟩ => ⟨a * c + b * d, a * d + b * c⟩

/-! 可以验证上述加法、乘法与等价关系`NatPair.diffEq`是兼容的（书中引理4.1.3）。-/
theorem NatPair.add_congr :
    ∀ n n', n ≈ n' → ∀ m m', m ≈ m' → add n m ≈ add n' m' := by
  simp [eqv_iff_diff_eq]
  unfold NatPair.diffEq NatPair.add; simp
  omega

theorem NatPair.mul_congr_right (l n m : NatPair) :
    n ≈ m → (mul l n) ≈ (mul l m) := by
  simp [eqv_iff_diff_eq]
  unfold diffEq mul; simp; intro h
  calc
    _ = l.a * (n.a + m.b) + l.b * (m.a + n.b) := by ring
    _ = l.a * (m.a + n.b) + l.b * (n.a + m.b) := by rw [h]
    _ = _ := by ring

theorem NatPair.mul_congr_left (n m l: NatPair) :
    n ≈ m → (mul n l) ≈ (mul m l) := by
  simp [eqv_iff_diff_eq]
  unfold diffEq mul; simp; intro h
  calc
    _ = l.a * (n.a + m.b) + l.b * (m.a + n.b) := by ring
    _ = l.a * (m.a + n.b) + l.b * (n.a + m.b) := by rw [h]
    _ = _ := by ring

/-! 从而可以将`NatPair`上的加法、乘法迁移到`Integer`上。-/
def Integer.add : Integer → Integer → Integer :=
  Quotient.map₂
  NatPair.add
  NatPair.add_congr

def Integer.mul : Integer → Integer → Integer :=
  Quot.map₂
  NatPair.mul
  NatPair.mul_congr_right
  NatPair.mul_congr_left

infix:65 " + " => Integer.add
infix:70 " * " => Integer.mul

/-! 按照下述方式可以将自然数嵌入到整数中。-/
def ofNat : ℕ → Integer
  | n => Quotient.mk instSetoidNatPair ⟨n, 0⟩

/-! 并且这种嵌入可以保持加法、乘法。-/
example (n m : ℕ) : ofNat (n + m) = (ofNat n) + (ofNat m) := rfl

example (n m : ℕ) : ofNat (n * m) = (ofNat n) * (ofNat m) := by
  unfold ofNat
  apply Quot.sound
  unfold NatPair.mul; simp
  trivial

theorem ofNatInj {n m : ℕ} : ofNat n = ofNat m → n = m := by
  unfold ofNat
  rw [Quotient.eq]
  exact id

/-! # 相反数
整数的相反数定义如下（书中定义4.1.4）：
$$-(a,b)=(b,a)$$
在Lean中定义自然数对的”相反数“如下：
-/
def NatPair.neg : NatPair → NatPair
  | ⟨a, b⟩ => ⟨b, a⟩

/-! 可以验证上述“相反数”与等价关系`NatPair.diffEq`是兼容的（书中习题4.1.2）。-/
theorem NatPair.neg_congr (n m : NatPair) :
    n ≈ m → neg n ≈ neg m := by
  simp [eqv_iff_diff_eq]
  unfold neg diffEq;
  omega

/-! 从而可以将`NatPair`上的“相反数”迁移到`Integer`上。-/
def Integer.neg : Integer → Integer :=
  Quotient.map
  NatPair.neg
  NatPair.neg_congr

prefix:75 "-" => Integer.neg

/-! # 三歧性
可以证明整数具有三歧性（书中引理4.1.5）。

先证整数包含零、正整数和负整数。
-/
theorem Integer.trichotomy (n : Integer) :
    (n = ofNat 0) ∨
    (∃ m : ℕ, m > 0 ∧ n = ofNat m) ∨
    (∃ m : ℕ, m > 0 ∧ n = -ofNat m) := by
  have : ∀ n : NatPair, Quot.mk Setoid.r n = Quotient.mk instSetoidNatPair n
    := fun _ => rfl
  obtain ⟨a, b⟩ := n
  rcases (Nat.lt_trichotomy a b) with h | h | h
  . -- a < b
    right; right
    obtain ⟨d, hd⟩ := Nat.le.dest h
    use d + 1
    constructor
    . exact Nat.zero_lt_succ d
    . unfold ofNat Integer.neg NatPair.neg
      simp [this]
      rw [Quotient.eq, NatPair.eqv_iff_diff_eq]
      unfold NatPair.diffEq
      omega
  . -- a = b
    left
    unfold ofNat
    simp [this]
    rw [Quotient.eq, NatPair.eqv_iff_diff_eq]
    unfold NatPair.diffEq
    omega
  . -- a > b
    right; left
    obtain ⟨d, hd⟩ := Nat.le.dest h
    use d + 1
    constructor
    . exact Nat.zero_lt_succ d
    . unfold ofNat
      simp [this]
      rw [Quotient.eq, NatPair.eqv_iff_diff_eq]
      unfold NatPair.diffEq
      omega

/-! 再证整数只能是零、正数、负数其中一种情况。-/
example (n : Integer) :
    ¬(n = ofNat 0 ∧ ∃ m : ℕ, m > 0 ∧ n = ofNat m) := by
  rintro ⟨hn, ⟨m, hm⟩⟩
  have : m = 0 := ofNatInj <| hn ▸ hm.right.symm
  linarith


example (n : Integer) :
    ¬(n = ofNat 0 ∧ ∃ m : ℕ, m > 0 ∧ n = -ofNat m) := by
  rintro ⟨hn, ⟨m, hm⟩⟩
  have : ofNat 0 = -ofNat m := hn ▸ hm.right
  conv at this =>
    unfold ofNat Integer.neg NatPair.neg; simp
    rw [Quotient.eq, NatPair.eqv_iff_diff_eq]
    unfold NatPair.diffEq; simp
  linarith

example (n : Integer) :
    ¬((∃ m : ℕ, m > 0 ∧ n = ofNat m) ∧
    ∃ m : ℕ, m > 0 ∧ n = -ofNat m) := by
  rintro ⟨⟨m1, hm1⟩, ⟨m2, hm2⟩⟩
  have : ofNat m1 = -ofNat m2 := hm1.right ▸ hm2.right
  conv at this =>
    unfold ofNat Integer.neg NatPair.neg; simp
    rw [Quotient.eq, NatPair.eqv_iff_diff_eq]
    unfold NatPair.diffEq; simp
  linarith

/-! 整数的三歧性提供了另一种定义整数的方式，事实上Lean就是这样定义整数的。
```lean
inductive Int where
  | ofNat : Nat → Int
  | negSucc : Nat → Int
```
整数的加法、乘法满足一系列的运算律（书中<a name="4.1.6"></a>**命题4.1.6**），这使得整数成为一个交换环。
-/
#check (Int.add_comm : ∀ (x y : ℤ), x + y = y + x)
#check (Int.add_assoc : ∀ (x y z : ℤ), x + y + z = x + (y + z))
#check (Int.add_zero : ∀ x : ℤ, x + 0 = x)
#check (Int.zero_add : ∀ x : ℤ, 0 + x = x)
#check (Int.add_right_neg : ∀ x : ℤ, x + (-x) = 0)
#check (Int.add_left_neg : ∀ x : ℤ, (-x) + x = 0)
#check (Int.mul_comm : ∀ (x y : ℤ), x * y = y * x)
#check (Int.mul_assoc : ∀ (x y z : ℤ), x * y * z = x * (y * z))
#check (Int.mul_add : ∀ (x y z : ℤ), x * (y + z) = x * y + x * z)
#check (Int.add_mul : ∀ (y z x: ℤ), (y + z) * x = y * x + z * x)

/-! 并且整数是一个无零因子环（书中<a name="4.1.8"></a>**命题4.1.8**）。-/
#check (Int.mul_eq_zero : ∀ {a b : ℤ},a * b = 0 ↔ a = 0 ∨ b = 0)

/-! 整数还满足消去律（书中<a name="4.1.9"></a>**推论4.1.9**）。-/
#check (Int.eq_of_mul_eq_mul_left : ∀ {a b c : ℤ},a ≠ 0 → a * b = a * c → b = c)

/-! # 小于等于
称整数$m$小于等于$n$，如果存在自然数$a$使得$n=m+a$(书中定义4.1.10)。
这与Lean中的定义不同，但二者是等价的。-/
example {m n : ℤ} : m ≤ n ↔ ∃ a : ℕ, m + a = n := by
  constructor
  . exact Int.le.dest
  rintro ⟨a, h⟩
  exact Int.le.intro a h

/-! 整数的小于等于关系满足一系列性质（书中<a name="4.1.11"></a>**引理4.1.11**）。-/
#check (Int.le_def : ∀ b a : ℤ, b ≤ a ↔ Int.NonNeg (a - b))
#check (Int.add_lt_add_right : ∀ {a b: ℤ}, b < a → ∀ c : ℤ, b + c < a + c)
#check (Int.mul_lt_mul_of_pos_right : ∀ {a b c : ℤ}, b < a → c > 0 → b * c < a * c)
#check (Int.neg_lt_neg : ∀ {b a : ℤ}, b < a → -a < -b)
#check (Int.lt_trans : ∀ {c b a : ℤ}, c < b → b < a → c < a)
#check (Int.lt_trichotomy : ∀ b a : ℤ, b < a ∨ b = a ∨ a < b)

/-! # 习题
4.1.1 验证`NatPair.diffEq`是等价关系。
-/
#check (instSetoidNatPair : Setoid NatPair)

/-! 4.1.2 验证整数的相反数是良定的。-/
#check (Integer.neg : Integer → Integer)

/-! 4.1.3 证明$(-1)\times a = -a$。-/
#check (neg_one_mul : ∀ a : ℤ, (-1) * a = -a)

/-! 4.1.4 证明[命题4.1.6](#4.1.6)。

4.1.5 证明[命题4.1.8](#4.1.8)。

4.1.6 证明[推论4.1.9](#4.1.9)。

4.1.7 证明[引理4.1.11](#4.1.11)。

4.1.8 证明整数不适用数学归纳法。
-/
example : ∃ P : ℤ → Prop, P 0 ∧ (∀ n : ℤ, P n → P (n + 1)) ∧
    (∃ n : ℤ, ¬P n) := by
  use Int.NonNeg
  constructor
  . exact Int.NonNeg.mk 0
  constructor
  . intro _ h
    obtain ⟨n⟩ := h
    exact Int.NonNeg.mk (n + 1)
  use -1
  intro h
  obtain ⟨n⟩ := h
