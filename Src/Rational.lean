import Mathlib.Tactic --#

/-! # 有理数的定义
用整数对$(a,b)$表示“形式商”$a/b$。
-/
structure IntPair where
  a : ℤ
  b : ℤ
  b_ne_zero : b ≠ 0

/-! 定义整数对的等价关系$(a,b)\sim(c,d)\iff ad=cb$。-/
def IntPair.quotEq : IntPair → IntPair → Prop
  | ⟨a, b, _⟩, ⟨c, d, _⟩ => a * d = c * b

/-! 可以验证`IntPair.quotEq`是一个等价关系。-/
instance instSetoidIntPair : Setoid IntPair where
  r := IntPair.quotEq
  iseqv := {
    refl := by
      intro x; unfold IntPair.quotEq; simp [Int.mul_comm]
    symm := by
      intro x y; unfold IntPair.quotEq; simp
      intro h; rw [Int.mul_comm, h, Int.mul_comm]
    trans := by
      intro x y z; unfold IntPair.quotEq; simp
      intro hxy hyz
      apply Int.eq_of_mul_eq_mul_left y.b_ne_zero
      rw [← Int.mul_assoc, ← Int.mul_assoc]
      rw [Int.mul_comm y.b x.a, Int.mul_comm y.b z.a]
      rw [hxy, hyz.symm]
      rw [Int.mul_assoc, Int.mul_comm x.b, ← Int.mul_assoc]
  }

theorem IntPair.eqv_iff_quot_eq {n m : IntPair} : n ≈ m ↔ quotEq n m
  := Eq.to_iff rfl

/-! 定义有理数为整数对$(a,b)$关于等价关系`IntPair.quotEq`的商类型（书中定义4.2.1）。-/
def Rational := Quotient instSetoidIntPair

/-! # 加法、乘法、相反数
定义有理数的加法、乘法、相反数如下（书中定义4.2.2）：
$$(a,b)+(c,d)=(ad+bc,bd)$$
$$(a,b)\times(c,d)=(ac,bd)$$
$$-(a,b)=(-a,b)$$
在Lean中定义整数对的加法、乘法、相反数如下：-/
def IntPair.add : IntPair → IntPair → IntPair
  | ⟨a, b, hb⟩, ⟨c, d, hd⟩ =>
  ⟨a * d + b * c, b * d, Int.mul_ne_zero hb hd⟩

def IntPair.mul : IntPair → IntPair → IntPair
  | ⟨a, b, hb⟩, ⟨c, d, hd⟩ =>
  ⟨a * c, b * d, Int.mul_ne_zero hb hd⟩

def IntPair.neg : IntPair → IntPair
  | ⟨a, b, hb⟩ => ⟨-a, b, hb⟩

/-! 可以验证上述加法、乘法、相反数与等价关系`IntPair.quotEq`是兼容的（书中<a name="4.2.3"></a>**引理4.2.3**）。-/
theorem IntPair.add_congr_left (n m l : IntPair) :
  n ≈ m → (add n l) ≈ (add m l)
:= by
  simp [eqv_iff_quot_eq]
  unfold quotEq add; simp; intro h
  calc
    _ = n.a * m.b * l.b * l.b + n.b * m.b * l.a * l.b := by ring
    _ = m.a * n.b * l.b * l.b + n.b * m.b * l.a * l.b := by rw [h]
    _ = _ := by ring

theorem IntPair.add_congr_right (l n m : IntPair) :
  n ≈ m → (add l n) ≈ (add l m)
:= sorry -- 与`IntPair.add_congr_left`类似

theorem IntPair.mul_congr_left (n m l : IntPair) :
  n ≈ m → (mul n l) ≈ (mul m l)
:= by
  simp [eqv_iff_quot_eq]
  unfold quotEq mul; simp; intro h
  calc
    _ = n.a * m.b * l.a * l.b := by ring
    _ = m.a * n.b * l.a * l.b := by rw [h]
    _ = _ := by ring

theorem IntPair.mul_congr_right (l n m : IntPair) :
  n ≈ m → (mul l n) ≈ (mul l m)
:= sorry -- 与`IntPair.mul_congr_left`类似

theorem IntPair.neg_congr (n m : IntPair) :
  n ≈ m → neg n ≈ neg m
:= by
  simp [eqv_iff_quot_eq]
  unfold neg quotEq
  simp

/-!从而可以将`IntPair`上的加法、乘法、相反数迁移到`Rational`上。-/
def Rational.add : Rational → Rational → Rational :=
  Quot.map₂
  IntPair.add
  IntPair.add_congr_right
  IntPair.add_congr_left

def Rational.mul : Rational → Rational → Rational :=
  Quot.map₂
  IntPair.mul
  IntPair.mul_congr_right
  IntPair.mul_congr_left

def Rational.neg : Rational → Rational :=
  Quotient.map
  IntPair.neg
  IntPair.neg_congr

infix:65 " + " => Rational.add
infix:70 " * " => Rational.mul
prefix:75 "-" => Rational.neg

/-! 按照下述方式可以将整数嵌入到有理数中。-/
def ofInt : ℤ → Rational
  | n => Quotient.mk instSetoidIntPair ⟨n, 1, by decide⟩

/-! 并且这种嵌入可以保持加法、乘法、相反数。-/
example (n m : ℤ) : ofInt (n + m) = ofInt n + ofInt m := by
  unfold ofInt
  apply Quot.sound
  unfold IntPair.add; simp
  trivial

example (n m : ℤ) : ofInt (n * m) = ofInt n * ofInt m := by
  unfold ofInt
  apply Quot.sound
  unfold IntPair.mul; simp
  trivial

example (n : ℤ) : ofInt (-n) = -ofInt n := rfl

theorem ofIntInj {n m : ℤ} : ofInt n = ofInt m → n = m := by
  unfold ofInt
  sorry

/-! # 倒数
定义有理数的倒数如下：
$$(a,b)^{-1}=(b,a),\textrm{其中}a\neq 0$$
在Lean中定义整数对的倒数如下：-/
def IntPair.inv {n : IntPair} (h : n.a ≠ 0) : IntPair := ⟨n.b, n.a, h⟩

/-! 可以验证上述倒数与等价关系`IntPair.quotEq`是兼容的。-/
def IntPair.inv_congr (n m : IntPair) (hn : n.a ≠ 0) (hm : m.a ≠ 0) :
  n ≈ m → inv hn ≈ inv hm
:= by
  simp [eqv_iff_quot_eq]
  unfold quotEq inv; simp; intro h
  rw [Int.mul_comm n.b, Int.mul_comm m.b]
  exact h.symm

/-! # Lean中的有理数
Lean中的有理数实际上是如下定义的：
```lean
structure Rat where
  num : Int
  den : Nat := 1
  den_nz : den ≠ 0 := by decide
  reduced : num.natAbs.Coprime den := by decide
```
`Rat`的分母`den`是正整数，并且分子`num`和分母`den`是互素的，也就是说`num /. den`是既约分数。

有理数的加法、乘法、相反数、倒数满足一系列运算律（书中<a name="4.2.4"></a>**命题4.2.4**），
这使得有理数成为一个域。-/
#check (Rat.add_comm : ∀ x y : ℚ, x + y = y + x)
#check (Rat.add_assoc : ∀ x y z : ℚ, x + y + z = x + (y + z))
#check (Rat.add_zero : ∀ x : ℚ, x + 0 = x)
#check (Rat.zero_add : ∀ x : ℚ, 0 + x = x)
#check (add_neg_cancel : ∀ x : ℚ, x + (-x) = 0)
#check (Rat.neg_add_cancel : ∀ x : ℚ, (-x) + x = 0)
#check (Rat.mul_comm : ∀ x y : ℚ, x * y = y * x)
#check (Rat.mul_assoc : ∀ x y z : ℚ, x * y * z = x * (y * z))
#check (Rat.mul_one : ∀ x : ℚ, x * 1 = x)
#check (Rat.one_mul : ∀ x : ℚ, 1 * x = x)
#check (Rat.mul_add : ∀ x y z : ℚ, x * (y + z) = x * y + x * z)
#check (Rat.add_mul : ∀ y z x : ℚ, (y + z) * x = y * x + z * x)
#check (Rat.mul_inv_cancel : ∀ x : ℚ, x ≠ 0 → x * x⁻¹ = 1)
#check (Rat.inv_mul_cancel : ∀ x : ℚ, x ≠ 0 → x⁻¹ * x = 1)

/-! # 三歧性
可以证明有理数具有三歧性（书中<a name="4.2.7"></a>**引理4.2.7**）。

先证有理数包含零、正有理数和负有理数。-/
example (x : ℚ) : (0 < x) ∨ (0 = x) ∨ (x < 0) := lt_trichotomy 0 x

/-! 再证有理数只能是零、正有理数、负有理数其中一种情况。-/
example (x : ℚ) : ¬(0 < x ∧ 0 = x) := by intro h; linarith

example (x : ℚ) : ¬(0 < x ∧ x < 0) := by intro h; linarith

example (x : ℚ) : ¬(0 = x ∧ x < 0) := by intro h; linarith

/-! # 小于等于
称有理数$y$小于等于$x$，如果$x-y$是非负有理数（书中定义4.2.8）。这与Lean中的定义不同，但二者是等价的。-/
#check (Rat.le_iff_sub_nonneg : ∀ y x : ℚ, y ≤ x ↔ 0 ≤ x - y)

/-! 有理数的小于等于关系满足一系列性质（书中<a name="4.2.9"></a>**命题4.2.9**），这使得有理数称为一个有序域。-/
#check (lt_trichotomy : ∀ x y : ℚ, x < y ∨ x = y ∨ y < x)
example (x y : ℚ) : x < y ↔ y > x := Eq.to_iff rfl
#check (lt_trans : ∀ {x y z : ℚ}, x < y → y < z → x < z)
#check (add_lt_add_iff_right : ∀ z : ℚ, ∀ {x y : ℚ}, x + z < y + z ↔ x < y)
#check (mul_lt_mul_iff_of_pos_right : ∀ {z y x : ℚ}, 0 < z → (x * z < y * z ↔ x < y))

/-! # 习题
4.2.1 验证`IntPair.quotEq`是等价关系。
-/
#check (instSetoidIntPair : Setoid IntPair)

/-! 4.2.2 证明[引理4.2.3](#4.2.3)。

4.2.3 证明[命题4.2.4](#4.2.4)。

4.2.4 证明[引理4.2.7](#4.2.7)。

4.2.5 证明[命题4.2.9](#4.2.9)。

4.2.6 证明若$z < 0$，则$x < y \implies xz > yz$。
-/
example (x y z : ℚ) (hz : z < 0) (h : x < y) : y * z < x * z :=
  mul_lt_mul_of_neg_right h hz
