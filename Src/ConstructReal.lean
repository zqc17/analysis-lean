import Mathlib.Tactic --#

/-! # 实数的定义
在Lean中实数是如下定义的：
```lean
structure Real where ofCauchy ::
  cauchy : CauSeq.Completion.Cauchy (abs : ℚ → ℚ)
```
其中`cauchy`是柯西列关于序列等价的商类型（书中定义5.3.1）：
-/
#check ((0 : ℝ).cauchy : @Quotient (CauSeq ℚ (abs : ℚ → ℚ)) CauSeq.equiv)

/-! Lean中定义两个柯西列等价为它们的差趋近于0。-/
theorem equiv_iff_limZero (a b : CauSeq ℚ (abs : ℚ → ℚ)) :
  a ≈ b ↔ CauSeq.LimZero (a - b) := by rfl

/-! 可以验证这确实是个等价关系（书中<a name="5.3.3"></a>**命题5.3.3**）。-/
example (a : CauSeq ℚ (abs : ℚ → ℚ)) : a ≈ a := by
  simp [equiv_iff_limZero, CauSeq.zero_limZero]

example (a b : CauSeq ℚ (abs : ℚ → ℚ)) : a ≈ b → b ≈ a := by
  simp [equiv_iff_limZero]
  intro h
  rw [show b - a = - (a - b) by ring]
  exact CauSeq.neg_limZero h

example (a b c : CauSeq ℚ (abs : ℚ → ℚ)) : a ≈ b → b ≈ c → a ≈ c := by
  simp [equiv_iff_limZero]
  intro h1 h2
  rw [show a - c = a - b + (b - c) by ring]
  exact CauSeq.add_limZero h1 h2

/-! # 加法、乘法
有理数序列的加法定义为逐项相加（书中定义5.3.4）：-/
example (a b : ℕ → ℚ) : a + b = fun n ↦ a n + b n := rfl

/-! 可以验证柯西列相加仍然是柯西列（书中引理5.3.6）；-/
example (a b : ℕ → ℚ) (ha : IsCauSeq (abs : ℚ → ℚ) a) (hb : IsCauSeq (abs : ℚ → ℚ) b) :
  IsCauSeq (abs : ℚ → ℚ) (a + b) := IsCauSeq.add ha hb

/-! 并且上述加法与柯西列的等价关系兼容（书中引理5.3.7），从而上述加法可以迁移到实数上。-/
example (a1 a2 b1 b2 : CauSeq ℚ (abs : ℚ → ℚ)) :
  a1 ≈ a2 → b1 ≈ b2 → a1 + b1 ≈ a2 + b2 := CauSeq.add_equiv_add

/-! 类似地，有理数序列的乘法定义为逐项相乘（书中定义5.3.9）：-/
example (a b : ℕ → ℚ) : a * b = fun n ↦ a n * b n := rfl

/-! 可以验证柯西列相乘仍然是柯西列（书中<a name="5.3.10"></a>**命题5.3.10**）；-/
example (a b : ℕ → ℚ) (ha : IsCauSeq (abs : ℚ → ℚ) a) (hb : IsCauSeq (abs : ℚ → ℚ) b) :
  IsCauSeq (abs : ℚ → ℚ) (a * b) := IsCauSeq.mul ha hb

/-! 并且上述乘法与柯西列的等价关系兼容，从而上述乘法可以迁移到实数上。-/
example (a1 a2 b1 b2 : CauSeq ℚ (abs : ℚ → ℚ)) :
  a1 ≈ a2 → b1 ≈ b2 → a1 * b1 ≈ a2 * b2 := CauSeq.mul_equiv_mul

/-! 由有理数的运算律易得实数的运算律（书中命题5.3.11）：-/
#check (add_comm : ∀ x y : ℝ, x + y = y + x)
#check (add_assoc : ∀ x y z : ℝ, x + y + z = x + (y + z))
#check (add_zero : ∀ x : ℝ, x + 0 = x)
#check (zero_add : ∀ x : ℝ, 0 + x = x)
#check (add_neg_cancel : ∀ x : ℝ, x + (-x) = 0)
#check (neg_add_cancel : ∀ x : ℝ, (-x) + x = 0)
#check (mul_comm : ∀ x y : ℝ, x * y = y * x)
#check (mul_assoc : ∀ x y z : ℝ, x * y * z = x * (y * z))
#check (mul_one : ∀ x : ℝ, x * 1 = x)
#check (one_mul : ∀ x : ℝ, 1 * x = x)
#check (mul_add : ∀ x y z : ℝ, x * (y + z) = x * y + x * z)
#check (add_mul : ∀ x y z : ℝ, (x + y) * z = x * z + y * z)
#check (mul_inv_cancel₀ : ∀ {x : ℝ}, x ≠ 0 → x * x⁻¹ = 1)
#check (inv_mul_cancel₀ : ∀ {x : ℝ}, x ≠ 0 → x⁻¹ * x = 1)

/-! # 倒数
需要注意的是倒数不是直接定义为柯西列逐项取倒数，因为柯西列的倒数不一定是柯西列，
甚至柯西列中还可能存在0，从而无法取倒数。

书中通过定义一个序列是远离零的来绕过这个问题（书中定义5.3.12）。
-/
def awayFromZero (a : ℕ → ℚ) :=
  ∃ c > 0, ∀ n, |a n| ≥ c

/-! 可以证明如果一个实数非零，那么它对应的柯西列的等价类中存在一个远离零的序列（书中引理5.3.14）。-/
example (a : CauSeq ℚ (abs : ℚ → ℚ)) : ¬(a ≈ (0 : CauSeq ℚ (abs : ℚ → ℚ))) →
  ∃ b : ℕ → ℚ, awayFromZero b ∧ IsCauSeq (abs : ℚ → ℚ) b := sorry

/-! 对远离零的柯西列逐项倒数得到序列也是柯西列（书中引理5.3.15）。
从而可以顺利地定义倒数（书中定义5.3.16）。-/
example (a : ℕ → ℚ) (ha : IsCauSeq (abs : ℚ → ℚ) a) (ha' : awayFromZero a) :
  IsCauSeq (abs : ℚ → ℚ) fun n ↦ (a n)⁻¹ := by sorry

/-! # 习题
5.3.1 证明[命题5.3.3](#5.3.3)。

5.3.2 证明[命题5.3.10](#5.3.10)。

5.3.3 证明有理数相等当且仅当它们嵌入实数后相等。
-/
example (a b : ℚ) : a = b ↔ (a : ℝ) = (b : ℝ) := by norm_cast

/-! 5.3.4 证明有界序列的等价序列也有界。-/

/-! 5.3.5 证明柯西列$\frac{1}{n},n=1,2,\cdots$对应实数$0$。-/
