import Mathlib.Tactic --#

/-! # 乘法
自然数的乘法定义为（书中定义2.3.1）：
$$0\times m=0,\quad (n+1)\times m=n\times m + m$$
在Lean中定义如下：
-/
#check (Nat.zero_mul : ∀ m : ℕ, 0 * m = 0)
#check (Nat.succ_mul : ∀ n m : ℕ, (n + 1) * m = n * m + m)

/-! 利用数学归纳法可以证明自然数乘法的交换律（书中<a name="2.3.2"></a>**引理2.3.2**）。-/
example : ∀ n m : ℕ, n * m = m * n := by
  have h_mul_zero : ∀ n : ℕ, n * 0 = 0 := by
    intro n
    induction n with
    | zero => rw [Nat.zero_mul]
    | succ n ihn => rw [Nat.succ_mul, Nat.add_zero, ihn]
  have h_mul_succ : ∀ n m : ℕ, n * (m + 1) = n * m + n := by
    intro n m
    induction n with
    | zero => rw [Nat.zero_mul, Nat.zero_mul, Nat.zero_add]
    | succ n ihn =>
      rw [Nat.succ_mul, Nat.succ_mul, ihn, Nat.add_succ, Nat.add_succ]
      rw [Nat.add_assoc, Nat.add_comm n, ← Nat.add_assoc]
  intro n m
  induction n with
  | zero => rw [Nat.zero_mul, h_mul_zero]
  | succ n ihn => rw [Nat.succ_mul, h_mul_succ, ihn]


/-! 可以证明自然数没有零因子（书中<a name="2.3.3"></a>**引理2.3.3**）。-/
#check (Nat.mul_eq_zero : ∀ {m n : ℕ}, n * m = 0 ↔ n = 0 ∨ m = 0)

/-! 可以证明自然数乘法对加法的分配律（书中命题2.3.4）。-/
theorem Prop234 (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero => rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero]
  | succ c ihc => rw [Nat.add_succ, Nat.mul_succ, Nat.mul_succ, ihc, Nat.add_assoc]

-- 乘法交换律
#check (Nat.mul_comm : ∀ (n m : ℕ), n * m = m * n)

example (a b c : ℕ) : (b + c) * a = b * a + c * a := by
  repeat rw [Nat.mul_comm _ a]
  exact Prop234 a b c

/-! 可以证明自然数乘法的结合律（书中<a name="2.3.5"></a>**命题2.3.5**）。-/
example (a b c : ℕ) : a * b * c = a * (b * c) := by
  induction a with
  | zero => repeat rw [Nat.zero_mul]
  | succ a iha => rw [Nat.succ_mul, Nat.succ_mul, Nat.add_mul, iha]

/-! 可以证明自然数乘法的保序性（书中命题2.3.6）。-/
#check (Nat.mul_lt_mul_of_pos_right : ∀ {a b c : ℕ},
  a < b → 0 < c → a * c < b * c)

/-! 由乘法的保序性可得推论：乘法消去律（书中推论2.3.7）。-/
#check (Nat.mul_right_cancel : ∀ {a b c : ℕ}, 0 < c → a * c = b * c → a = b)

/-! 可以证明带余除法定理（书中<a name="2.3.9"></a>**命题2.3.9**）。-/
#check (Nat.div_add_mod : ∀ n q : ℕ, q * (n / q) + n % q = n)
#check (Nat.mod_lt : ∀ n : ℕ, ∀ {q : ℕ}, 0 < q → n % q < q)

/-! 最后我们定义自然数的幂为（书中定义2.3.11）：
$$m^0=1,\quad m^{n+1}=m^n\times m$$
在Lean中定义如下：-/
#check (Nat.pow_zero : ∀ n : ℕ, n ^ 0 = 1)
#check (Nat.pow_succ : ∀ m n : ℕ, m ^ n.succ = m ^ n * m)

/-! # 习题
2.3.1 证明[引理2.3.2](#2.3.2)。

2.3.2 证明[引理2.3.3](#2.3.3)。

2.3.3 证明[命题2.3.5](#2.3.5)。

2.3.4 证明完全平方公式。
-/
example (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := calc
  _ = (a + b) * (a + b) := by
    rw [Nat.pow_two]
  _ = a * a + a * b + b * a + b * b := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.add_assoc (a * a + a * b)]
  _ = a * a + 2 * a * b + b * b := by
    rw [Nat.two_mul, Nat.add_mul, ← Nat.add_assoc, Nat.mul_comm b a]
  _ = a ^ 2 + 2 * a * b + b ^ 2 := by
    rw [← Nat.pow_two, ← Nat.pow_two]

/-! 在Lean中这种反复使用运算律就可以证明的命题可以使用`ring`方便地证明。-/
example (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring

/-! 2.3.5 证明[命题2.3.9](#2.3.9)。-/
