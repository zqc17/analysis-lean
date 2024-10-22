import Mathlib.Tactic --#

/- # 加法
自然数的加法定义如下（书中定义2.2.1）：
$$0+m=m,\quad n.succ+m=(n+m).succ$$
在Lean中定义如下：
-/
#check (Nat.zero_add : ∀ m : ℕ, 0 + m = m)
#check (Nat.succ_add : ∀ n m : ℕ, n.succ + m = (n + m).succ)

/-! 我们无法从定义中直接得出$n+0=n$，
但是我们可以使用数学归纳法证明它（书中引理2.2.2）。-/
example (n : ℕ) : n + 0 = n := by
  induction n with
  | zero => rw [Nat.zero_add]
  | succ n ihn => rw [Nat.succ_add, ihn]

/-! 类似地，还可以证明$n+m.succ=(n+m).succ$（书中引理2.2.3）。-/
example (n m : ℕ) : n + m.succ = (n + m).succ := by
  induction n with
  | zero => rw [Nat.zero_add, Nat.zero_add]
  | succ n ihn => rw [Nat.succ_add, Nat.succ_add, ihn]

/-! 有了上述两个引理就可以证明自然数加法的交换律了（书中命题2.2.4）。-/
example (n m : ℕ) : n + m = m + n := by
  induction n with
  | zero => rw [Nat.zero_add, Nat.add_zero]
  | succ n ihn => rw [Nat.succ_add, Nat.add_succ, ihn]

/-! 利用数学归纳法还可以证明自然数加法的结合律
（书中<a name="2.2.5"></a>**命题2.2.5**）；-/
example (a b c : ℕ) : a + b + c = a + (b + c) := by
  induction a with
  | zero => rw [Nat.zero_add, Nat.zero_add]
  | succ a iha => rw [Nat.succ_add, Nat.succ_add, Nat.succ_add, iha]

/-! 以及消去律（书中命题2.2.6）。-/
example (a b c : ℕ) (h : a + b = a + c) : b = c := by
  induction a with
  | zero => rwa [Nat.zero_add, Nat.zero_add] at h
  | succ a iha =>
    rw [Nat.succ_add, Nat.succ_add] at h
    exact iha <| Nat.succ.inj h

/-! # 正性
称一个自然数是正的，如果它不等于零（书中定义2.2.7）。
在Lean中定义如下：
-/
#check (Nat.pos_iff_ne_zero : ∀ {n : ℕ}, 0 < n ↔ n ≠ 0)

/-! 通过分类讨论可以证明正自然数和任意自然数的和是正自然数（书中命题2.2.8）。-/
theorem Prop228 {a b : ℕ} (ha: 0 < a) : 0 < a + b:= by
  rw [Nat.pos_iff_ne_zero] at ha ⊢
  cases b
  . rw [Nat.add_zero]; exact ha
  . rw [Nat.add_succ]; exact Nat.succ_ne_zero _

/-! 由上述命题可以得到推论：两个自然数之和等于零当且仅当它们都等于零（书中推论2.2.9）。-/
example (a b : ℕ) (h : a + b = 0) : a = 0 ∧ b = 0 := by
  constructor
  . contrapose! h
    rw [← Nat.pos_iff_ne_zero] at h ⊢
    exact Prop228 h
  contrapose! h
  rw [← Nat.pos_iff_ne_zero] at h ⊢
  rw [add_comm]
  exact Prop228 h

/-! 可以证明如果一个自然数是正的，那么它是某个自然数的后继（书中<a name="2.2.10"></a>**引理2.2.10**）。-/
example (a : ℕ) (h : 0 < a) : ∃ b : ℕ, b.succ = a := by
  rw [pos_iff_ne_zero] at h
  cases a with
  | zero => contradiction
  | succ a => use a

/-! # 小于等于
称自然数$m$小于等于自然数$n$，如果存在自然数$a$使得$n=m+a$（书中定义2.2.11）。
这与Lean中的定义不同，但二者是等价的。-/
example (n m : ℕ) : m ≤ n ↔ ∃ a : ℕ, m + a = n := by
  constructor
  . exact Nat.le.dest
  intro ⟨a, ha⟩
  exact Nat.le.intro ha

/-! 自然数的小于等于关系满足下列性质（书中<a name="2.2.12"></a>**命题2.2.12**），
这使得小于等于成为自然数的一个偏序。-/
#check (Nat.le_refl : ∀ a : ℕ, a ≤ a)
#check (Nat.le_trans : ∀ {a b c : ℕ}, c ≤ b → b ≤ a → c ≤ a)
#check (Nat.le_antisymm : ∀ {a b : ℕ}, a ≤ b → b ≤ a → a = b)
#check (Nat.add_le_add_iff_right : ∀ {a b c : ℕ}, b + c ≤ a + c ↔ b ≤ a)
#check (Nat.add_one_le_iff : ∀ {a b : ℕ}, a.succ ≤ b ↔ a < b)
#check (lt_iff_exists_pos_add : ∀ {a b : ℕ}, a < b ↔ ∃ d > 0, a + d = b)

/-! 自然数具有三歧性（书中<a name="2.2.13"></a>**命题2.2.13**），
这使得小于等于成为自然数的一个全序。-/
#check (Nat.lt_trichotomy : ∀ a b : ℕ, a < b ∨ a = b ∨ b < a)

-- 不能同时小于、等于
example (a b : ℕ) : ¬(a < b ∧ a = b) := by intro h; linarith

-- 不能同时等于、大于
example (a b : ℕ) : ¬(a = b ∧ b < a) := by intro h; linarith

-- 不能同时小于、大于
example (a b : ℕ) : ¬(a < b ∧ b < a) := by intro h; linarith

/-! 利用自然数的小于等于关系可以给出强数学归纳法（书中命题<a name="2.2.14"></a>**2.2.14**）。-/
#check (Nat.strongRec : ∀ {P : ℕ → Prop}, (∀ n, (∀ m, m < n → P m) → P n) → ∀ n, P n)

/-! # 习题
2.2.1 证明[命题2.2.5](#2.2.5)。

2.2.2 证明[引理2.2.10](#2.2.10)。

2.2.3 证明[命题2.2.12](#2.2.12)。

2.2.4 证明[命题2.2.13](#2.2.13)。

2.2.5 证明[命题2.2.14](#2.2.14)。

2.2.6 证明逆向数学归纳法。
-/
example (P : ℕ → Prop) (n : ℕ) : P n → (∀ {m}, P m.succ → P m) → ∀ m ≤ n, P m := by
  intro h0 h1 m hm
  induction n with
  | zero => rwa [← Nat.eq_zero_of_le_zero hm] at h0
  | succ n ihn =>
    specialize ihn (h1 h0)
    obtain ⟨a, ha⟩ := Nat.le.dest hm
    cases a
    . rwa [← ha] at h0
    exact ihn (Nat.le.intro (Nat.succ.inj ha))
