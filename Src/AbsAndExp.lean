import Mathlib.Tactic --#

/-! # 绝对值
有理数的绝对值的定义如下（书中定义4.3.1）：
-/
#check (abs_of_pos : ∀ {x : ℚ}, 0 < x → |x| = x)
#check (abs_of_neg : ∀ {x : ℚ}, x < 0 → |x| = -x)
#check (abs_eq_zero : ∀ {x : ℚ}, |x| = 0 ↔ x = 0)

/-! 有理数的距离定义如下（书中定义4.3.2）：-/
def Rat.distance : ℚ → ℚ → ℚ
  | x, y => |x - y|

/-! 绝对值和距离满足下列性质（书中<a name="4.3.3"></a>**命题4.3.3**）。-/
#check (abs_nonneg : ∀ x : ℚ, 0 ≤ |x|)
#check (abs_add_le : ∀ x y : ℚ, |x + y| ≤ |x| + |y|)
#check (abs_le : ∀ {x y : ℚ}, |x| ≤ y ↔ (-y ≤ x ∧ x ≤ y))
#check (abs_mul : ∀ x y : ℚ, |x * y| = |x| * |y|)
#check (abs_neg : ∀ x : ℚ, |-x| = |x|)
example (x y : ℚ) : 0 ≤ x.distance y := by
  unfold Rat.distance; simp
example (x y : ℚ) : x.distance y = 0 ↔ x = y := by
  unfold Rat.distance; simp; exact sub_eq_zero
example (x y : ℚ) : x.distance y = y.distance x := by
  unfold Rat.distance; simp; exact abs_sub_comm x y
example (x y z : ℚ) : x.distance z ≤ x.distance y + y.distance z := by
  unfold Rat.distance; simp; exact abs_sub_le x y z

/-! # ε-邻近
设$\varepsilon$为有理数，称两个有理数是$\varepsilon-$邻近的，如果它们的距离小于等于$\varepsilon$。-/
def Rat.close (ε x y : ℚ) := distance x y ≤ ε

/-! > 注意：$\varepsilon-$邻近并非标准术语，只是《陶哲轩实分析》一书为了方便行文搭建的脚手架。

$\varepsilon-$邻近具有以下性质（书中<a name="4.3.7"></a>**命题4.3.7**）。-/
namespace Rat
variable (x y z w : ℚ)

example : x = y ↔ ∀ ε > 0, close ε x y := sorry
example : ∀ ε > 0, close ε x y → close ε y x := sorry
example : ∀ ε > 0, ∀ δ > 0, close ε x y → close δ y z → close (ε + δ) x z := sorry
example : ∀ ε > 0, ∀ δ > 0, close ε x y ∧ close δ z w →
  close (ε + δ) (x + z) (y + w) ∧ close (ε + δ) (x - z) (y - w) := sorry
example : ∀ ε > 0, close ε x y → ∀ ε' > ε, close ε' x y := sorry
example : ∀ ε > 0, y ≤ z → close ε y x ∧ close ε z x →
  y ≤ w ∧ w ≤ z → close ε w x:= sorry
example : ∀ ε > 0, z ≠ 0 → close ε x y → close (ε * |z|) (x * z) (y * z) := sorry

example : ∀ ε > 0, ∀ δ > 0, close ε x y → close δ z w →
  close (ε * |z| + δ * |x| + ε * δ) (y * w) (x * z)
:= by
  unfold close distance; simp
  intro ε hε δ _ hxy hzw
  let a := y - x
  have haε : |a| ≤ ε := by unfold_let a; rw [abs_sub_comm]; exact hxy
  let b := w - z
  have hbδ : |b| ≤ δ := by unfold_let b; rw [abs_sub_comm]; exact hzw
  have : |y * w - x * z| ≤ |a * z| + |b * x| + |a * b| := by
    rw [show y * w - x * z = a * z + b * x + a * b by ring]
    exact abs_add_three (a * z) (b * x) (a * b)
  have : |y * w - x * z| ≤ |a| * |z| + |b| * |x| + |a| * |b| := by
    rwa [abs_mul a z, abs_mul b x, abs_mul a b] at this
  have haz : |a| * |z| ≤ ε * |z| :=
    mul_le_mul_of_nonneg_right haε (abs_nonneg z)
  have hbx : |b| * |x| ≤ δ * |x| :=
    mul_le_mul_of_nonneg_right hbδ (abs_nonneg x)
  have hab : |a| * |b| ≤ ε * δ := calc
    _ ≤ ε * |b| := mul_le_mul_of_nonneg_right haε (abs_nonneg b)
    _ ≤ ε * δ := mul_le_mul_of_nonneg_left hbδ (le_of_lt hε)
  linarith

end Rat

/-! # 幂
设$x$为有理数，$n$为自然数，$x$的$n$次幂定义如下（书中定义4.3.9）：
$$x^0=1,\quad x^{n+1}=x^n\times x$$
在Lean中定义有理数的自然数幂如下：
-/
#check (pow_zero : ∀ x : ℚ, x ^ 0 = 1)
#check (pow_succ : ∀ x : ℚ, ∀ n : ℕ, x ^ (n + 1) = x ^ n * x)

/-! 有理数的自然数幂满足下列性质（书中<a name="4.3.10"></a>**命题4.3.10**）：-/
#check (pow_add : ∀ x : ℚ, ∀ n m : ℕ, x ^ (n + m) = x ^ n * x ^ m)
#check (pow_mul : ∀ x : ℚ, ∀ n m : ℕ, x ^ (n * m) = (x ^ n) ^ m)
#check (mul_pow : ∀ x y : ℚ, ∀ n : ℕ, (x * y) ^ n = x ^ n * y ^ n)
#check (pow_eq_zero_iff : ∀ {x : ℚ}, ∀ {n : ℕ}, n ≠ 0 → (x ^ n = 0 ↔ x = 0))
#check (pow_le_pow_left : ∀ {x y : ℚ}, 0 ≤ x → x ≤ y →
  ∀ n : ℕ, x ^ n ≤ y ^ n)
#check (pow_lt_pow_left : ∀ {x y : ℚ}, x < y → 0 ≤ x →
  ∀ {n : ℕ}, n ≠ 0 → x ^ n < y ^ n)
#check (abs_pow : ∀ x : ℚ, ∀ n : ℕ, |x ^ n| = |x| ^ n)

/-! 设$x$是非零有理数，$n$是正整数，定义$x$的负整数幂如下（书中定义4.3.11）：

$$ x^{-n}=1/x^{n},\quad x\neq 0 $$

在Lean中定义有理数的整数幂如下：
-/
#check (zpow_neg : ∀ x : ℚ, ∀ n : ℤ, x ^ (- n) = (x ^ n)⁻¹)

/-! 有理数的整数幂满足下列性质（书中<a name="4.3.12"></a>**命题4.3.12**）：-/
#check (zpow_add₀ : ∀ {x : ℚ}, x ≠ 0 → ∀ n m : ℤ, x ^ (n + m) = x ^ n * x ^ m)
#check (zpow_mul : ∀ x : ℚ, ∀ n m : ℤ, x ^ (n * m) = (x ^ n) ^ m)
#check (mul_zpow : ∀ x y : ℚ, ∀ n : ℤ, (x * y) ^ n = x ^ n * y ^ n)

-- 4.3.12 (b) 只证 n < 0 的情形
example (x y : ℚ) (n : ℤ) (hn : n < 0) :
  0 < y → y ≤ x → x ^ n ≤ y ^ n
:= by
  intro hy hyx
  let m := -n
  have : n = -m := Int.eq_neg_comm.mp rfl
  rw [this, zpow_neg x, zpow_neg y]
  apply inv_le_inv_of_le
  . exact zpow_pos_of_pos hy m
  have : m = m.natAbs := Int.eq_natAbs_of_zero_le
    <| le_of_lt <| Int.neg_pos_of_neg hn
  rw [this, zpow_natCast, zpow_natCast]
  exact pow_le_pow_left (le_of_lt hy) hyx m.natAbs

-- 4.3.12 (c) 只证 n < 0 的情形
example (x y : ℚ) (hx : 0 < x) (hy : 0 < y) (n : ℤ) (hn : n < 0):
  x ^ n = y ^ n → x = y
:= by
  intro h
  let m := -n
  have hm : n = -m := Int.eq_neg_comm.mp rfl
  have hm_abs : m = m.natAbs := Int.eq_natAbs_of_zero_le
    <| le_of_lt <| Int.neg_pos_of_neg hn
  have hxy : x ^ m.natAbs = y ^ m.natAbs ↔ _ := pow_eq_pow_iff_of_ne_zero
    <| Int.natAbs_ne_zero.mpr <| Int.neg_ne_zero.mpr <| ne_of_lt hn
  conv at h =>
    rw [hm, zpow_neg x, zpow_neg y, inv_inj]
    rw [hm_abs, zpow_natCast, zpow_natCast]
    rw [hxy]
  rcases h with _ | h
  . assumption
  linarith

-- 4.3.12 (d) 只证 n < 0 的情形
example (x : ℚ) (n : ℤ) (hn : n < 0) : |x ^ n| = |x| ^ n := by
  let m := -n
  have : n = -m := Int.eq_neg_comm.mp rfl
  rw [this, zpow_neg, abs_inv, zpow_neg |x|]
  have : m = m.natAbs := Int.eq_natAbs_of_zero_le
    <| le_of_lt <| Int.neg_pos_of_neg hn
  rw [this, zpow_natCast, zpow_natCast, abs_pow]

/-! # 习题
4.3.1 证明[命题4.3.3](#4.3.3)。

4.3.2 证明[命题4.3.7](#4.3.7)。

4.3.3 证明[命题4.3.10](#4.3.10)。

4.3.4 证明[命题4.3.12](#4.3.12)。

4.3.5 证明$\forall n\in\mathbb{N}, n\leq 2^n$。
-/
theorem Ex435 (n : ℕ) : n ≤ 2 ^ n := match n with
  | 0 => Nat.zero_le (2 ^ 0)
  | (n + 1) => Nat.pow_succ 2 n ▸ Nat.mul_two (2 ^ n) ▸
    Nat.add_le_add (Ex435 n) Nat.one_le_two_pow
