import Mathlib.Data.Rat.Defs --#
import Mathlib.Data.Rat.Cast.Order --#
import Mathlib.Data.Real.Basic --#
import Mathlib.Data.Real.Archimedean --#
import Mathlib

/-! # 序列极限
定义两个实数的距离为它们的差的绝对值（书中定义6.1.1）。-/
def dist (x y : ℝ) := |x - y|

/-! 称两个实数是$\varepsilon-$临近的，如果它们的距离小于等于$\varepsilon$（书中定义6.1.2）。-/
def close (ε x y : ℝ) := |x - y| ≤ ε

/-! 称一个实数序列是柯西列，如果它对任意$\varepsilon>0$都是最终$\varepsilon-$稳定的；
其中最终$\varepsilon-$稳定的定义是存在整数$N$使得对任意大于等于$N$的整数$j,k$都有$|a_j-a_k|\leq\varepsilon$
（书中定义6.1.3）。-/
def evSteady (ε : ℝ) (a : ℕ → ℝ) := ∃ N, ∀ j ≥ N, ∀ k ≥ N, |a j - a k| ≤ ε

/-! 可以证明一个有理数序列的柯西列可以看成实数序列的柯西列（书中命题6.1.4）。
> 注意有理数序列的柯西列定义中$\varepsilon$为有理数，实数序列的柯西列定义中$\varepsilon$为实数。
-/
example (a : ℕ → ℚ) : (∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N, |a j - a k| ≤ ε) ↔
    ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N, |a j - a k| ≤ (ε : ℝ) := by
  constructor
  . intro h ε hε -- 此处的ε是实数
    obtain ⟨ε', hε'⟩ := exists_rat_btwn hε -- 此处的ε'是有理数
    specialize h ε' (by exact_mod_cast hε'.left)
    obtain ⟨N, h⟩ := h
    use N
    intro j hj k hk
    refine le_trans ?_ (le_of_lt hε'.right)
    exact_mod_cast h j hj k hk
  intro h ε hε
  specialize h ε (by norm_cast)
  obtain ⟨N, h⟩ := h
  use N
  exact_mod_cast h

/-! 上述定义与Lean中的柯西列定义不同，但二者是等价的。-/
example (a : ℕ → ℝ) : IsCauSeq (abs : ℝ → ℝ) a ↔ ∀ ε > 0, evSteady ε a := by
  simp [IsCauSeq, evSteady]
  constructor
  . intro h ε hε
    specialize h (ε / 2) (half_pos hε)
    obtain ⟨N, h⟩ := h
    use N
    intro j hj k hk
    have : |a j - a k| ≤ |a j - a N| + |a k - a N| := by
      rw [show a j - a k = (a j - a N) + (a N - a k) by ring]
      rw [abs_sub_comm (a k)]
      exact abs_add _ _
    linarith [h j hj, h k hk]
  intro h ε hε
  specialize h (ε / 2) (half_pos hε)
  obtain ⟨N, h⟩ := h
  use N
  intro j hj
  specialize h j hj N (le_refl _)
  exact lt_of_le_of_lt h (div_two_lt_of_pos hε)

/-! 称一个实数序列$(a_n)_{n=0}^{+\infty}$收敛到实数$L$，
如果对任意$\varepsilon>0$该序列都最终$\varepsilon-$邻近$L$（书中定义6.1.5）。-/
def convergesTo (a : ℕ → ℝ) (L : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| ≤ ε

/-! 可以证明一个实数序列不可能收敛到两个不同的实数（书中命题6.1.7）。-/
example (a : ℕ → ℝ) (L1 L2 : ℝ) (hL1 : convergesTo a L1) (hL2 : convergesTo a L2) :
    L1 = L2 := by sorry

/-! 如果一个实数序列$(a\_n)\_{n=0}^{+\infty}$收敛到实数$L$，则称该序列收敛，并称$L$为该序列的极限，
记为（书中定义6.1.8）：
$$L=\lim\_{n\to+\infty}a\_n$$
可以证明调和数列的极限是$0$。-/
example : convergesTo (fun n ↦ (1 : ℝ) / (n + 1)) 0 := by
  simp [convergesTo]
  intro ε hε
  let N := Nat.floor ε⁻¹
  use N
  intro n hn
  apply le_of_lt
  have : 0 < (n + (1 : ℝ))⁻¹ := by
    apply inv_pos_of_pos
    exact_mod_cast Nat.zero_lt_succ _
  rw [abs_of_pos this, ← inv_inv ε]
  rw [inv_lt_inv (by exact_mod_cast Nat.zero_lt_succ _) (inv_pos_of_pos hε)]
  have : ε⁻¹ < N + 1 := by exact_mod_cast Nat.lt_succ_floor ε⁻¹
  apply lt_of_lt_of_le this
  exact_mod_cast Nat.add_le_add_right hn 1

/-! 可以证明收敛实数序列一定是柯西列（书中<a name="6.1.12"></a>**命题6.1.12**）。-/
example (a : ℕ → ℝ) (ha : ∃ L, convergesTo a L) : IsCauSeq (abs : ℝ → ℝ) a := by
  sorry

/-! > 书中定理6.4.18将证明实数的柯西列一定收敛。
-/

/-! 可以证明有理数柯西列一定是收敛的（书中<a name="6.1.15"></a>**命题6.1.15**）。-/
example (a : ℕ → ℚ) (ha : IsCauSeq (abs : ℚ → ℚ) a) :
    ∃ L, convergesTo (fun n ↦ a n) L := by sorry

/-! 如果存在实数$M$使得实数序列的每一项的绝对值都小于等于$M$，
则称该实数序列有界（书中<a name="6.1.16"></a>**定义6.1.16**）。-/
def bounded (a : ℕ → ℝ) := ∃ M, ∀ n, |a n| ≤ M

/-! 显然收敛实数序列必定有界（书中推论6.1.17）。-/
example (a : ℕ → ℝ) (ha : ∃ L, convergesTo a L) : bounded a := by sorry

/-! 极限满足下述运算法则，从而可以大大简化极限的计算
（书中<a name="6.1.19"></a>**定理6.1.19**）。-/
section
open CauSeq
variable (a b : CauSeq ℝ (abs : ℝ → ℝ))

example : lim a + lim b = lim (a + b) := lim_add a b
example : lim a * lim b = lim (a * b) := lim_mul_lim a b
example (c : ℝ) : lim a * c = lim (a * const abs c) := lim_mul a c
example : lim (a - b) = lim a - lim b := by
  rw [sub_eq_add_neg, ← lim_add, lim_neg, sub_eq_add_neg]
example (hb : ¬LimZero b) : lim (inv b hb) = (lim b)⁻¹ := lim_inv hb

-- Lean中a ⊔ b表示两个柯西列逐项取最大值，a ⊓ b表示两个柯西列逐项取最小值
example (n : ℕ) : (a ⊔ b) n = max (a n) (b n) := rfl
example (n : ℕ) : (a ⊓ b) n = min (a n) (b n) := rfl
example : lim (a ⊔ b) = max (lim a) (lim b) := by sorry
example : lim (a ⊓ b) = min (lim a) (lim b) := by sorry
end

/-! # 习题
6.1.1 实数序列满足$a_{n+1}>a_n$。证明对任意自然数$m>n$有$a_{m}>a_{n}$。-/
example (a : ℕ → ℝ) (ha : ∀ n, a n < a (n + 1)) (n m : ℕ) (hnm : n < m) :
    a n < a m := by
  induction m with
  | zero => contradiction
  | succ m ihm =>
    rcases Nat.lt_or_ge n m with h | h
    . apply lt_trans <| ihm h; exact ha m
    . rw [Nat.eq_of_le_of_lt_succ h hnm]; exact ha m

/-! 6.1.2 证明实数序列收敛到实数$L$当且仅当对任意$\varepsilon>0$存在自然数$N$使得对任意$n\geq N$都有$|a_n-L|\leq\varepsilon$。

6.1.3 证明实数序列在头部任意添加、丢弃有限项不影响其收敛性。-/
example (a : ℕ → ℝ) (L : ℝ) (m : ℕ) :
    convergesTo a L ↔ convergesTo (fun n ↦ a (n + m)) L := by
  sorry

/-! 6.1.4 与6.1.5没有本质区别。

6.1.5 证明[命题6.1.12](#6.1.12)。

6.1.6 证明[命题6.1.15](#6.1.15)。

6.1.7 证明[定义6.1.16](#6.1.16)与定义5.1.12兼容。

6.1.8 证明[定理6.1.19](#6.1.19)。

6.1.9 说明为什么定理6.1.19(f)在$y=0$时失效。

6.1.10 证明允许定义5.2.6中的$\varepsilon$取正实数不影响有理数柯西列等价类的定义。
-/
