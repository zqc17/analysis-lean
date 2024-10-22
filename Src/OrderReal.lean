import Mathlib.Tactic --#

/-! # 实数的序

定义一个有理数序列是正远离零的和负远离零的（书中定义5.4.1）。-/
def posAwayZero (a : ℕ → ℚ) :=
  ∃ c > 0, ∀ n, a n ≥ c

def negAwayZero (a : ℕ → ℚ) :=
  ∃ c > 0, ∀ n, a n ≤ -c

/-! 称一个实数是正的如果它对应的柯西列的等价类中存在一个正远离零的；
称一个实数是负的如果它对应的柯西列的等价类中存在一个负远离零的（书中定义5.4.3）。

这与Lean中定义有所不同。Lean中定义一个柯西列是正的如果存在正有理数$K$以及自然数$i$使得：
$$a_j \geq K,\quad j=i,i+1,\cdots$$
-/
example (a : CauSeq ℚ (abs : ℚ → ℚ)) :
  CauSeq.Pos a ↔ ∃ K > 0, ∃ i, ∀ j ≥ i, K ≤ a j := by rfl

/-! 可以证明实数具有三歧性（书中命题5.4.4）。-/
example (a : CauSeq ℚ (abs : ℚ → ℚ)) :
  a.Pos ∨ a.LimZero ∨ (-a).Pos := CauSeq.trichotomy a

example (x : ℝ) : 0 < x ∨ 0 = x ∨ x < 0 := lt_trichotomy 0 x

/-! 实数的绝对值定义如下（书中定义5.4.5）。-/
#check (abs_of_pos : ∀ {x : ℝ}, 0 < x → |x| = x)
#check (abs_of_neg : ∀ {x : ℝ}, x < 0 → |x| = -x)
#check (abs_eq_zero : ∀ {x : ℝ}, |x| = 0 ↔ x = 0)

/-! # 小于
称实数$y$小于$x$如果$x-y$是正的（书中定义5.4.6）。这与Lean中的定义类似。-/
example (a b : CauSeq ℚ (abs : ℚ → ℚ)) :
  a < b ↔ (b - a).Pos := by rfl

/-! 实数的小于关系满足于有理数相同的性质（书中命题5.4.7），这使得实数成为一个有序域。-/
#check (lt_trichotomy : ∀ x y : ℝ, x < y ∨ x = y ∨ y < x)
example (x y : ℝ) : x < y ↔ y > x := Eq.to_iff rfl
#check (lt_trans : ∀ {x y z : ℝ}, x < y → y < z → x < z)
#check (add_lt_add_iff_right : ∀ z : ℝ, ∀ {x y : ℝ}, x + z < y + z ↔ x < y)
#check (mul_lt_mul_iff_of_pos_right : ∀ {z y x : ℝ}, 0 < z → (x * z < y * z ↔ x < y))

/-! 利用上述性质可以证明正实数的倒数还是正实数，以及倒数使不等式反向（书中命题5.4.8）。-/
example (x : ℝ) : 0 < x⁻¹ ↔ 0 < x := inv_pos
example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x⁻¹ < y⁻¹ ↔ y < x := inv_lt_inv hx hy

/-! 可以证明两个正实数的和还是正实数（书中命题5.4.9）。-/
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x + y := add_nonneg hx hy

/-! 由上述命题可以得到如下推论（书中推论5.4.10）。-/
open CauSeq.Completion in
example (a b : CauSeq ℚ (abs : ℚ → ℚ)) :
  ∀ n, b n ≤ a n → (⟨mk b⟩ : ℝ) ≤ (⟨mk a⟩ : ℝ) := by sorry

/-! 可以证明正实数总是小于某个正整数，大于某个正有理数（书中命题5.4.12）。-/
example (x : ℝ) : ∃ N : ℕ, ∃ q : ℚ, q ≤ x ∧ x ≤ N := by sorry

/-! 由上述命题可以得到推论：实数具有阿基米德性（书中推论5.4.13）。-/
example (x ε : ℝ) (hx : 0 < x) (hε : 0 < ε) : ∃ M : ℕ, 0 < M ∧ x < M * ε := by sorry

/-! 可以证明任意两个不等实数间总存在一个有理数（书中命题5.4.14）。-/
example (x y : ℝ) (h : x < y) : ∃ q : ℚ, x < q ∧ q < y := by sorry

/-! # 习题
5.4.1 证明[命题5.4.4](#5.4.4)。

5.4.2 证明[命题5.4.7](#5.4.7)。

5.4.3 证明实数可以定义下取整$\lfloor x \rfloor$。
-/
example (x : ℝ) : ⌊x⌋ ≤ x := Int.floor_le x
example (x : ℝ) : x < ⌊x⌋ + 1 := Int.lt_floor_add_one x

/-! 5.4.4 证明对任意正实数$x$都存在正整数$N$使得$x > 1 / N$。 -/
example (x : ℝ) (hx : 0 < x) : ∃ N : ℕ, 0 < N ∧ 1 / N < x := by sorry

/-! 5.4.5 证明[命题5.4.14](#5.4.14)。

5.4.6 设$x,y\in\mathbb{R}$，$\varepsilon\in\mathbb{R}^{+}$。证明$|x-y|<\varepsilon$
当且仅当$y-\varepsilon < x < y+\varepsilon$。
$|x-y|\leq\varepsilon$当且仅当$y-\varepsilon \leq x \leq y+\varepsilon$。
-/
example (x y ε: ℝ) : |x - y| < ε ↔ y - ε < x ∧ x < y + ε := by
  rw [abs_sub_lt_iff]
  constructor <;> intro _ <;> constructor <;> linarith

example (x y ε: ℝ) : |x - y| ≤ ε ↔ y - ε ≤ x ∧ x ≤ y + ε := by
  rw [abs_sub_le_iff]
  constructor <;> intro _ <;> constructor <;> linarith

/-! 5.4.7 设$x,y\in\mathbb{R}$。
证明$x\leq y$当且仅当对任意$\varepsilon>0$都有$x\leq y+\varepsilon$。
$x=y$当且仅当对任意$\varepsilon>0$都有$|x-y|<\varepsilon$。-/
example (x y : ℝ) : (∀ ε > 0, x ≤ y + ε) ↔ x ≤ y := by
  constructor
  . intro h
    contrapose! h
    use (x - y) / 2
    constructor
    . apply half_pos
      rwa [sub_pos]
    linarith
  intro h ε hε
  linarith

/-! 5.4.8 设$(a_n)_{n=0}^{+\infty}$是一个柯西列，如果它的每一项都小于等于实数$x$，
则该柯西列对应的实数小于等于$x$。-/
open CauSeq.Completion in
example (a : CauSeq ℚ (abs : ℚ → ℚ)) (x : ℝ) :
  ∀ n, a n ≤ x → (⟨mk a⟩ : ℝ) ≤ x := by sorry
