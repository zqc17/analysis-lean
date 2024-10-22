import Mathlib.Tactic --#

/-! # 有理数的间隙
我们知道有理数的小于等于关系是一个线性序，
而整数散列其中（书中<a name="4.4.1"></a>**命题4.4.1**）。
-/
example (x : ℚ) : ∃ n : ℤ, n ≤ x ∧ x < n + 1 := by
  use ⌊x⌋
  constructor
  . rw [← Rat.le_floor]
    apply le_refl
  simp

/-! 并且有理数是稠密的，也即任意两个有理数之间总存在第三个有理数（书中命题4.4.3）。-/
#check (exists_rat_btwn : ∀ {x y : ℚ}, x < y → ∃ z, x < z ∧ z < y)

/-! 尽管有理数是稠密的，但是有理数是不完备的。
直观上讲就是有理数存在间隙，一个经典的例子是$\sqrt{2}$的无理性
（书中<a name="4.4.4"></a>**命题4.4.4**）。
-/
theorem Prop444 : ∀ x : ℚ, x ^ 2 ≠ 2 := by
  intro x h
  have : IsSquare (2 : ℚ) := Exists.intro x (by rw [pow_two] at h; exact h.symm)
  have : IsSquare (2 : ℕ) := Rat.isSquare_natCast_iff.mp this
  have : ¬IsSquare (2 : ℕ) := Irreducible.not_square Nat.prime_two
  contradiction

-- 书中采用奇偶分析+无穷递降
#check (neg_pow_two : ∀ x : ℚ, (-x) ^ 2 = x ^ 2)
#check (Nat.even_or_odd : ∀ n : ℕ, Even n ∨ Odd n)
#check (Nat.not_odd_iff_even : ∀ {n : ℕ}, ¬Odd n ↔ Even n)
#check (Nat.not_even_iff_odd : ∀ {n : ℕ}, ¬Even n ↔ Odd n)
#check (Odd.pow : ∀ {n : ℕ}, Odd n → ∀ m, Odd (n ^ m))

example (p q : ℕ) (hq : 0 < q) : p ^ 2 = 2 * q ^ 2 → q < p := by
  intro h
  have : q ^ 2 < p ^ 2 := by
    rw [← Nat.add_zero (q ^ 2), h, two_mul]
    apply Nat.add_lt_add_left
    exact Nat.pos_pow_of_pos 2 hq
  exact lt_of_pow_lt_pow_left' 2 this

/-! 虽然$\sqrt{2}$不是有理数，但是有理数可以任意逼近$\sqrt{2}$（书中命题4.4.5）。-/
example (ε : ℚ) (hε : ε > 0) : ∃ x, x ^ 2 < 2 ∧ 2 < (x + ε) ^ 2 := by
  by_contra h
  push_neg at h
  have hn : ∀ n : ℕ, (ε * n) ^ 2 < 2 := by
    intro n
    induction n with
    | zero => norm_cast; rw [Rat.mul_zero]; decide
    | succ n ihn =>
      specialize h (ε * n) ihn
      apply lt_of_le_of_ne
      . nth_rewrite 2 [← Rat.mul_one ε] at h
        rw [← Rat.mul_add] at h
        exact_mod_cast h
      apply Prop444
  let n := Nat.floor (2 / ε) + 1
  have : 2 / ε < n := by exact_mod_cast Nat.lt_floor_add_one (2 / ε)
  have : 2 < ε * n := (div_lt_iff' hε).mp this
  have : 2 < (ε * n) ^ 2 := by
    apply lt_trans (show (2 : ℚ) < 2 ^ 2 by decide)
    rw [sq_lt_sq]
    rw [abs_of_pos (show 0 < ε * n from lt_trans (by decide) this)]
    exact_mod_cast this
  have : 2 < (2 : ℚ) := lt_trans this (hn n)
  contradiction

/-! # 习题
4.4.1 证明[命题4.4.1](#4.4.1)。

4.4.2 证明自然数满足降链条件，整数、正有理数不满足降链条件。

（在Lean中用`WellFoundedRelation`表示降链条件。）
-/
#check (Nat.lt_wfRel : WellFoundedRelation Nat)

/-! 整数的小于关系是不满足降链条件的。-/
example : ∃ f : ℕ → ℤ, ∀ n, f n > f (n + 1) := by
  use fun n => -n; simp

/-! 正有理数的小于关系也是不满足降链关系的。-/
example : ∃ f : ℕ → ℚ, (∀ n, f n > 0) ∧ (∀ n, f n > f (n + 1)) := by
  use fun n => 1 / (n + 1); simp
  constructor
  . intro n
    exact_mod_cast Nat.zero_lt_succ n
  intro n
  rw [inv_lt_inv]
  exact_mod_cast Nat.lt_add_one (n + 1)
  exact_mod_cast Nat.zero_lt_succ (n + 1)
  exact_mod_cast Nat.zero_lt_succ n

/-! 4.4.3 证明[命题4.4.4](#4.4.4)。-/
