import Mathlib.Tactic --#

/-! # 等价序列
定义两个有理数序列$(a_n)\_{n=0}^{+\infty},(b_n)\_{n=0}^{+\infty}$
是$\varepsilon-$邻近的，
如果对任意自然数$n$有$a_n,b_n$是$\varepsilon-$邻近的（书中定义5.2.1）。-/
def close (ε : ℚ) (a b : ℕ → ℚ) :=
  ∀ n, |a n - b n| ≤ ε

/-! 定义两个有理数序列是最终$\varepsilon-$邻近的，
如果对于充分大的下标它们是$\varepsilon-$邻近的（书中定义5.2.3）。-/
def eventuallyClose (ε : ℚ) (a b : ℕ → ℚ) :=
  ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε

/-! 称两个有理数序列是等价的如果对于任意$\varepsilon>0$它们是最终$\varepsilon-$邻近的
（书中定义5.2.6）。-/
def equivSeq (a b : ℕ → ℚ) :=
  ∀ ε > 0, eventuallyClose ε a b

/-! 可以验证下述两个有理数序列是等价的（书中命题5.2.8）。-/
example : equivSeq (fun n ↦ 1 + 10⁻¹ ^ (n + 1)) (fun n ↦ 1 - 10⁻¹ ^ (n + 1)) := by
  unfold equivSeq eventuallyClose; simp
  intro ε hε
  let N := Nat.floor (2 / ε) + 1
  use N
  intro n hn
  have : 2 / N < ε := by
    rw [div_lt_comm₀]
    . exact Nat.lt_succ_floor (2 / ε)
    . exact_mod_cast Nat.zero_lt_succ _
    . exact hε
  refine le_trans ?_ (le_of_lt this)
  have : (0 : ℚ) ≤ 2 * (10 ^ (n + 1))⁻¹ := by
    rw [mul_nonneg_iff_of_pos_left (by decide)]
    rw [inv_nonneg]
    exact_mod_cast Nat.zero_le _
  rw [← two_mul, abs_of_nonneg this]
  rw [show 2 / N = 2 * (N : ℚ)⁻¹ from rfl]
  rw [mul_le_mul_left (show (0 : ℚ) < 2 by decide)]
  rw [inv_le_inv]
  case h.ha => exact pow_pos rfl (n + 1)
  case h.hb => exact_mod_cast Nat.zero_lt_succ _
  norm_cast
  apply le_trans hn
  apply le_trans (show n ≤ n + 1 from Nat.le_succ n)
  apply le_of_lt
  apply Nat.lt_pow_self
  decide

/-! # 习题
5.2.1 证明柯西列的等价序列也是柯西列。-/
example (a b : ℕ → ℚ) (h : equivSeq a b) :
    IsCauSeq (abs : ℚ → ℚ) a → IsCauSeq (abs : ℚ → ℚ) b := by
  unfold equivSeq eventuallyClose at h
  unfold IsCauSeq
  intro ha ε hε
  specialize h (ε / 4) (div_pos hε rfl)
  specialize ha (ε / 4) (div_pos hε rfl)
  obtain ⟨N1, h⟩ := h
  obtain ⟨N2, ha⟩ := ha
  let N := max N1 N2
  use N
  intro j hj
  have : |b j - b N| ≤ |a j - b j| + |a j - b N| := by
    rw [abs_sub_comm (a j)]
    rw [show b j - b N = (b j - a j) + (a j - b N) by ring]
    apply abs_add
  have : |a j - b N| ≤ |a j - a N| + |a N - b N| := by
    rw [show a j - b N = a j - a N + (a N - b N) by ring]
    apply abs_add
  have : |a j - a N| ≤ |a j - a N2| + |a N - a N2| := by
    rw [abs_sub_comm (a N)]
    rw [show a j - a N = a j - a N2 + (a N2 - a N) by ring]
    apply abs_add
  have : |b j - b N| ≤ |a j - b j| + |a N - b N| + |a j - a N2| + |a N - a N2| := by
    linarith
  apply lt_of_le_of_lt this
  have : |a N - b N| ≤ ε / 4 := h N (Nat.le_max_left N1 N2)
  have : |a j - b j| ≤ ε / 4 := h j (Nat.le_trans (Nat.le_max_left N1 N2) hj)
  have : |a j - a N2| < ε / 4 := ha j (Nat.le_trans (Nat.le_max_right N1 N2) hj)
  have : |a N - a N2| < ε / 4 := ha N (Nat.le_max_right N1 N2)
  linarith

/-！5.2.2 设$\varepsilon>0$，证明与有界序列最终$\varepsilon-$邻近的序列也是有界序列。-/
example (a b : ℕ → ℚ) (ha : ∃ M, ∀ n, a n < M) :
    (∃ ε > 0, eventuallyClose ε a b) → ∃ M, ∀ n, b n < M := by
  unfold eventuallyClose
  rintro ⟨ε, ⟨hε, ⟨N, h⟩⟩⟩
  obtain ⟨M, ha⟩ := ha
  cases N with
  | zero =>
    use M + ε
    intro n
    have : b n ≤ |a n - b n| + a n := by
      nth_rw 1 [show b n = b n - a n + a n by ring]
      rw [add_le_add_iff_right, abs_sub_comm]
      apply le_abs_self
    apply lt_of_le_of_lt this
    have : a n < M := ha n
    have : |a n - b n| ≤ ε := h n (Nat.zero_le _)
    linarith
  | succ N =>
    let f (n : Fin (N + 1)) : ℚ := |a n - b n|
    let l := List.ofFn f
    have : 0 < l.length := by
      rw [List.length_ofFn f]
      apply Nat.zero_lt_succ
    let maxl := l.maximum_of_length_pos this
    use M + max ε maxl
    intro n
    have : b n ≤ |a n - b n| + a n := by
      nth_rw 1 [show b n = b n - a n + a n by ring]
      rw [add_le_add_iff_right, abs_sub_comm]
      apply le_abs_self
    apply lt_of_le_of_lt this
    have : a n < M := ha n
    have : |a n - b n| ≤ max ε maxl := by
      cases Nat.lt_or_ge n (N + 1) with
      | inl hN =>
        refine le_trans ?_ (show maxl ≤ max ε maxl from le_max_right _ _)
        have : |a n - b n| ∈ l := by
          rw [List.mem_ofFn f]
          use n
          unfold_let f; simp
          rw [Nat.mod_eq_of_lt hN]
        apply List.le_maximum_of_mem this
        apply Eq.symm
        apply List.coe_maximum_of_length_pos
      | inr hN =>
        refine le_trans ?_ (show ε ≤ max ε maxl from le_max_left _ _)
        exact h n hN
    linarith
