import Mathlib.Tactic --#

/- # 柯西列
一个有理数序列$(a_n)_{n=0}^{+\infty}$就是一个从$\mathbb{N}$到$\mathbb{Q}$的函数（书中定义5.1.1）。-/
def square : ℕ → ℚ
  | n => n ^ 2

def constant (c : ℚ) : ℕ → ℚ
  | _ => c

/-! 为了研究序列的收敛性，定义$\varepsilon-$稳定。
称一个有理数序列是$\varepsilon-$稳定的，如果序列中任意两个有理数是$\varepsilon-$邻近的，
也即任意两个数的距离小于等于$\varepsilon$。-/
def steady (ε : ℚ) (a : ℕ → ℚ) :=
  ∀ j k : ℕ, |a j - a k| ≤ ε

/-!
>注意：$\varepsilon-$稳定并非标准术语，只是《陶哲轩实分析》一书为了方便行文搭建的脚手架。
>下面的最终$\varepsilon-$稳定也不是标准术语。

要求一个有理数序列$\varepsilon-$稳定过于严苛，
实际上我们只关心序列下标充分大时序列的性质，
为此定义一个有理数序列是最终$\varepsilon-$稳定的，
如果当下标充分大时它是$\varepsilon-$稳定的。
-/
def eventuallySteady (ε : ℚ) (a : ℕ → ℚ) :=
  ∃ N : ℕ, ∀ j k : ℕ, N ≤ j → N ≤ k → |a j - a k| ≤ ε

/-! 有了上述铺垫就可以来正式定义柯西列。
称一个有理数序列是柯西列，如果对于任意$\varepsilon>0$，该序列都是最终$\varepsilon$稳定的。
这与Lean中的定义不同，但二者是等价的。-/
example (a : ℕ → ℚ) : (∀ ε > 0, eventuallySteady ε a) → IsCauSeq (abs : ℚ → ℚ) a := by
  unfold eventuallySteady IsCauSeq
  intro h ε hε
  specialize h (ε / 2) (half_pos hε)
  obtain ⟨N, h⟩ := h
  use N
  intro j hj
  specialize h j N hj (Nat.le_refl N)
  exact lt_of_le_of_lt h (div_two_lt_of_pos hε)

example (a : ℕ → ℚ) : IsCauSeq (abs : ℚ → ℚ) a → ∀ ε > 0, eventuallySteady ε a := by
  unfold eventuallySteady IsCauSeq
  intro h ε hε
  specialize h (ε / 2) (half_pos hε)
  obtain ⟨N, h⟩ := h
  use N
  intro j k hj hk
  have : |a j - a N| + |a k - a N| < ε := by
    rw [← add_halves ε]
    exact add_lt_add (h j hj) (h k hk)
  refine le_trans ?_ (le_of_lt this)
  rw [show a j - a k = (a j - a N) - (a k - a N) by ring]
  apply abs_sub

/- 可以证明调和数列是柯西列（书中命题5.1.11）。-/
example : IsCauSeq (abs : ℚ → ℚ) (fun n ↦ (n + 1)⁻¹) := by
  unfold IsCauSeq; simp
  intro ε hε
  let N := Nat.floor (ε⁻¹) + 1
  use N
  intro j hj
  have : |(N + (1 : ℚ))⁻¹ - (j + (1 : ℚ))⁻¹| =
    (N + (1 : ℚ))⁻¹ - (j + (1 : ℚ))⁻¹
  := by
    apply abs_of_nonneg
    rw [← Rat.le_iff_sub_nonneg]
    apply inv_le_inv_of_le  <;> norm_cast <;> omega
  rw [abs_sub_comm, this]
  have : (N + (1 : ℚ))⁻¹ - (j + (1 : ℚ))⁻¹ < (N + (1 : ℚ))⁻¹ := by
    apply sub_lt_self; apply inv_pos_of_pos; norm_cast; omega
  apply lt_trans this
  have : ε⁻¹ < N + 1 := by
    apply lt_trans (Nat.lt_succ_floor ε⁻¹)
    exact_mod_cast lt_add_one N
  rwa [← inv_lt_inv, inv_inv ε] at this
  . exact_mod_cast Nat.zero_lt_succ N
  . exact inv_pos_of_pos hε

/-! # 有界序列
称一个有理数序列$(a_n)_{n=0}^{+\infty}$是有界的，如果存在有理数$M\geq 0$使得（书中定义5.1.12）：
$$∀ n\in\mathbb{N}, |a_n| ≤ M$$
在Lean中定义如下。
-/
def Bounded (a : ℕ → ℚ) :=
  ∃ M ≥ 0, ∀ n : ℕ, |a n| ≤ M

/-! 显然有理数的有限序列是有界的。-/
example (a : List ℚ) (ha : a.length > 0) :
  ∀ x ∈ a, x ≤ a.maximum_of_length_pos ha
:= by
  intro x hx
  apply List.le_maximum_of_mem hx
  rw [← List.coe_maximum_of_length_pos ha]

/-! 显然柯西列是有界的（书中<a name="5.1.15"></a>**引理5.1.15**），
注意在Lean中有界定义为严格小于。-/
#check (IsCauSeq.bounded : ∀ {a : ℕ → ℚ}, IsCauSeq (abs : ℚ → ℚ) a →
  ∃ M : ℚ, ∀ n : ℕ, |a n| < M)

/-! # 习题
5.1.1 证明[引理5.1.5](#5.1.5)。
-/
