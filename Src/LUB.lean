import Mathlib.Tactic --#

/-! # 最小上界
设$E$为实数集的一个子集，若对$E$中的任意实数$x$均有$x\leq M$，
则称$M$为$E$的一个上界（书中定义5.5.1）。
-/
example (E : Set ℝ) (M : ℝ) : M ∈ upperBounds E ↔ ∀ x, x ∈ E → x ≤ M := mem_upperBounds

/-! 称$M$是实数集合$E$的最小上界，如果$M$是$E$的上界，并且不存在比$M$更小的上界（书中定义5.5.5）。-/
example (E : Set ℝ) (M : ℝ) : IsLUB E M = IsLeast (upperBounds E) M := rfl

/-! 显然最小上界如果存在则一定唯一（书中命题5.5.8）。-/
theorem Prop558 {E : Set ℝ} {M1 M2 : ℝ} : IsLUB E M1 → IsLUB E M2 → M1 = M2 := by
  have : ∀ {M1 M2 : ℝ}, IsLUB E M1 → IsLUB E M2 → M1 ≤ M2 := by
    intro M1 M2 h1 h2
    rw [isLUB_iff_le_iff] at h1
    rw [h1 M2]
    exact Set.mem_of_mem_inter_left h2
  intro h1 h2
  apply le_antisymm
  . exact this h1 h2
  . exact this h2 h1

/-! 可以证明实数的重要性质：若非空实数集合$E$有上界，则必定有唯一最小上界（书中定理5.5.9）。-/
example (E : Set ℝ) (hne : E.Nonempty) (hbdd : BddAbove E) :
  ∃ M, IsLUB E M := Real.exists_isLUB hne hbdd

/-! 有了上述定理就可以定义上确定界。
如果一个非空实数集合$E$具有上界，那么称它的最小上界为上确界，记为$\mathrm{sup }E$（书中定义5.5.10）。
注意在Lean中当$E$不存在上确界时`sSup E = 0`。-/
example (E : Set ℝ) (hne : E.Nonempty) (hbdd : BddAbove E) :
  IsLUB E (sSup E) := Real.isLUB_sSup E hne hbdd

/-! 利用上确界我们可以证明存在正实数的平方是$2$（书中命题5.5.12）。-/
example : ∃ x : ℝ, 0 < x ∧ x ^ 2 = 2 := by
  let E := {y : ℝ | 0 ≤ y ∧ y ^ 2 < 2}
  have hne : E.Nonempty := by use 1; simp [E]
  have hbdd : BddAbove E := by
    use 2; simp [upperBounds, E]
    intro a ha1 ha2
    have : a ^ 2 ≤  2 ^ 2 := le_trans (le_of_lt ha2) (show 2 ≤ 2 ^ 2 by norm_num)
    rwa [pow_le_pow_iff_left] at this
    . exact ha1
    . norm_num
    . norm_num
  obtain ⟨M, hM⟩ := Real.exists_isLUB hne hbdd
  use M
  constructor
  . have hE : 1 ∈ E := by simp [E]
    have := Set.mem_of_mem_inter_left hM
    simp [upperBounds] at this
    specialize this hE
    exact lt_of_lt_of_le (by norm_num) this
  by_contra h
  rcases lt_trichotomy (M ^ 2) 2 with h | h | h
  -- M^2 < 2
  have : ∀ ε, 0 < ε → ε < 1 → (M+ε)^2 < M^2 + 5*ε := by
    intro ε hε0 hε1
    have : 2*ε*M ≤ 4*ε := sorry
    have : ε^2 < ε := sorry
    linarith
  have : ∃ ε > 0, M + ε ∈ E := by
    let ε  := (2 - M ^ 2) / 5
    use ε
    constructor
    sorry
    simp [E]
    constructor
    sorry
    rw [show 2 = M^2 + 5*ε by ring]
    apply this
    . sorry
    . sorry
  obtain ⟨ε , ⟨hε, hMε⟩⟩ := this
  have : M ∈ upperBounds E := Set.mem_of_mem_inter_left hM
  simp [upperBounds] at this
  have : M + ε ≤ M := by
    have := Set.mem_of_mem_inter_left hM
    simp [upperBounds] at this
    exact this hMε
  linarith
  . contradiction
  . have : ∃ ε > 0, IsLUB E (M - ε) := sorry
    obtain ⟨ε, hε⟩ := this
    have : M - ε = M := Prop558 hε.right hM
    linarith

/-! # 习题
5.5.1 设$E$具有有限的上确界$M$，证明集合$\{-x | x\in E\}$具有有限的下确界$-M$。-/

/-! 5.5.2-/
