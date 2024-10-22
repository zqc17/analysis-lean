import Mathlib.Tactic --#
import Mathlib

/-! # 扩展实数系
向实数添加两个额外对象$-\infty,+\infty$，得到的数系成为扩展实数系（书中定义6.2.1）。-/
#check (⊥ : EReal) -- 负无穷
#check (⊤ : EReal) -- 正无穷
example : (⊥ : EReal) ≠ (⊤ : EReal) := bot_ne_top

/-! 定义正无穷的相反数为负无穷，负无穷的相反数为正无穷（书中定义6.2.2）。-/
example : -(⊤ : EReal) = ⊥ := rfl
example : -(⊥ : EReal) = ⊤ := rfl

/-! 规定负无穷小于任何有限的实数，正无穷大于任何有限的实数（书中定义6.2.23）。-/
example (x : ℝ) : (⊥ : EReal) < x := EReal.bot_lt_coe x
example (x : ℝ) : x < (⊤ : EReal) := EReal.coe_lt_top x

/-! 按上述定义可以验证扩展实数系的小于等于关系满足下述性质（书中<a name="6.2.5"></a>**命题6.2.5**）。-/
example (x : EReal) : x ≤ x := le_refl _
example (x y : EReal) : x < y ∨ x = y ∨ y < x := lt_trichotomy _ _
example (x y z : EReal) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := le_trans hxy hyz
example (x y : EReal) (hxy : x ≤ y) : -y ≤ -x := EReal.neg_le_neg_iff.mpr hxy

/-! 定义扩展实数系集合的上确界如下（书中定义6.2.6）。-/
example (E : Set EReal) (hE : (⊤ : EReal) ∈ E) : sSup E = (⊤ : EReal) := sup_eq_top_of_top_mem hE
--？

/-! 拓展实数系集合的上确界和下确界满足以下性质（书中<a name="6.2.11"></a>**定理6.2.11**）。-/
example (E : Set EReal) (x : EReal) (hx : x ∈ E) : x ≤ sSup E := CompleteLattice.le_sSup E x hx
example (E : Set EReal) (x : EReal) (hx : x ∈ E) : sInf E ≤ x := CompleteLattice.sInf_le E x hx
example (E : Set EReal) (M : EReal) (hM : M ∈ upperBounds E) : sSup E ≤ M := CompleteSemilatticeSup.sSup_le E M hM
example (E : Set EReal) (M : EReal) (hM : M ∈ lowerBounds E) : M ≤ sInf E := CompleteLattice.le_sInf E M hM

/-! # 习题
6.2.1 证明[命题6.2.5](#6.2.5)。

6.2.2 证明[定理6.2.11](#6.2.11)。-/
