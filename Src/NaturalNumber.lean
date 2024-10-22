import Mathlib.Data.Nat.Notation --#

/- # 皮亚诺公理
皮亚诺公理包含以下5条（书中公理2.1-2.5）。
1. $0$是自然数；
2. 每个自然数$n$都有唯一的后继$n++$；
3. 每个自然数的后继均不等于$0$；
4. 若两个自然数后继相等，则它们自身也相等；
5. （归纳公理）设$P(n)$为关于自然数的性质。有数学归纳法如下：
  $$P(0)\land (P(n)\to P(n++)) \implies P(n)$$

在Lean中如下表示。
-/
variable (n : ℕ)

#check (0 : ℕ) -- 公理一
#check (n.succ : ℕ) -- 公理二
#check (Nat.succ_ne_zero : ∀ n : ℕ, n.succ ≠ 0) -- 公理三
#check (Nat.succ.inj : ∀ {n m : ℕ}, n.succ = m.succ → n = m) -- 公理四
#check (Nat.rec : ∀ {P : ℕ → Prop}, P 0 → (∀ n, P n → P n.succ) → ∀ n, P n) -- 公理五（归纳公理）

/-! 在Lean中自然数是如下归纳类型。
```lean
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
```
在Lean中使用`rfl`验证两个对象是否依定义相等（Definitional equality），
例如下面几个例子（书中定义2.1.3）。
-/
example : 1 = Nat.succ 0 := rfl
example : 2 = Nat.succ 1 := rfl
example : 3 = Nat.succ 2 := rfl

/-! 利用公理三可以证明一些自然数不等于零，例如下面这个例子（书中命题2.1.3）。-/
example : 4 ≠ 0 := by
  have : 4 = Nat.succ 3 := rfl
  rw [this]
  exact Nat.succ_ne_zero 3

/-! 结合公理三和公理四，可以判定任意两个自然数是否相等，例如下面这个例子（书中命题2.1.6）。-/
example : 6 ≠ 2 := by
  intro h
  have h6 : 6 = Nat.succ 5 := rfl
  have h5 : 5 = Nat.succ 4 := rfl
  have h4 : 4 = Nat.succ 3 := rfl
  have h3 : 3 = Nat.succ 2 := rfl
  have h2 : 2 = Nat.succ 1 := rfl
  have h1 : 1 = Nat.succ 0 := rfl
  rw [h6, h2] at h
  have : 5 = 1 := Nat.succ.inj h
  rw [h5, h1] at this
  have : 4 = 0 := Nat.succ.inj this
  rw [h4] at this
  exact Nat.succ_ne_zero 3 this

/-! 当自然数很大的时候，手写上面这种证明是不可接受的，
幸运的是在Lean中可以用`decide`验证一些可判定的命题。-/
example : 4 ≠ 0 := by decide
example : 6 ≠ 2 := by decide
example : 50 ≠ 100 := by decide

/-! 在Lean中可以通过如下方式书写数学归纳法（书中命题2.1.11）。-/
example {P : ℕ → Prop} (h0: P 0) (h1: ∀ n, P n → P n.succ) : ∀ n, P n := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ihn => exact h1 n ihn
