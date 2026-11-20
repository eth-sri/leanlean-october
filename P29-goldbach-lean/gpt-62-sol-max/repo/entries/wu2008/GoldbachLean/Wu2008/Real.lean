module

public import Mathlib

/-! # Wu's admissible parameters -/

namespace GoldbachLean.Wu2008.WuReal
@[expose] public noncomputable section

def wk1 : ℝ := 100 / 1327
def wk2 : ℝ := 100 / 824
def em (k : ℝ) : ℝ := 1 / 2 - 3 * k
def e13 : ℝ := 1 / 3

def Admissible (k l : ℝ) : Prop :=
  1 / 18 ≤ k ∧ k < l ∧ 3 * k + l < 1 / 2 ∧ 3 * k - l ≤ 1 / 6

lemma wu_admissible : Admissible wk1 wk2 := by norm_num [Admissible, wk1, wk2]

end
end GoldbachLean.Wu2008.WuReal
