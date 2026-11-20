module

public import Mathlib

/-! # The exponents and parameter hypotheses in Wu 2008, Lemma 2.2 -/

@[expose] public noncomputable section
namespace GoldbachLean.Wu2008.WuReal

def wk1 : ℝ := 100 / 1327
def wk2 : ℝ := 100 / 824
def em (k1 : ℝ) : ℝ := 1 / 2 - 3 * k1
def e13 : ℝ := 1 / 3

def Admissible (k1 k2 : ℝ) :=
  1 / 18 ≤ k1 ∧ k1 < k2 ∧ 3 * k1 + k2 < 1 / 2 ∧ 3 * k1 - k2 ≤ 1 / 6

lemma wu_admissible : Admissible wk1 wk2 := by norm_num [Admissible, wk1, wk2]

end GoldbachLean.Wu2008.WuReal
