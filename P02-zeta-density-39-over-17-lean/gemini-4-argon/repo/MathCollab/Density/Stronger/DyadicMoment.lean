module
/-
Selected proof slices adapted from Scott McColm, MIT-0,
commit 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
See ../../../../third_party/twelfth/SOURCE_IMPORTS.json and LICENSE-MIT-0.
No upstream project or Architect module is imported.
-/
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Filter Set
open scoped Interval ENNReal Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

theorem exists_dyadic_cutoff {X : ℝ} (hX : 1 ≤ X) :
    ∃ M : ℕ, X ≤ (2:ℝ)^M ∧ (2:ℝ)^M ≤ 2*X := by
  obtain ⟨m,hm,hupper⟩ := exists_nat_pow_near hX (by norm_num : (1:ℝ)<2)
  refine ⟨m+1,hupper.le,?_⟩
  rw [pow_succ']
  exact mul_le_mul_of_nonneg_left hm (by norm_num)

theorem exists_dyadic_count_sq_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ M : ℕ, ((M:ℝ)+1)^2 ≤ D*((2:ℝ)^M)^ε := by
  let a : ℝ := ε/2
  have ha : 0 < a := by dsimp [a]; positivity
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C : ℝ := 1+1/(a*Real.log 2)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C^2,pow_pos hC 2,?_⟩
  intro M
  have hp : 1 ≤ ((2:ℝ)^M)^a :=
    Real.one_le_rpow (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) ha.le
  have hl := Real.log_le_rpow_div (by positivity : (0:ℝ) ≤ (2:ℝ)^M) ha
  rw [Real.log_pow] at hl
  have hm : (M:ℝ) ≤ ((2:ℝ)^M)^a/(a*Real.log 2) := by
    apply (le_div_iff₀ (mul_pos ha hlog)).mpr
    have h := (le_div_iff₀ ha).mp hl
    nlinarith
  have hcount : (M:ℝ)+1 ≤ C*((2:ℝ)^M)^a := by
    calc
      _ ≤ ((2:ℝ)^M)^a/(a*Real.log 2)+((2:ℝ)^M)^a := add_le_add hm hp
      _ = _ := by dsimp [C]; ring
  calc
    _ ≤ (C*((2:ℝ)^M)^a)^2 :=
      pow_le_pow_left₀ (by positivity) hcount 2
    _ = _ := by
      rw [mul_pow,← Real.rpow_mul_natCast (by positivity : (0:ℝ) ≤ (2:ℝ)^M)]
      congr 2
      dsimp [a]
      norm_num





