module
public import Glennie.Native.AlgebraLaws
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Tactic.Module

@[expose] public section
namespace Glennie
noncomputable section

def jordanLinear : Albert →ₗ[ℝ] Albert →ₗ[ℝ] Albert where
  toFun x :=
    { toFun := jordan x
      map_add' := jordan_add_right x
      map_smul' := fun r y => jordan_smul_right r x y }
  map_add' x y := LinearMap.ext (jordan_add_left x y)
  map_smul' r x := LinearMap.ext (jordan_smul_left r x)

def traceLinear : Albert →ₗ[ℝ] ℝ where
  toFun := trace
  map_add' := trace_add
  map_smul' := trace_smul

@[simp] theorem jordanLinear_apply (x y : Albert) : jordanLinear x y = jordan x y := rfl
@[simp] theorem traceLinear_apply (x : Albert) : traceLinear x = trace x := rfl

def cubicResidual (x : Albert) : Albert :=
  (6 : ℝ) • jordan x (jordan x x) - (6 * trace x) • jordan x x +
    (3 * (trace x) ^ 2 - 3 * trace (jordan x x)) • x -
    ((trace x) ^ 3 - 3 * trace x * trace (jordan x x) + 2 * trace (jordan x (jordan x x))) • (1 : Albert)

set_option maxHeartbeats 8000000 in
theorem cubicResidual_eq_zero (x : Albert) : cubicResidual x = 0 := by
  ext <;> simp [cubicResidual, jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12, trace,
    octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, smul_eq_mul] <;> ring

private def linearResidual (x y : Albert) : Albert :=
  (4 : ℝ) • jordan x (jordan x y) + (2 : ℝ) • jordan (jordan x x) y -
    (2 * trace y) • jordan x x - (4 * trace x) • jordan x y +
    (2 * trace x * trace y - 2 * trace (jordan x y)) • x +
    ((trace x) ^ 2 - trace (jordan x x)) • y -
    (((trace x) ^ 2 - trace (jordan x x)) * trace y -
      2 * trace x * trace (jordan x y) + 2 * trace (jordan (jordan x x) y)) • (1 : Albert)

set_option maxHeartbeats 2000000 in
theorem jordan_identity (x y : Albert) :
    jordan (jordan x y) (jordan x x) = jordan x (jordan y (jordan x x)) := by
  have hlin (u v : Albert) : linearResidual u v = 0 := by
    have ht : trace (jordan u (jordan u v)) = trace (jordan (jordan u u) v) := (inner_jordan_associative u u v).symm
    calc linearResidual u v = (1 / 6 : ℝ) •
          (cubicResidual (u + v) - cubicResidual (u - v) - (2 : ℝ) • cubicResidual v) := by
          simp only [linearResidual, cubicResidual, jordan_add_left, jordan_add_right, jordan_sub_left, jordan_sub_right,
            trace_add, trace_sub]
          simp only [jordan_comm v u, jordan_comm v (jordan u u), ht]
          module
      _ = 0 := by rw [cubicResidual_eq_zero, cubicResidual_eq_zero, cubicResidual_eq_zero]; simp
  have hB₁ : trace (jordan x (jordan x y)) = trace (jordan (jordan x x) y) := (inner_jordan_associative x x y).symm
  have hB₂ : trace (jordan (jordan x x) (jordan x y)) = trace (jordan (jordan x (jordan x x)) y) := by
    change inner (jordan x x) (jordan x y) = inner (jordan x (jordan x x)) y
    rw [← inner_jordan_associative, jordan_comm (jordan x x) x]
  have hj : jordan (jordan x x) (jordan x y) - jordan x (jordan (jordan x x) y) = 0 := by
    calc jordan (jordan x x) (jordan x y) - jordan x (jordan (jordan x x) y) =
          (-1 / 2 : ℝ) • (jordan x (linearResidual x y) - linearResidual x (jordan x y)) -
          (trace y / 6) • cubicResidual x + ((1 / 6 : ℝ) * trace (jordan (cubicResidual x) y)) • (1 : Albert) := by
          simp only [linearResidual, cubicResidual, jordan_add_left, jordan_add_right, jordan_sub_left, jordan_sub_right,
            jordan_smul_left, jordan_smul_right, jordan_unit_left, jordan_unit_right, trace_add, trace_sub, trace_smul, hB₁, hB₂]
          module
      _ = 0 := by rw [hlin, hlin, cubicResidual_eq_zero]; simp [trace]
  simpa only [jordan_comm (jordan x y) (jordan x x), jordan_comm y (jordan x x)] using sub_eq_zero.mp hj

end
end Glennie
