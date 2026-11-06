/- The actual compact Newton cubic identity and resulting Jordan identity. -/
module
public import Mathlib.Tactic.Simps.Basic
public import Glennie.Native.CoordinateSimp

public import Glennie.Native.AlgebraLaws
public import Glennie.LinearSimp
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Glennie
noncomputable section

@[simps! apply_apply] def jordanLinear : Albert →ₗ[ℝ] Albert →ₗ[ℝ] Albert where
  toFun x :=
    { toFun := jordan x
      map_add' := fun y z => jordan_add_right x y z
      map_smul' := fun r y => jordan_smul_right r x y }
  map_add' x y := LinearMap.ext fun z => jordan_add_left x y z
  map_smul' r x := LinearMap.ext fun y => jordan_smul_left r x y

@[simps!] def traceLinear : Albert →ₗ[ℝ] ℝ where
  toFun := trace
  map_add' := trace_add
  map_smul' := trace_smul




/-- Six times the native Newton characteristic residual. -/
def cubicResidual (x : Albert) : Albert :=
  (6 : ℝ) • jordan x (jordan x x) - (6 * trace x) • jordan x x +
    (3 * (trace x) ^ 2 - 3 * trace (jordan x x)) • x -
    ((trace x) ^ 3 - 3 * trace x * trace (jordan x x) +
      2 * trace (jordan x (jordan x x))) • (1 : Albert)

set_option maxHeartbeats 8000000 in
/-- The Newton residual is proved in all 27 native compact coordinates. -/
theorem cubicResidual_eq_zero (x : Albert) :
    cubicResidual x = 0 := by
  unfold cubicResidual
  ext
  all_goals simp [albert_coords, trace]
  all_goals ring

/- The polarization argument is adapted from AlbertLean/CubicJordan.lean in
albert-lean-public-clean, commit dd06ef5d423a0e4a5d814d2c221e999b98887ee1,
source SHA256 cc885b590ac2317fbde15b490d8205d684fafbf7dbe4ffd883155275a0986826.
The upstream repository is licensed under Apache-2.0; see THIRD-PARTY-NOTICES. -/
set_option maxHeartbeats 2000000 in
/-- The native compact Hermitian product satisfies the Jordan identity. -/
theorem jordan_identity (x y : Albert) :
    jordan (jordan x y) (jordan x x) = jordan x (jordan y (jordan x x)) := by
  have hB₁ (z : Albert) : trace (jordan x (jordan x z)) = trace (jordan (jordan x x) z) :=
    (inner_jordan_associative x x z).symm
  have hB₂ : trace (jordan (jordan x x) (jordan x y)) =
      trace (jordan (jordan x (jordan x x)) y) := by
    change inner (jordan x x) (jordan x y) = inner (jordan x (jordan x x)) y
    rw [← inner_jordan_associative, jordan_comm (jordan x x) x]
  let L (u v : Albert) := (1 / 6 : ℝ) •
    (cubicResidual (u + v) -
      cubicResidual (u - v) -
      (2 : ℝ) • cubicResidual v)
  have hlin (u v : Albert) : L u v = 0 := by simp [L, cubicResidual_eq_zero]
  have h1 := congrArg (fun z => jordan x z) (hlin x y)
  have h2 := hlin x (jordan x y)
  have h3 := cubicResidual_eq_zero x
  have h4 := congrArg (fun z => trace (jordan z y) • (1 : Albert)) h3
  rw [jordan_comm (jordan x y) (jordan x x), jordan_comm y (jordan x x)]
  simp only [albert_linear, L, cubicResidual, trace_zero, jordan_unit_left, jordan_unit_right,
    jordan_comm y x, jordan_comm y (jordan x x), jordan_comm (jordan x y) x,
    jordan_comm (jordan x y) (jordan x x), hB₁, hB₂] at h1 h2 h3 h4
  linear_combination (norm := module) (-1 / 2 : ℝ) • h1 + (1 / 2 : ℝ) • h2 -
    (trace y / 6) • h3 + (1 / 6 : ℝ) • h4

end
end Glennie
