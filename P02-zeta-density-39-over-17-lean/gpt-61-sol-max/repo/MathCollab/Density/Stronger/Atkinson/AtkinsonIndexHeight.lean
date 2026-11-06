module
import Mathlib
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm.
See ../../../../../third_party/twelfth/ATKINSON_PREFIX_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonIndexCurvature
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
Adapted from the inspected adjacent `GafniTao.HeathBrownAtkinsonCurvatureHeight` proof.
This local version uses the current native foundation and the exact
`atkinsonSourcePhase`; it imports no adjacent moment theorem.

# Height variation of Atkinson curvature

The phase-difference estimate compares the curvatures at two separated
heights.  Here the positive curvature magnitude is differentiated in the
height variable.  This is the exact source quantity; later scale bounds are
obtained from this formula.
-/



namespace MathCollab.Density.Stronger.Atkinson

noncomputable section

/-- Positive magnitude of the (negative) real-index curvature. -/
def atkinsonIndexCurvatureMagnitude (T x : ℝ) : ℝ :=
  Real.pi * T /
    (x ^ (2 : ℕ) * atkinsonIndexRealSlope T x)

theorem atkinsonIndexCurvatureMagnitude_eq_neg
    (T x : ℝ) :
    atkinsonIndexCurvatureMagnitude T x =
      -atkinsonIndexRealCurvature T x := by
  unfold atkinsonIndexCurvatureMagnitude
    atkinsonIndexRealCurvature
  ring

section
variable {T x : ℝ} (hT : 0 < T) (hx : 0 < x)
include T x hT hx

/-- Height derivative of the exact real-index slope. -/
theorem hasDerivAt_atkinsonIndexRealSlope_height
     :
    HasDerivAt (fun u => atkinsonIndexRealSlope u x)
      (Real.pi / (x * atkinsonIndexRealSlope T x)) T := by
  have hlin : HasDerivAt
      (fun u : ℝ => 2 * Real.pi * u / x + Real.pi ^ (2 : ℕ))
      (2 * Real.pi / x) T := by
    simpa only [mul_one, id_eq] using!
      (((hasDerivAt_id T).const_mul (2 * Real.pi)).div_const x).add_const
        (Real.pi ^ (2 : ℕ))
  have hpos : 0 < 2 * Real.pi * T / x + Real.pi ^ (2 : ℕ) := by
    positivity
  have hsqrt := hlin.sqrt hpos.ne'
  unfold atkinsonIndexRealSlope
  grind

/-- Exact height derivative of the positive curvature magnitude. -/
theorem hasDerivAt_atkinsonIndexCurvatureMagnitude
     :
    HasDerivAt (fun u => atkinsonIndexCurvatureMagnitude u x)
      (Real.pi / x ^ (2 : ℕ) *
        (Real.pi * T / x + Real.pi ^ (2 : ℕ)) /
        (atkinsonIndexRealSlope T x) ^ (3 : ℕ)) T := by
  have hs := hasDerivAt_atkinsonIndexRealSlope_height hT hx
  have hden : HasDerivAt
      (fun u => x ^ (2 : ℕ) * atkinsonIndexRealSlope u x)
      (x ^ (2 : ℕ) *
        (Real.pi / (x * atkinsonIndexRealSlope T x))) T :=
    hs.const_mul (x ^ (2 : ℕ))
  have hdenpos : 0 <
      x ^ (2 : ℕ) * atkinsonIndexRealSlope T x := by
    exact mul_pos (sq_pos_of_pos hx)
      (atkinsonIndexRealSlope_pos hT hx)
  have hnum : HasDerivAt (fun u : ℝ => Real.pi * u) Real.pi T := by
    simpa only [mul_one] using! (hasDerivAt_id T).const_mul Real.pi
  have hquot := hnum.div hden hdenpos.ne'
  unfold atkinsonIndexCurvatureMagnitude
  convert hquot using 1
  have hspos := atkinsonIndexRealSlope_pos hT hx
  have hsquare :
      (atkinsonIndexRealSlope T x) ^ 2 =
        2 * Real.pi * T / x + Real.pi ^ (2 : ℕ) := by
    unfold atkinsonIndexRealSlope
    rw [Real.sq_sqrt]
    positivity
  have hsquare_mul :
      x * (atkinsonIndexRealSlope T x) ^ 2 =
        2 * Real.pi * T + Real.pi ^ (2 : ℕ) * x := by grind
  field_simp [hx.ne', hspos.ne']
  nlinarith [hsquare_mul]
end


/-- Mean-value representation of the curvature difference in the height
variable. -/
theorem exists_atkinsonIndexCurvatureDifference_eq
    {t u x : ℝ} (hu : 0 < u) (htu : u < t) (hx : 0 < x) :
    ∃ c ∈ Set.Ioo u t,
      -(atkinsonIndexRealCurvature t x -
          atkinsonIndexRealCurvature u x) =
        (Real.pi / x ^ (2 : ℕ) *
          (Real.pi * c / x + Real.pi ^ (2 : ℕ)) /
          (atkinsonIndexRealSlope c x) ^ (3 : ℕ)) * (t - u) := by
  let F := fun v => atkinsonIndexCurvatureMagnitude v x
  let F' := fun v =>
    Real.pi / x ^ (2 : ℕ) *
      (Real.pi * v / x + Real.pi ^ (2 : ℕ)) /
      (atkinsonIndexRealSlope v x) ^ (3 : ℕ)
  have hcont : ContinuousOn F (Set.Icc u t) := by
    intro v hv
    exact (hasDerivAt_atkinsonIndexCurvatureMagnitude
      (hu.trans_le hv.1) hx).continuousAt.continuousWithinAt
  have hderiv : ∀ v ∈ Set.Ioo u t, HasDerivAt F (F' v) v := by
    intro v hv
    exact hasDerivAt_atkinsonIndexCurvatureMagnitude
      (hu.trans hv.1) hx
  obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope F F' htu hcont hderiv
  refine ⟨c, hc, ?_⟩
  dsimp only [F, F'] at heq ⊢
  rw [atkinsonIndexCurvatureMagnitude_eq_neg,
    atkinsonIndexCurvatureMagnitude_eq_neg] at heq
  rw [heq]
  grind




