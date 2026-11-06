module

public import Mathlib
public import PottsDiscontinuity.Bethe.Prop21Defs

/-!
# Uniform bounds for the Bethe derivative kernel

The explicit formula `thetaInv` is analytic on `|ε| < 1`. Compactifying
`Δ ≤ Δ₀ < -1` by `ε = 1/Δ` includes the limiting parameter `ε = 0` and
gives bounds for the kernel and its derivatives which are uniform in `Δ`.
-/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

/-- The first spatial partial derivative of the inverse-parameter phase. -/
noncomputable def thetaFirstInv (ε x y : ℝ) : ℝ :=
  fderiv ℝ (fun z : ℝ × ℝ × ℝ => thetaInv z.1 z.2.1 z.2.2)
    (ε, x, y) (0, 1, 0)

section
variable {ε : ℝ} (hε : |ε| < 1) (x y : ℝ)
include hε
theorem analyticAt_thetaFirstInv  :
    AnalyticAt ℝ (fun z : ℝ × ℝ × ℝ => thetaFirstInv z.1 z.2.1 z.2.2)
      (ε, x, y) := by
  exact ((ContinuousLinearMap.apply ℝ ℝ (0, 1, 0)).analyticAt _).comp
    (analyticAt_thetaInv hε x y).fderiv

theorem hasDerivAt_thetaInv_left  :
    HasDerivAt (fun s => thetaInv ε s y) (thetaFirstInv ε x y) x := by
  exact (analyticAt_thetaInv hε x y).differentiableAt.hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_const x ε).prodMk ((hasDerivAt_id x).prodMk (hasDerivAt_const x y)))
end

section
variable {Δ : ℝ} (hΔ : Δ < -1)
include hΔ
theorem abs_inverse_parameter_lt_one  : |1 / Δ| < 1 := by
  rw [abs_div, abs_one]
  have habs : 1 < |Δ| := by grind
  exact (div_lt_one (by linarith : 0 < |Δ|)).2 habs

theorem d1Theta_eq_thetaFirstInv (x y : ℝ) :
    d1Theta Δ x y = thetaFirstInv (1 / Δ) x y := by
  unfold d1Theta
  rw [(funext fun s => theta_eq_thetaInv hΔ s y)]
  exact (hasDerivAt_thetaInv_left (abs_inverse_parameter_lt_one hΔ) x y).deriv

theorem continuous_d1Theta_right (x : ℝ) :
    Continuous (d1Theta Δ x) := by
  apply continuous_iff_continuousAt.2
  intro y
  have ha : AnalyticAt ℝ (fun t => thetaFirstInv (1 / Δ) x t) y :=
    AnalyticAt.comp (f := fun t : ℝ => ((1 / Δ, x, t) : ℝ × ℝ × ℝ))
     
      (analyticAt_thetaFirstInv (abs_inverse_parameter_lt_one hΔ) x y) (by fun_prop)
  have heq :=
    funext fun t => (d1Theta_eq_thetaFirstInv hΔ x t).symm
  simp_all
  fun_prop
end

theorem inverse_parameter_mem {Δ₀ Δ : ℝ} (hΔ₀ : Δ₀ < -1) (hΔ : Δ ≤ Δ₀) :
    1 / Δ ∈ Icc (1 / Δ₀) 0 := by
  refine ⟨one_div_le_one_div_of_neg_of_le (by linarith : Δ₀ < 0) hΔ, ?_⟩
  exact (one_div_neg.2 (by linarith : Δ < 0)).le

/-- The kernel and its full spatial and parameter derivative are bounded on
the compact inverse-parameter box. The bounds come from the explicit analytic
phase formula, rather than an assumed uniform derivative estimate. -/
theorem exists_uniform_thetaFirstInv_box_bounds {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈
      (Icc (1 / Δ₀) 0 ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)),
      |thetaFirstInv z.1 z.2.1 z.2.2| ≤ C ∧
      ‖fderiv ℝ (fun w : ℝ × ℝ × ℝ => thetaFirstInv w.1 w.2.1 w.2.2) z‖ ≤ C := by
  let K := Icc (1 / Δ₀) 0 ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have heps (z : ℝ × ℝ × ℝ) (hz : z ∈ K) : |z.1| < 1 := by
    have h0 := abs_lt.mp (abs_inverse_parameter_lt_one hΔ₀)
    grind
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (fun z hz => (analyticAt_thetaFirstInv (heps z hz) _ _).continuousAt.continuousWithinAt)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (fun z hz => (analyticAt_thetaFirstInv (heps z hz) _ _).fderiv.continuousAt.continuousWithinAt)
  refine ⟨1 + |A| + |B|, by positivity, fun z hz => ?_⟩
  constructor
  · have ha := hA z hz
    rw [Real.norm_eq_abs] at ha
    grind
  · have hb := hB z hz
    grind

theorem hasDerivAt_d1Theta_right_inv {Δ : ℝ} (hΔ : Δ < -1) (x y : ℝ) :
    HasDerivAt (d1Theta Δ x)
      (fderiv ℝ (fun w : ℝ × ℝ × ℝ => thetaFirstInv w.1 w.2.1 w.2.2)
        (1 / Δ, x, y) (0, 0, 1)) y := by
  have hp :=
    (hasDerivAt_const y (1 / Δ)).prodMk
      ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
  have hf := (analyticAt_thetaFirstInv (abs_inverse_parameter_lt_one hΔ) x y).differentiableAt.hasFDerivAt
  have hc := hf.comp_hasDerivAt y hp
  have heq :=
    funext fun t => (d1Theta_eq_thetaFirstInv hΔ x t).symm
  change HasDerivAt (fun t => thetaFirstInv (1 / Δ) x t) _ y at hc
  simp_all

section
variable {Δ₀ : ℝ} (hΔ₀ : Δ₀ < -1)
include hΔ₀
/-- Uniform kernel, mixed-derivative, and joint Lipschitz bounds on the physical
square, including the full range `Δ ≤ Δ₀`. -/
theorem exists_uniform_d1Theta_box_bounds (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ ≤ Δ₀,
      (∀ x ∈ Icc (-R) R, ∀ y ∈ Icc (-R) R,
        |d1Theta Δ x y| ≤ C ∧ |deriv (d1Theta Δ x) y| ≤ C) ∧
      (∀ x ∈ Icc (-R) R, ∀ y ∈ Icc (-R) R,
        ∀ x' ∈ Icc (-R) R, ∀ y' ∈ Icc (-R) R,
        |d1Theta Δ x y - d1Theta Δ x' y'| ≤
          C * max |x - x'| |y - y'|) := by
  obtain ⟨C, hCpos, hC⟩ := exists_uniform_thetaFirstInv_box_bounds hΔ₀ R
  refine ⟨C, hCpos, fun Δ hΔ => ?_⟩
  have hΔvalid : Δ < -1 := by linarith
  let K := Icc (1 / Δ₀) 0 ×ˢ (Icc (-R) R ×ˢ Icc (-R) R)
  let F := fun w : ℝ × ℝ × ℝ => thetaFirstInv w.1 w.2.1 w.2.2
  have hmem {x y : ℝ} (hx : x ∈ Icc (-R) R)
      (hy : y ∈ Icc (-R) R) : (1 / Δ, x, y) ∈ K :=
    ⟨inverse_parameter_mem hΔ₀ hΔ, hx, hy⟩
  have hdiff (w : ℝ × ℝ × ℝ) (hw : w ∈ K) : DifferentiableAt ℝ F w := by
    have h0 := abs_lt.mp (abs_inverse_parameter_lt_one hΔ₀)
    exact (analyticAt_thetaFirstInv (by grind) _ _).differentiableAt
  constructor
  · intro x hx y hy
    constructor
    · grind [d1Theta_eq_thetaFirstInv]
    · rw [(hasDerivAt_d1Theta_right_inv hΔvalid x y).deriv, ← Real.norm_eq_abs]
      calc
        ‖fderiv ℝ F (1 / Δ, x, y) (0, 0, 1)‖ ≤
            ‖fderiv ℝ F (1 / Δ, x, y)‖ * ‖((0, 0, 1) : ℝ × ℝ × ℝ)‖ :=
          (fderiv ℝ F _).le_opNorm _
        _ = ‖fderiv ℝ F (1 / Δ, x, y)‖ := by simp
        _ ≤ C := (hC _ (hmem hx hy)).2
  · intro x hx y hy x' hx' y' hy'
    have hconv : Convex ℝ K := (convex_Icc _ _).prod ((convex_Icc _ _).prod (convex_Icc _ _))
    have hmv := hconv.norm_image_sub_le_of_norm_fderiv_le hdiff
      (fun w hw => (hC w hw).2) (hmem hx' hy') (hmem hx hy)
    simpa [F, d1Theta_eq_thetaFirstInv hΔvalid, Prod.norm_def, Real.norm_eq_abs] using hmv

theorem exists_uniform_d1Theta_bounds  :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ ≤ Δ₀,
      (∀ x ∈ Icc (-Real.pi) Real.pi, ∀ y ∈ Icc (-Real.pi) Real.pi,
        |d1Theta Δ x y| ≤ C ∧ |deriv (d1Theta Δ x) y| ≤ C) ∧
      (∀ x ∈ Icc (-Real.pi) Real.pi, ∀ y ∈ Icc (-Real.pi) Real.pi,
        ∀ x' ∈ Icc (-Real.pi) Real.pi, ∀ y' ∈ Icc (-Real.pi) Real.pi,
        |d1Theta Δ x y - d1Theta Δ x' y'| ≤
          C * max |x - x'| |y - y'|) :=
  exists_uniform_d1Theta_box_bounds hΔ₀ Real.pi
end

end PottsDiscontinuity.Bethe
