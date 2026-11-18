module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGeometry
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import PDEFoundation.Measure.OneDimensionalCoordinate
import Mathlib.Tactic.FinCases
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdaptersCalculus
import Mathlib.Tactic.FieldSimp
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.CaseW
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FullCoefficientAdapters
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
public import Mathlib.Analysis.Calculus.MeanValue
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EvolutionInstance
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelTheorem
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripSource

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory HypoellipticAleksandrov.Parabolic HypoellipticAleksandrov.KineticAleksandrov.TheoremA Filter HypoellipticAleksandrov.KineticAleksandrov.SectionTwo HypoellipticAleksandrov.KineticAleksandrov.Decay Set HypoellipticAleksandrov SectionTwo TheoremA Evolution Parabolic
open scoped Topology MatrixOrder

/-- Physical scalar coordinates on the existing kinetic point carrier. -/
def scalarCoordinates (p : Point) : Fin 3 → ℝ := ![p.time, p.position 0, p.velocity 0]

/-- Reconstruct a kinetic point from scalar coordinates. -/
def scalarPoint (p : Fin 3 → ℝ) : Point := ⟨p 0, fun _ => p 1, fun _ => p 2⟩

/-- Scalar coordinates retain all information on the one-dimensional kinetic carrier. -/
theorem scalarPoint_coordinates (p : Point) : scalarPoint (scalarCoordinates p) = p := by
  ext i
  · rfl
  · have hi := Fin.eq_zero i
    subst i
    rfl
  · have hi := Fin.eq_zero i
    subst i
    rfl

/-- The coordinate reconstruction is an inverse in the other direction as well. -/
theorem scalarCoordinates_point (p : Fin 3 → ℝ) : scalarCoordinates (scalarPoint p) = p := by
  ext i
  fin_cases i <;> rfl

/-- The actual matrix of the inverse clock's linear part. -/
def Clock.inverseMatrix (c : Clock) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![c.r ^ 2, -(c.r ^ 3 / c.vbar), 0;
    c.vbar * c.r ^ 2, 0, 0;
    0, 0, c.r]

/-- The inverse clock written on native scalar coordinates. -/
def Clock.inverseCoordinates (c : Clock) (e : Point) (q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  scalarCoordinates (c.inverse e (scalarPoint q))

/-- Its linear part plus its physical starting-point translation is exactly the inverse clock. -/
theorem Clock.inverseCoordinates_eq (c : Clock) (e : Point) (q : Fin 3 → ℝ) :
    c.inverseCoordinates e q = c.inverseMatrix.mulVec q + ![e.time, e.position 0, c.vbar] := by
  ext i
  fin_cases i <;>
    simp [Clock.inverseCoordinates, Clock.inverseMatrix, Clock.inverse,
      scalarCoordinates, scalarPoint, dotProduct, Fin.sum_univ_succ] <;> ring




/-- The literal scalar-coordinate measurable equivalence. -/
def scalarMeasurableEquiv : Point ≃ᵐ (Fin 3 → ℝ) where
  toFun := scalarCoordinates
  invFun := scalarPoint
  left_inv := scalarPoint_coordinates
  right_inv := scalarCoordinates_point
  measurable_toFun := by
    apply Measurable.of_eval
    intro i
    fin_cases i
    · exact continuous_time.measurable
    · exact (continuous_apply 0 |>.comp continuous_position).measurable
    · exact (continuous_apply 0 |>.comp continuous_velocity).measurable
  measurable_invFun := by
    change Measurable ((KineticPoint.equivProd 1).symm ∘
      fun p : Fin 3 → ℝ => (p 0, (fun _ => p 1, fun _ => p 2)))
    exact (KineticPoint.measurable_equivProd_symm 1).comp
      ((measurable_pi_apply 0).prodMk
        ((Measurable.of_eval fun _ => measurable_pi_apply 1).prodMk
          (Measurable.of_eval fun _ => measurable_pi_apply 2)))

/-- The scalar coordinates preserve the source product volume without any factor. -/
theorem scalarCoordinates_volumePreserving :
    MeasurePreserving scalarMeasurableEquiv volume volume := by
  have ht := (MeasurePreserving.id (volume : Measure ℝ)).prod (PDE.volumePreserving_vecOneEquivReal.prod PDE.volumePreserving_vecOneEquivReal)
  have hh := (MeasurePreserving.id (volume : Measure ℝ)).prod ((volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).symm)
  have hm := ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm).comp (hh.comp (ht.comp (KineticPoint.measurePreserving_equivProd 1)))
  apply hm.congr scalarMeasurableEquiv.measurable
  apply Filter.Eventually.of_forall
  intro p
  ext i
  fin_cases i <;> rfl

/-- The inverse clock rescales the actual kinetic volume, not a replacement measure. -/
theorem Clock.map_inverse_volume (c : Clock) (e : Point) :
    Measure.map (c.inverse e) volume = ENNReal.ofReal ((c.r ^ 6)⁻¹) •
      (volume : Measure Point)   := by
  have det_inverseMatrix :
      c.inverseMatrix.det = c.r ^ 6 := by
    simp [Clock.inverseMatrix, Matrix.det_fin_three]
    field_simp [c.nonzero]
  have map_inverseCoordinates_volume (e : Point) :
      Measure.map (c.inverseCoordinates e) volume =
      ENNReal.ofReal ((c.r ^ 6)⁻¹) • (volume : Measure (Fin 3 → ℝ)) := by
    have abs_det_inverseMatrix :
        |c.inverseMatrix.det| = c.r ^ 6 := by
      rw [det_inverseMatrix, abs_of_nonneg (pow_nonneg c.positive.le 6)]
    have hdet : c.inverseMatrix.det ≠ 0 := by
      rw [det_inverseMatrix]
      exact pow_ne_zero _ (ne_of_gt c.positive)
    have heq : c.inverseCoordinates e =
        (fun p : Fin 3 → ℝ => p + ![e.time, e.position 0, c.vbar]) ∘
          Matrix.toLin' c.inverseMatrix := by
      funext q
      exact c.inverseCoordinates_eq e q
    rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop),
      Real.map_matrix_volume_pi_eq_smul_volume_pi hdet, Measure.map_smul _ (by fun_prop),
      map_add_right_eq_self]
    rw [abs_inv, abs_det_inverseMatrix]
  have heq : c.inverse e = scalarPoint ∘ c.inverseCoordinates e ∘ scalarCoordinates := by
    funext p
    simp [Clock.inverseCoordinates, scalarPoint_coordinates]
  have hc : Measurable scalarCoordinates := scalarMeasurableEquiv.measurable
  have hp : Measurable scalarPoint := scalarMeasurableEquiv.symm.measurable
  have hi : Measurable (c.inverseCoordinates e) := by
    rw [show c.inverseCoordinates e = fun p =>
      Matrix.toLin' c.inverseMatrix p + ![e.time, e.position 0, c.vbar] from
        funext (c.inverseCoordinates_eq e)]
    fun_prop
  have hm : Measure.map scalarCoordinates volume = volume :=
    scalarCoordinates_volumePreserving.map_eq
  rw [heq, ← Measure.map_map hp (hi.comp hc), ← Measure.map_map hi hc,
    hm, map_inverseCoordinates_volume,
    Measure.map_smul _ hp.aemeasurable]
  exact congrArg (fun m => ENNReal.ofReal ((c.r ^ 6)⁻¹) • m) scalarCoordinates_volumePreserving.symm.map_eq

/-- The forward clock in the same native scalar coordinates as its inverse. -/
def Clock.mapCoordinates (c : Clock) (e : Point) (q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  scalarCoordinates (c.map e (scalarPoint q))

/-- Smoothness of the global forward coordinate map. -/
theorem Clock.mapCoordinates_smooth (c : Clock) (e : Point) :
    ContDiff ℝ (⊤ : ℕ∞) (c.mapCoordinates e) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;>
    dsimp [Clock.mapCoordinates, Clock.map, scalarCoordinates, scalarPoint] <;> fun_prop

/-- In the forward direction the source volume formula has factor `r^6`. -/
theorem Clock.map_volume (c : Clock) (e : Point) :
    Measure.map (c.map e) volume = ENNReal.ofReal (c.r ^ 6) •
      (volume : Measure Point) := by
  have hr := pow_pos c.positive 6
  have hs : ENNReal.ofReal (c.r ^ 6) • Measure.map (c.inverse e) volume =
      (volume : Measure Point) := by
    rw [c.map_inverse_volume, smul_smul, ← ENNReal.ofReal_mul hr.le,
      mul_inv_cancel₀ (ne_of_gt hr), ENNReal.ofReal_one, one_smul]
  have heq : c.map e ∘ c.inverse e = id := funext (c.map_inverse e)
  calc
    Measure.map (c.map e) volume =
        Measure.map (c.map e) (ENNReal.ofReal (c.r ^ 6) •
          Measure.map (c.inverse e) volume) := congrArg (Measure.map (c.map e)) hs.symm
    _ = ENNReal.ofReal (c.r ^ 6) • volume := by
      rw [Measure.map_smul _ (c.continuous_map e).measurable.aemeasurable,
        Measure.map_map (c.continuous_map e).measurable
          (c.continuous_inverse e).measurable, heq, Measure.map_id]


/-- The normalized autonomous diffusion, independent of the old time coordinate `z`. -/
def Clock.diffusion (c : Clock) (a : ℝ → ℝ → ℝ) (e : Point) (s y : ℝ) : ℝ :=
  |c.vbar| * a (e.position 0 + c.vbar * c.r ^ 2 * s) (c.vbar + c.r * y) /
    |c.vbar + c.r * y|

/-- The normalized transport drift from `e:clock-coefficients`. -/
def Clock.drift (c : Clock) (y : ℝ) : ℝ := |c.vbar| * y / |c.vbar + c.r * y|

/-- Uniform denominator bounds in the entire cutoff region. -/
theorem Clock.normalized_abs_bounds (c : Clock) {y : ℝ} (hy : |y| < 1) :
    |c.vbar| / 3 ≤ |c.vbar + c.r * y| ∧
      |c.vbar + c.r * y| ≤ 5 * |c.vbar| / 3 := by
  have hmul : |c.r * y| ≤ c.r := by
    rw [abs_mul, abs_of_pos c.positive]
    exact mul_le_of_le_one_right c.positive.le hy.le
  have hl := abs_sub_abs_le_abs_sub c.vbar (c.vbar + c.r * y)
  have heq : |c.vbar - (c.vbar + c.r * y)| = |c.r * y| := by
    rw [sub_add_eq_sub_sub, sub_self, zero_sub, abs_neg]
  rw [heq] at hl
  constructor <;> linarith only [hmul, (abs_add_le c.vbar (c.r * y)), hl, c.radius]

/-- The denominator cannot vanish on the cutoff region. -/
theorem Clock.normalized_ne_zero (c : Clock) {y : ℝ} (hy : |y| < 1) :
    c.vbar + c.r * y ≠ 0 := by
  apply abs_pos.mp
  linarith only [((c.normalized_abs_bounds hy).1), (abs_pos.mpr c.nonzero)]


/-- The normalized diffusion obeys the source bounds on `|y| < 1`. -/
theorem Clock.diffusion_bounds {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (c : Clock) (A : SmoothAutonomous lam Lam) (e : Point) (s y : ℝ) (hy : |y| < 1) :
    3 * lam / 5 ≤ c.diffusion A.a e s y ∧ c.diffusion A.a e s y ≤ 3 * Lam := by
  have hv := abs_pos.mpr c.nonzero
  have hd := abs_pos.mpr (c.normalized_ne_zero hy)
  have hb := c.normalized_abs_bounds hy
  have ha := A.bounds (e.position 0 + c.vbar * c.r ^ 2 * s) (c.vbar + c.r * y)
  change 3 * lam / 5 ≤ _ / _ ∧ _ / _ ≤ 3 * Lam
  constructor
  · rw [le_div_iff₀ hd]
    have h1 := mul_le_mul_of_nonneg_left hb.2 hlam.le
    have h2 := mul_le_mul_of_nonneg_left ha.1 hv.le
    nlinarith only [h1, h2]
  · rw [div_le_iff₀ hd]
    nlinarith only [(mul_le_mul_of_nonneg_left hb.1 (hlam.trans_le hLam).le), (mul_le_mul_of_nonneg_left ha.2 hv.le)]


/-- The exact derivative formula of the clock drift on the cutoff region. -/
theorem Clock.hasDerivAt_drift (c : Clock) {y : ℝ} (hy : |y| < 1) :
    HasDerivAt c.drift (c.vbar ^ 2 / (c.vbar + c.r * y) ^ 2) y  := by
  have normalized_sign :
      (0 < c.vbar → 0 < c.vbar + c.r * y) ∧
      (c.vbar < 0 → c.vbar + c.r * y < 0) := by
    have hmul : |c.r * y| ≤ c.r := by
      rw [abs_mul, abs_of_pos c.positive]
      exact mul_le_of_le_one_right c.positive.le hy.le
    have hh := abs_le.mp hmul
    constructor
    · intro hv
      have hr := c.radius
      rw [abs_of_pos hv] at hr
      linarith only [hh.1, hr, hv]
    · intro hv
      have hr := c.radius
      rw [abs_of_neg hv] at hr
      linarith only [hh.2, hr, hv]
  have hne := c.normalized_ne_zero hy
  have hs := normalized_sign
  have ha : HasDerivAt (fun t : ℝ => c.vbar + c.r * t) c.r y := by
    simpa using! ((hasDerivAt_id y).const_mul c.r).const_add c.vbar
  have hn : HasDerivAt (fun t : ℝ => |c.vbar| * t) |c.vbar| y := by
    simpa using! (hasDerivAt_id y).const_mul |c.vbar|
  rcases lt_or_gt_of_ne c.nonzero with hv | hv
  · have hden := (hasDerivAt_abs_neg (hs.2 hv)).comp y ha
    have hd := hn.div hden (abs_ne_zero.mpr hne)
    convert! hd using 1
    simp
    rw [abs_of_neg hv, abs_of_neg (hs.2 hv)]
    field_simp
    ring
  · have hden := (hasDerivAt_abs_pos (hs.1 hv)).comp y ha
    convert! (hn.div hden (abs_ne_zero.mpr hne)) using 1
    simp
    rw [abs_of_pos hv, abs_of_pos (hs.1 hv)]
    field_simp
    ring



/-- The scalar-coordinate direction corresponding to a named field. -/
def coordinateDirection (i : Fin 3) : Fin 3 → ℝ := Pi.single i 1

/-- The directional derivative in native scalar coordinates. -/
def directional (f : (Fin 3 → ℝ) → ℝ) (d q : Fin 3 → ℝ) : ℝ :=
  fderiv ℝ f q d


/-- The first chain rule along an affine line, with local differentiability only. -/
theorem deriv_coordinateLine (f : (Fin 3 → ℝ) → ℝ) (q d : Fin 3 → ℝ)
    (t₀ : ℝ) (hf : DifferentiableAt ℝ f q) :
    deriv (fun t => f (q + (t-t₀) • d)) t₀ = directional f d q  := by
  have hasDerivAt_coordinateLine (t₀ t : ℝ) :
      HasDerivAt (fun t : ℝ => q + (t-t₀) • d) d t := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa using!
      (((hasDerivAt_id t).sub_const t₀).mul_const (d i)).const_add (q i)
  have hq : q + (t₀-t₀) • d = q := by simp
  have hf' : HasFDerivAt f (fderiv ℝ f q) (q + (t₀-t₀) • d) := by
    simpa using! hf.hasFDerivAt
  simpa using! (hf'.comp_hasDerivAt t₀ (hasDerivAt_coordinateLine t₀ t₀)).deriv

/-- The second directional chain rule; finite C-two regularity supplies the neighborhood. -/
theorem deriv_deriv_coordinateLine (f : (Fin 3 → ℝ) → ℝ) (q d : Fin 3 → ℝ)
    (t₀ : ℝ) (hf : ContDiffAt ℝ 2 f q) :
    deriv (deriv (fun t => f (q + (t-t₀) • d))) t₀ =
      directional (directional f d) d q := by
  have hc : ContinuousAt (fun t : ℝ => q + (t-t₀) • d) t₀ := by fun_prop
  have hq : q + (t₀-t₀) • d = q := by simp
  change Filter.Tendsto _ (𝓝 t₀) (𝓝 (q + (t₀-t₀) • d)) at hc
  rw [hq] at hc
  have hh :=
    hc.eventually (hf.eventually (by norm_num))
  have he : deriv (fun t => f (q + (t-t₀) • d)) =ᶠ[𝓝 t₀]
      fun t => directional f d (q + (t-t₀) • d) := by
    filter_upwards [hh] with t ht
    have hl := deriv_coordinateLine f (q + (t-t₀) • d) d t
      (ht.differentiableAt (by norm_num))
    have heq : (fun s => f ((q + (t-t₀) • d) + (s-t) • d)) =
        fun s => f (q + (s-t₀) • d) := by
      funext s
      congr 1
      ext i
      simp
      ring
    rw [heq] at hl
    exact hl
  rw [he.deriv_eq]
  have hd : ContDiffAt ℝ 1 (directional f d) q := by
    exact (hf.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  exact deriv_coordinateLine (directional f d) q d t₀
    (hd.differentiableAt (by norm_num))

/-- A named partial derivative is the scalar derivative on its coordinate line. -/
theorem deriv_coordinate_slice (f : (Fin 3 → ℝ) → ℝ) (q : Fin 3 → ℝ)
    (i : Fin 3) (hf : DifferentiableAt ℝ f q) :
    deriv (fun t => f (Function.update q i t)) (q i) =
      directional f (coordinateDirection i) q := by
  have he : (fun t => f (Function.update q i t)) =
      fun t => f (q + (t-q i) • coordinateDirection i) := by
    funext t
    congr 1
    ext j
    by_cases hij : j = i
    · subst j
      simp [coordinateDirection]
    · simp [coordinateDirection, hij]
  rw [he]
  exact deriv_coordinateLine f q (coordinateDirection i) (q i) hf

/-- The second named partial derivative is likewise the scalar second slice derivative. -/
theorem deriv_deriv_coordinate_slice (f : (Fin 3 → ℝ) → ℝ) (q : Fin 3 → ℝ)
    (i : Fin 3) (hf : ContDiffAt ℝ 2 f q) :
    deriv (deriv (fun t => f (Function.update q i t))) (q i) =
      directional (directional f (coordinateDirection i)) (coordinateDirection i) q := by
  have he : (fun t => f (Function.update q i t)) =
      fun t => f (q + (t-q i) • coordinateDirection i) := by
    funext t
    congr 1
    ext j
    by_cases hij : j = i
    · subst j
      simp [coordinateDirection]
    · simp [coordinateDirection, hij]
  rw [he]
  exact deriv_deriv_coordinateLine f q (coordinateDirection i) (q i) hf


/-- Clock direction when physical time alone varies. -/
def Clock.timeDirection (c : Clock) : Fin 3 → ℝ :=
  (-c.vbar / c.r ^ 3) • coordinateDirection 1

/-- Clock direction when physical position alone varies. -/
def Clock.positionDirection (c : Clock) : Fin 3 → ℝ :=
  (1 / (c.vbar * c.r ^ 2)) • coordinateDirection 0 +
    (1 / c.r ^ 3) • coordinateDirection 1

/-- Clock direction when physical velocity alone varies. -/
def Clock.velocityDirection (c : Clock) : Fin 3 → ℝ :=
  (1 / c.r) • coordinateDirection 2




/-- Every scalar coordinate slice reconstructs its literal kinetic slice. -/
theorem scalarPoint_update (p : Point) (i : Fin 3) (t : ℝ) :
    scalarPoint (Function.update (scalarCoordinates p) i t) =
      match i with
      | 0 => ⟨t, p.position, p.velocity⟩
      | 1 => ⟨p.time, fun _ => t, p.velocity⟩
      | 2 => ⟨p.time, p.position, fun _ => t⟩ := by
  fin_cases i <;> ext j
  all_goals try (have hj := Fin.eq_zero j; subst j)
  all_goals simp [scalarPoint, scalarCoordinates, Function.update]




private theorem directional_smul (f : (Fin 3 → ℝ) → ℝ) (d q : Fin 3 → ℝ)
    (k : ℝ) : directional f (k • d) q = k * directional f d q := by
  simp [directional, map_smul]

private theorem second_directional_smul (f : (Fin 3 → ℝ) → ℝ) (d q : Fin 3 → ℝ)
    (k : ℝ) (hf : ContDiffAt ℝ 2 f q) :
    directional (directional f (k • d)) (k • d) q =
      k ^ 2 * directional (directional f d) d q := by
  have hd : DifferentiableAt ℝ (directional f d) q :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  rw [(funext (fun q => directional_smul f d q k)), directional_smul]
  change k * (fderiv ℝ (fun q => k * directional f d q) q) d = _
  rw [fderiv_const_mul hd k]
  simp [smul_apply, directional]
  ring

/-- The normalized forward operator in clock field order `(sigma,z,y)`. -/
def Clock.normalizedOperator (c : Clock) (a : ℝ → ℝ → ℝ) (e : Point)
    (h : Point → ℝ) (q : Point) : ℝ :=
  kineticTimeDerivative h q +
    c.diffusion a e q.time (q.velocity 0) * kineticVelocityHessian h q 0 0 +
      c.drift (q.velocity 0) * kineticPositionGradient h q 0



/-- The local normalized scalar diffusion on the full coefficient carrier. -/
def Clock.normalizedCoefficient (c : Clock) (a : ℝ → ℝ → ℝ) (e : Point) :
    FullKineticCoefficient 1 := fun s y _ _ _ => c.diffusion a e s (y 0)

/-- The local normalized scalar transport on the drift carrier. -/
def Clock.normalizedDrift (c : Clock) : PDE.Vec 1 → PDE.Vec 1 :=
  fun y _ => c.drift (y 0)




/-- A fixed genuine smooth cutoff with the required normalized radii. -/
def clockCutoff : ContDiffBump (0 : ℝ) where
  rIn := 3 / 4
  rOut := 7 / 8
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The cutoff equals one throughout the normalized active interval. -/
theorem clockCutoff_eq_one {y : ℝ} (hy : |y| ≤ 3 / 4) : clockCutoff y = 1 := by
  apply clockCutoff.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, Real.dist_eq, clockCutoff] using hy

/-- Away from the cutoff region it vanishes on a neighborhood, not just at one point. -/
theorem clockCutoff_eventually_zero {y : ℝ} (hy : ¬ |y| < 1) :
    ∀ᶠ t in 𝓝 y, clockCutoff t = 0 := by
  have hh : (7 / 8 : ℝ) < |y| := by linarith only [not_lt.mp hy]
  have hn : ∀ᶠ t in 𝓝 y, (7 / 8 : ℝ) < |t| :=
    (isOpen_lt continuous_const continuous_abs).mem_nhds hh
  filter_upwards [hn] with t ht
  apply clockCutoff.zero_of_le_dist
  simpa [Real.dist_eq, clockCutoff] using ht.le

/-- The exact convex diffusion extension from the source proof. -/
def Clock.extendedDiffusion (c : Clock) (lam : ℝ) (a : ℝ → ℝ → ℝ)
    (e : Point) (s y : ℝ) : ℝ :=
  clockCutoff y * c.diffusion a e s y + (1 - clockCutoff y) * lam

/-- The exact convex derivative to be integrated for the transport extension. -/
def Clock.extendedDriftDerivative (c : Clock) (y : ℝ) : ℝ :=
  clockCutoff y * (c.vbar ^ 2 / (c.vbar + c.r * y) ^ 2) + 1 - clockCutoff y

/-- The exact integral transport extension, normalized to vanish at zero. -/
def Clock.extendedDrift (c : Clock) (y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..y, c.extendedDriftDerivative t


/-- The extended drift derivative is globally smooth. -/
theorem Clock.extendedDriftDerivative_smooth (c : Clock) :
    ContDiff ℝ (⊤ : ℕ∞) c.extendedDriftDerivative := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : |y| < 1
  · have hd : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun t : ℝ => c.vbar ^ 2 / (c.vbar + c.r * t) ^ 2) y :=
      contDiffAt_const.div
        ((contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)).pow 2)
        (pow_ne_zero _ (c.normalized_ne_zero hy))
    exact ((clockCutoff.contDiffAt.mul hd).add contDiffAt_const).sub clockCutoff.contDiffAt
  · apply (contDiffAt_const (c := 1)).congr_of_eventuallyEq
    filter_upwards [clockCutoff_eventually_zero hy] with t ht
    simp [Clock.extendedDriftDerivative, ht]


/-- The global diffusion bounds depend only on the original ellipticity constants. -/
theorem Clock.extendedDiffusion_bounds {lam Lam : ℝ} (hlam : 0 < lam)
    (hLam : lam ≤ Lam) (c : Clock) (A : SmoothAutonomous lam Lam)
    (e : Point) (s y : ℝ) :
    3 * lam / 5 ≤ c.extendedDiffusion lam A.a e s y ∧
      c.extendedDiffusion lam A.a e s y ≤ 3 * Lam := by
  by_cases hy : |y| < 1
  · have hb := c.diffusion_bounds hlam hLam A e s y hy
    have ht0 : 0 ≤ clockCutoff y := clockCutoff.nonneg
    have ht1 : clockCutoff y ≤ 1 := clockCutoff.le_one
    simp only [Clock.extendedDiffusion]
    constructor <;> nlinarith only [(mul_nonneg ht0 (sub_nonneg.mpr hb.1)), (mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (by linarith only [hlam] : 3 * lam / 5 ≤ lam))), (mul_nonneg ht0 (sub_nonneg.mpr hb.2)), (mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (by linarith only [hlam, hLam] : lam ≤ 3 * Lam)))]
  · have ht : clockCutoff y = 0 := by
      apply clockCutoff.zero_of_le_dist
      have hh : (7 / 8 : ℝ) ≤ |y| := by linarith only [not_lt.mp hy]
      simpa [Real.dist_eq, clockCutoff] using hh
    simp [Clock.extendedDiffusion, ht]
    constructor <;> linarith only [hlam, hLam]


/-- The integrated extension has exactly the constructed derivative at every point. -/
theorem Clock.hasDerivAt_extendedDrift (c : Clock) (y : ℝ) :
    HasDerivAt c.extendedDrift (c.extendedDriftDerivative y) y := by
  have hc := c.extendedDriftDerivative_smooth.continuous
  exact intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable _ _) hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- The transport extension is globally C-infinity, not merely continuously differentiable. -/
theorem Clock.extendedDrift_smooth (c : Clock) :
    ContDiff ℝ (⊤ : ℕ∞) c.extendedDrift := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun y => (c.hasDerivAt_extendedDrift y).differentiableAt, ?_⟩
  rw [(funext (fun y => (c.hasDerivAt_extendedDrift y).deriv))]
  exact c.extendedDriftDerivative_smooth




/-- The global normalized diffusion on the coefficient carrier. -/
def Clock.extendedCoefficient (c : Clock) (lam : ℝ) (a : ℝ → ℝ → ℝ) (e : Point) :
    CoefficientField 1 := fun s y _ _ => c.extendedDiffusion lam a e s (y 0)

/-- The global normalized drift on the native vector carrier. -/
def Clock.extendedVectorDrift (c : Clock) : PDE.Vec 1 → PDE.Vec 1 :=
  fun y _ => c.extendedDrift (y 0)



private theorem lifted_fderiv (c : Clock) (y w : PDE.Vec 1) :
    fderiv ℝ c.extendedVectorDrift y w =
      fun _ => deriv c.extendedDrift (y 0) * w 0 := by
  have hd' : HasFDerivAt c.extendedVectorDrift
      (ContinuousLinearMap.pi fun _ : Fin 1 =>
        (ContinuousLinearMap.toSpanSingleton ℝ (c.extendedDriftDerivative (y 0))).comp
          (ContinuousLinearMap.proj 0 : PDE.Vec 1 →L[ℝ] ℝ)) y :=
    hasFDerivAt_pi.mpr (fun _ => ((c.hasDerivAt_extendedDrift (y 0)).hasFDerivAt.comp y (ContinuousLinearMap.proj 0 : PDE.Vec 1 →L[ℝ] ℝ).hasFDerivAt))
  rw [hd'.fderiv, (c.hasDerivAt_extendedDrift (y 0)).deriv]
  ext i
  simp [ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply]
  ring


/-- The global normalized coefficient satisfies the Section Two coefficient conditions. -/
theorem Clock.extendedCoefficient_sectionTwo {lam Lam : ℝ} (hlam : 0 < lam)
    (hLam : lam ≤ Lam) (c : Clock) (A : SmoothAutonomous lam Lam) (e : Point) :
    IsSectionTwoCoefficient (3 * lam / 5) (3 * Lam) (c.extendedCoefficient lam A.a e)  := by
  have extendedDiffusion_smooth :
      ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (c.extendedDiffusion lam A.a e)) := by
    have diffusion_contDiffAt (q : ℝ × ℝ) (hq : c.vbar + c.r * q.2 ≠ 0) :
        ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry (c.diffusion A.a e)) q := by
      have hs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ =>
          (e.position 0 + c.vbar * c.r ^ 2 * q.1, c.vbar + c.r * q.2)) :=
        (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk
          (contDiff_const.add (contDiff_const.mul contDiff_snd))
      exact (contDiffAt_const.mul (A.smooth.comp hs).contDiffAt).div
        ((contDiffAt_const.add (contDiffAt_const.mul contDiffAt_snd)).abs hq)
        (abs_ne_zero.mpr hq)
    apply contDiff_iff_contDiffAt.mpr
    intro q
    by_cases hy : |q.2| < 1
    · exact ((clockCutoff.contDiffAt.comp q contDiffAt_snd).mul
        (diffusion_contDiffAt q (c.normalized_ne_zero hy))).add
        ((contDiffAt_const.sub (clockCutoff.contDiffAt.comp q contDiffAt_snd)).mul
          contDiffAt_const)
    · have hz := clockCutoff_eventually_zero hy
      have hq : ∀ᶠ p : ℝ × ℝ in 𝓝 q, clockCutoff p.2 = 0 :=
        (continuous_snd.continuousAt.tendsto.eventually hz)
      apply (contDiffAt_const (c := lam)).congr_of_eventuallyEq
      filter_upwards [hq] with p hp
      simp [Function.uncurry, Clock.extendedDiffusion, hp]
  let E : SmoothAutonomous (3 * lam / 5) (3 * Lam) :=
    ⟨c.extendedDiffusion lam A.a e, extendedDiffusion_smooth,
      c.extendedDiffusion_bounds hlam hLam A e⟩
  refine ⟨by positivity, by linarith only [hlam, hLam], ?_, ?_, ?_, ?_⟩
  · intro i j
    exact E.smooth.comp (contDiff_fst.prodMk
      ((contDiff_apply ℝ ℝ 0).comp contDiff_snd.fst))
  · intro s y
    rfl
  · intro s y
    exact (autonomousCoefficient_bounds E 0 (fun _ => s) y).1
  · intro s y
    exact (autonomousCoefficient_bounds E 0 (fun _ => s) y).2

/-- The literal global clock extensions have case-I structural constants independent of
centre, scale, starting point, and coefficient derivatives. -/
theorem Clock.extended_sourceSetting {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (c : Clock) (A : SmoothAutonomous lam Lam) (e : Point) :
    SourceSetting (3 * lam / 5) (3 * Lam) (9 / 25) 9
      (PDE.oneDimensionalAxisBox (-3 / 4) (3 / 4))
      (c.extendedCoefficient lam A.a e) c.extendedVectorDrift   := by
  have extendedVectorDrift_transportBounds :
      HasTransportBounds (9 / 25 : ℝ) 9 c.extendedVectorDrift := by
    have extendedDrift_deriv_bounds (y : ℝ) :
        (9 / 25 : ℝ) ≤ deriv c.extendedDrift y ∧ deriv c.extendedDrift y ≤ 9 := by
      have extendedDriftDerivative_bounds :
          (9 / 25 : ℝ) ≤ c.extendedDriftDerivative y ∧ c.extendedDriftDerivative y ≤ 9 := by
        have drift_deriv_bounds {y : ℝ} (hy : |y| < 1) :
            (9 / 25 : ℝ) ≤ deriv c.drift y ∧ deriv c.drift y ≤ 9 := by
          rw [(c.hasDerivAt_drift hy).deriv]
          have hb := c.normalized_abs_bounds hy
          have hp : 0 < (c.vbar + c.r * y) ^ 2 := sq_pos_of_ne_zero (c.normalized_ne_zero hy)
          have h1 : |c.vbar + c.r * y| ^ 2 ≤ (5 * |c.vbar| / 3) ^ 2 :=
            pow_le_pow_left₀ (abs_pos.mpr (c.normalized_ne_zero hy)).le hb.2 2
          have h2 : (|c.vbar| / 3) ^ 2 ≤ |c.vbar + c.r * y| ^ 2 :=
            pow_le_pow_left₀ (by positivity) hb.1 2
          simp [div_pow, mul_pow] at h1 h2
          constructor
          · rw [le_div_iff₀ hp]
            nlinarith only [h1]
          · rw [div_le_iff₀ hp]
            nlinarith only [h2]
        by_cases hy : |y| < 1
        · have hb := drift_deriv_bounds hy
          rw [(c.hasDerivAt_drift hy).deriv] at hb
          have ht0 : 0 ≤ clockCutoff y := clockCutoff.nonneg
          have ht1 : clockCutoff y ≤ 1 := clockCutoff.le_one
          simp only [Clock.extendedDriftDerivative]
          constructor <;> nlinarith only [(mul_nonneg ht0 (sub_nonneg.mpr hb.1)), (mul_nonneg ht0 (sub_nonneg.mpr hb.2)), ht0, ht1]
        · have ht : clockCutoff y = 0 := by
            apply clockCutoff.zero_of_le_dist
            have hh : (7 / 8 : ℝ) ≤ |y| := by linarith only [not_lt.mp hy]
            simpa [Real.dist_eq, clockCutoff] using hh
          simp [Clock.extendedDriftDerivative, ht]
          norm_num
      rw [(c.hasDerivAt_extendedDrift y).deriv]
      exact extendedDriftDerivative_bounds
    have euclideanNorm_one (y : PDE.Vec 1) :
        PDE.vecEuclideanNorm y = |y 0| := by
      simp only [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot, Fin.sum_univ_one,
        ← pow_two, Real.sqrt_sq_eq_abs]
    constructor
    · have hl : LipschitzWith 9 c.extendedDrift :=
        lipschitzWith_of_nnnorm_deriv_le
          (fun y => (c.hasDerivAt_extendedDrift y).differentiableAt) (fun y => by
            change |deriv c.extendedDrift y| ≤ 9
            have hb := extendedDrift_deriv_bounds y
            rw [abs_of_nonneg (by linarith only [hb.1])]
            exact hb.2)
      intro y y'
      rw [euclideanNorm_one, euclideanNorm_one]
      exact hl.norm_sub_le (y 0) (y' 0)
    · intro y w hw
      rw [euclideanNorm_one] at hw
      have hs : w 0 ^ 2 = 1 := by nlinarith only [sq_abs (w 0), hw]
      rw [lifted_fderiv]
      simp only [PDE.vecDot, Fin.sum_univ_one]
      have heq : w 0 * (deriv c.extendedDrift (y 0) * w 0) =
          deriv c.extendedDrift (y 0) := by
        calc
          _ = deriv c.extendedDrift (y 0) * w 0 ^ 2 := by ring
          _ = deriv c.extendedDrift (y 0) := by rw [hs, mul_one]
      rw [heq]
      exact (extendedDrift_deriv_bounds (y 0)).1
  have extendedVectorDrift_smooth :
      IsSmoothDrift c.extendedVectorDrift := by
    apply contDiff_pi.mpr
    intro i
    exact c.extendedDrift_smooth.comp (contDiff_apply ℝ ℝ 0)
  refine ⟨c.extendedCoefficient_sectionTwo hlam hLam A e,
    extendedVectorDrift_smooth, by norm_num, by norm_num,
    extendedVectorDrift_transportBounds, Or.inr ?_⟩
  exact ⟨rfl, -3 / 4, 3 / 4, by norm_num, rfl⟩


/-- The fixed normalized active interval, with the source's exact endpoints. -/
def clockNormalizedInterval : Interval := ⟨-3 / 4, 3 / 4, by norm_num⟩

/-- Realization of the literal globally extended normalized coefficient and drift. -/
def IsClockEvolution {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (E : StripEvolution clockNormalizedInterval) : Prop :=
  RealizesTerminalEvolution (intervalDomain clockNormalizedInterval) (fun _ => 0)
    (intervalDomain_measurable clockNormalizedInterval)
    (zIndependentCoefficient (c.extendedCoefficient lam A.a e)) c.extendedVectorDrift E.1 E.2



/-- Existence and uniqueness precede the canonical normalized family. -/
theorem existsUnique_clockEvolution
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) :
    ∃! E : StripEvolution clockNormalizedInterval, IsClockEvolution A c e E   := by
  have clockEvolution_unique (E : StripEvolution clockNormalizedInterval) (E' : StripEvolution clockNormalizedInterval) (hE : IsClockEvolution A c e E) (hE' : IsClockEvolution A c e E') :
      E = E' := by
    obtain ⟨hS, hK⟩ := terminalEvolution_unique (intervalDomain clockNormalizedInterval)
      (fun _ => 0) (intervalDomain_admissible clockNormalizedInterval)
      (zIndependentCoefficient (c.extendedCoefficient lam A.a e)) c.extendedVectorDrift
      E.1 E'.1 E.2 E'.2 hE hE'
    exact Prod.ext hS hK
  have exists_clockEvolution :
      ∃ E : StripEvolution clockNormalizedInterval, IsClockEvolution A c e E := by
    have hs := c.extended_sourceSetting hlam hLam A e
    obtain ⟨hBs, hBsym, hBell⟩ := sectionTwoCoefficient_fullBounds (3 * lam / 5) (3 * Lam)
      (c.extendedCoefficient lam A.a e) hs.1
    obtain ⟨S, K, hc, -, -, -, -, hi, -, -, -, -, he, hcomp, -, -, -⟩ :=
      exists_terminalEvolution_of_classical hLE hH 1 (by omega) (3 * lam / 5) (3 * Lam)
        (9 / 25) 9 (by positivity) (by linarith) (by norm_num) (by norm_num)
        (intervalDomain clockNormalizedInterval) (fun _ => 0)
        (zIndependentCoefficient (c.extendedCoefficient lam A.a e)) c.extendedVectorDrift
        (intervalDomain_admissible clockNormalizedInterval) (zeroCurve_piecewiseC1 1)
        hBs hBsym hBell hs.2.1 hs.2.2.2.2.1.1 hs.2.2.2.2.1.2
    exact ⟨(S, K), hc, hi, he, hcomp⟩
  obtain ⟨E, hE⟩ := exists_clockEvolution
  exact ⟨E, hE, fun E' hE' => clockEvolution_unique E' E hE' hE⟩

/-- The actual normalized clock evolution, selected only from its proved unique characterization. -/
def clockEvolution
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) :
    StripEvolution clockNormalizedInterval :=
  (existsUnique_clockEvolution hH hLE hlam hLam A c e).exists.choose

/-- The selected clock pair realizes exactly the extended case-I coefficient and drift. -/
theorem clockEvolution_spec
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) :
    IsClockEvolution A c e (clockEvolution hH hLE hlam hLam A c e) :=
  (existsUnique_clockEvolution hH hLE hlam hLam A c e).exists.choose_spec







/-- The clock test is the genuine normalized killed Duhamel potential. -/
def clockSourcePotential
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (T : ℝ)
    (f : exitProbeSubmodule) : Point → ℝ :=
  duhamelPotential (clockEvolution hH hLE hlam hLam A c e).2 T
    (exitProbePhysical f ∘ sectionTwoPoint)

/-- The actual clock test is bounded, smooth on the whole normalized strip, vanishes late,
and solves the literal extended transported equation there. -/
theorem clockSourcePotential_regular
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (R T : ℝ) (hRT : R < T)
    (f : exitProbeSubmodule) (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆
      {p | p.time < T ∧ p.velocity 0 ∈ clockNormalizedInterval.carrier})
    (hz : ∀ p, R ≤ p.time → exitProbePhysical f p = 0) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ p,
      |clockSourcePotential hH hLE hlam hLam A c e T f p| ≤ C) ∧
    ContDiffOn ℝ (⊤ : ℕ∞)
      ((clockSourcePotential hH hLE hlam hLam A c e T f ∘ sectionTwoPoint) ∘ scalarPoint)
      {q : Fin 3 → ℝ | q 2 ∈ normalizedActive} ∧
    (∀ p, R ≤ p.time → clockSourcePotential hH hLE hlam hLam A c e T f p = 0) ∧
    (∀ p, p.position ∈ intervalDomain clockNormalizedInterval →
      transportedForwardOperator (zIndependentCoefficient (c.extendedCoefficient lam A.a e))
        c.extendedVectorDrift (clockSourcePotential hH hLE hlam hLam A c e T f) p =
          -exitProbePhysical f (sectionTwoPoint p))     := by
  have clock_transport_operator_zero_after (B : FullKineticCoefficient 1) (b : PDE.Vec 1 → PDE.Vec 1) (u : Point → ℝ) (hz : ∀ p, R ≤ p.time → u p = 0) (p : Point) (hp : R < p.time) :
      transportedForwardOperator B b u p = 0 := by
    have ht : kineticTimeDerivative u p = 0 := by
      have hn : ∀ᶠ t in 𝓝 p.time, R < t := isOpen_Ioi.mem_nhds hp
      have heq : (fun t => u ⟨t, p.position, p.velocity⟩) =ᶠ[𝓝 p.time]
          (fun _ => 0) := hn.mono (fun t ht => hz _ ht.le)
      change deriv (fun t => u ⟨t, p.position, p.velocity⟩) p.time = 0
      rw [heq.deriv_eq]
      exact deriv_const _ _
    have hgrad : (fun y : PDE.Vec 1 => kineticPositionGradient u ⟨p.time, y, p.velocity⟩) =
        fun _ => 0 := by
      funext y
      ext i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rw [kineticPositionGradient_scalar]
      have heq : (fun v : ℝ => u ⟨p.time, fun _ => v, p.velocity⟩) = fun _ => 0 :=
        funext (fun _ => hz _ hp.le)
      rw [heq]
      exact deriv_const _ _
    have hv : diffusedHessian u p 0 0 = 0 := by
      rw [diffusedHessian, hgrad, fderiv_const_apply]
      rfl
    have hx : kineticVelocityGradient u p 0 = 0 := by
      rw [kineticVelocityGradient_scalar]
      have heq : (fun z : ℝ => u ⟨p.time, p.position, fun _ => z⟩) = fun _ => 0 :=
        funext (fun _ => hz _ hp.le)
      rw [heq]
      exact deriv_const _ _
    simp only [transportedForwardOperator_apply, matrixContraction, Fin.sum_univ_one,
      PDE.vecDot, ht, hv, hx, mul_zero, add_zero]
  have clock_native_smooth_of_zero_after (u : Point → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ evolutionHomeomorph 1)
      (evolutionHomeomorph 1 ⁻¹'
        evolutionPastOpenCylinder (intervalDomain clockNormalizedInterval) (fun _ => 0) T)) (hz : ∀ p, R ≤ p.time → u p = 0) :
      ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ evolutionHomeomorph 1)
      {x : EvolutionVec 1 | (evolutionHomeomorph 1 x).position ∈
        intervalDomain clockNormalizedInterval} := by
    intro x hx
    by_cases ht : (evolutionHomeomorph 1 x).time < T
    · have hmem : evolutionHomeomorph 1 x ∈
          evolutionPastOpenCylinder (intervalDomain clockNormalizedInterval) (fun _ => 0) T := by
        refine ⟨ht, ?_⟩
        rw [mem_movingDomain_iff, sub_zero]
        exact hx
      exact ((hu x hmem).contDiffAt
        (((isOpen_duhamelCylinder (isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible clockNormalizedInterval)) (show Continuous (fun _ : ℝ => 0) from continuous_const) T).preimage (evolutionHomeomorph 1).continuous).mem_nhds hmem)).contDiffWithinAt
    · have hRx : R < (evolutionHomeomorph 1 x).time := hRT.trans_le (not_lt.mp ht)
      have hn : ∀ᶠ y in 𝓝 x, R < (evolutionHomeomorph 1 y).time :=
        (isOpen_lt continuous_const (continuous_time.comp (evolutionHomeomorph
          1).continuous)).mem_nhds
          hRx
      have heq : (u ∘ evolutionHomeomorph 1) =ᶠ[𝓝 x] (fun _ => 0) :=
        hn.mono (fun y hy => hz _ hy.le)
      exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt
  have clock_native_smooth_to_scalar (u : Point → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ evolutionHomeomorph 1)
      {x : EvolutionVec 1 | (evolutionHomeomorph 1 x).position ∈
        intervalDomain clockNormalizedInterval}) :
      ContDiffOn ℝ (⊤ : ℕ∞) ((u ∘ sectionTwoPoint) ∘ scalarPoint)
      {q : Fin 3 → ℝ | q 2 ∈ normalizedActive} := by
    let c : (Fin 3 → ℝ) → EvolutionVec 1 := fun q =>
      (evolutionProdCLE 1).symm (q 0, (fun _ => q 2), (fun _ => q 1))
    have hc : ContDiff ℝ (⊤ : ℕ∞) c := (evolutionProdCLE 1).symm.contDiff.comp
      ((contDiff_apply ℝ ℝ (0 : Fin 3)).prodMk
        ((contDiff_pi.mpr (fun _ => contDiff_apply ℝ ℝ (2 : Fin 3))).prodMk
          (contDiff_pi.mpr (fun _ => contDiff_apply ℝ ℝ (1 : Fin 3)))))
    have he (q : Fin 3 → ℝ) : evolutionHomeomorph 1 (c q) = sectionTwoPoint (scalarPoint q) := by
      apply (KineticPoint.equivProd 1).injective
      change evolutionProdCLE 1 ((evolutionProdCLE 1).symm _) = _
      exact ContinuousLinearEquiv.apply_symm_apply _ _
    have hm : MapsTo c {q : Fin 3 → ℝ | q 2 ∈ normalizedActive}
        {x : EvolutionVec 1 | (evolutionHomeomorph 1 x).position ∈
          intervalDomain clockNormalizedInterval} := by
      intro q hq
      change (evolutionHomeomorph 1 (c q)).position ∈ intervalDomain clockNormalizedInterval
      rw [he q, intervalDomain, PDE.mem_oneDimensionalAxisBox_iff]
      exact hq
    have h := hu.comp hc.contDiffOn hm
    have heq : (u ∘ evolutionHomeomorph 1) ∘ c = (u ∘ sectionTwoPoint) ∘ scalarPoint := by
      funext q
      exact congrArg u (he q)
    rwa [heq] at h
  have clock_duhamel_zero_after {Ω : Set (PDE.Vec 1)} {γ : ℝ → PDE.Vec 1} (K : MovingFiberKernel Ω γ) (g : Point → ℝ) (hg : ∀ p, R ≤ p.time → g p = 0) (p : Point) (hp : R ≤ p.time) :
      duhamelPotential K T g p = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro r hr
    unfold duhamelIntegrand
    split
    · unfold duhamelSourceIntegral
      have hz : (fun w : EvolutionAmbientState 1 => g ⟨r, w.1, w.2⟩) = 0 := by
        funext w
        exact hg ⟨r, w.1, w.2⟩ (hp.trans hr.1.le)
      rw [hz]
      exact integral_zero' _ _
    · rfl
  let E := clockEvolution hH hLE hlam hLam A c e
  have hsetting := c.extended_sourceSetting hlam hLam A e
  obtain ⟨hBs, hBsym, hBell⟩ := sectionTwoCoefficient_fullBounds (3 * lam / 5) (3 * Lam)
    (c.extendedCoefficient lam A.a e) hsetting.1
  have hgc := (exitProbePhysical_continuous_compact f).2.comp_homeomorph
    (sectionTwoHomeomorph 1)
  obtain ⟨⟨-, C, hC, hb⟩, -, hsm, -, hop, -, -, -, -⟩ :=
    kinetic_duhamel hH (by omega)
      (intervalDomain_admissible clockNormalizedInterval) (zeroCurve_piecewiseC1 1)
      (by positivity : 0 < 3 * lam / 5) (by linarith : 3 * lam / 5 ≤ 3 * Lam)
      (by norm_num : (0 : ℝ) < 9 / 25)
      (zIndependentCoefficient (c.extendedCoefficient lam A.a e)) hBs hBsym hBell
      c.extendedVectorDrift hsetting.2.1 hsetting.2.2.2.2.1 E.1 E.2
      (clockEvolution_spec hH hLE hlam hLam A c e) T
      (exitProbePhysical f ∘ sectionTwoPoint) (fun p => hfn _)
      (nested_native_probe_raw_smooth f) hgc
      (nested_native_probe_source_support clockNormalizedInterval T f hs)
  have hzero : ∀ p, R ≤ p.time → duhamelPotential E.2 T
      (exitProbePhysical f ∘ sectionTwoPoint) p = 0 := by
    intro p hp
    exact clock_duhamel_zero_after E.2 (exitProbePhysical f ∘ sectionTwoPoint)
      (fun q hq => hz (sectionTwoPoint q) hq) p hp
  refine ⟨⟨C, hC, hb⟩,
    clock_native_smooth_to_scalar _
      (clock_native_smooth_of_zero_after _ hsm hzero), hzero, ?_⟩
  intro p hp
  by_cases ht : p.time < T
  · exact hop p ⟨ht, mem_movingDomain_iff.mpr (by simpa using hp)⟩
  · have hRp : R < p.time := hRT.trans_le (not_lt.mp ht)
    exact (clock_transport_operator_zero_after _ _ _ hzero p hRp).trans
      (by rw [hz (sectionTwoPoint p) hRp.le]; simp)



/-- The actual normalized compact-source test obeys the exact physical weighted source equation. -/
theorem clockSourcePotential_physical_equation
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (R T : ℝ) (hRT : R < T)
    (f : exitProbeSubmodule) (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆
      {p | p.time < T ∧ p.velocity 0 ∈ clockNormalizedInterval.carrier})
    (hz : ∀ p, R ≤ p.time → exitProbePhysical f p = 0)
    (p : Point) (hp : p.velocity 0 ∈ c.active) :
    forwardScalarOperator A.a
      ((clockSourcePotential hH hLE hlam hLam A c e T f ∘ sectionTwoPoint) ∘ c.map e) p =
        -(|p.velocity 0| / (|c.vbar| * c.r ^ 2)) * exitProbePhysical f (c.map e p)     := by
  have extendedDrift_eq {y : ℝ} (hy : y ∈ normalizedActive) :
      c.extendedDrift y = c.drift y := by
    have hy' : (-3 / 4 : ℝ) < y ∧ y < 3 / 4 := hy
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) y, |t| ≤ 3 / 4 := by
      intro t ht
      rw [Set.mem_uIcc] at ht
      rcases ht with ht | ht
      · rw [abs_of_nonneg ht.1]
        exact ht.2.trans hy'.2.le
      · rw [abs_of_nonpos ht.2]
        linarith only [ht.1, hy'.1]
    have hh : ∀ t ∈ Set.uIcc (0 : ℝ) y,
        HasDerivAt c.drift (c.extendedDriftDerivative t) t := by
      intro t ht
      have hb := hd t ht
      have hs : |t| < 1 := by linarith only [hb]
      simpa [Clock.extendedDriftDerivative, clockCutoff_eq_one hb, add_sub_cancel_right] using! c.hasDerivAt_drift hs
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hh
      (c.extendedDriftDerivative_smooth.continuous.intervalIntegrable 0 y)
    simpa [Clock.extendedDrift, Clock.drift] using heq
  have extendedDiffusion_eq (a : ℝ → ℝ → ℝ) (s : ℝ) (y : ℝ) (hy : y ∈ normalizedActive) :
      c.extendedDiffusion lam a e s y = c.diffusion a e s y := by
    have hy' : (-3 / 4 : ℝ) < y ∧ y < 3 / 4 := hy
    have hb : |y| ≤ 3 / 4 := (abs_lt.mpr
      ⟨by linarith only [hy'.1], hy'.2⟩).le
    simp [Clock.extendedDiffusion, clockCutoff_eq_one hb]
  have conjugacy (a : ℝ → ℝ → ℝ) (h : Point → ℝ) (hh : ContDiffOn ℝ (⊤ : ℕ∞) (h ∘ scalarPoint)
      {q : Fin 3 → ℝ | q 2 ∈ normalizedActive}) :
      forwardScalarOperator a (h ∘ c.map e) p =
      |p.velocity 0| / (|c.vbar| * c.r ^ 2) *
        transportedForwardOperator (c.normalizedCoefficient a e) c.normalizedDrift
          (h ∘ sectionTwoPoint) (sectionTwoPoint (c.map e p)) := by
    have normalizedOperator_eq_transport (q : Point) :
        c.normalizedOperator a e h q =
        transportedForwardOperator (c.normalizedCoefficient a e) c.normalizedDrift
          (h ∘ sectionTwoPoint) (sectionTwoPoint q) := by
      simp only [Clock.normalizedOperator, transportedForwardOperator, Clock.normalizedCoefficient,
        Clock.normalizedDrift, fullKineticCoefficientAt, sectionTwoPoint,
        matrixContraction, PDE.vecDot, Fin.sum_univ_one]
      rfl
    have conjugacy_at (hh : ContDiffAt ℝ 2 (h ∘ scalarPoint) (scalarCoordinates (c.map e p))) :
        forwardScalarOperator a (h ∘ c.map e) p =
        |p.velocity 0| / (|c.vbar| * c.r ^ 2) *
          c.normalizedOperator a e h (c.map e p) := by
      have pullback_derivatives :
          kineticTimeDerivative (h ∘ c.map e) p =
            directional (h ∘ scalarPoint) c.timeDirection (scalarCoordinates (c.map e p)) ∧
          kineticPositionGradient (h ∘ c.map e) p 0 =
            directional (h ∘ scalarPoint) c.positionDirection (scalarCoordinates (c.map e p)) ∧
          kineticVelocityHessian (h ∘ c.map e) p 0 0 =
            directional (directional (h ∘ scalarPoint) c.velocityDirection)
              c.velocityDirection (scalarCoordinates (c.map e p)) := by
        have map_velocity_line (v : ℝ) :
            scalarCoordinates (c.map e ⟨p.time, p.position, fun _ => v⟩) =
            scalarCoordinates (c.map e p) + (v-p.velocity 0) • c.velocityDirection := by
          ext i
          fin_cases i
          all_goals simp [scalarCoordinates, Clock.map, Clock.velocityDirection, coordinateDirection]
          all_goals ring
        have map_position_line (x : ℝ) :
            scalarCoordinates (c.map e ⟨p.time, fun _ => x, p.velocity⟩) =
            scalarCoordinates (c.map e p) + (x-p.position 0) • c.positionDirection := by
          ext i
          fin_cases i
          all_goals simp [scalarCoordinates, Clock.map, Clock.positionDirection, coordinateDirection]
          all_goals ring
        have map_time_line (t : ℝ) :
            scalarCoordinates (c.map e ⟨t, p.position, p.velocity⟩) =
            scalarCoordinates (c.map e p) + (t-p.time) • c.timeDirection := by
          ext i
          fin_cases i
          all_goals simp [scalarCoordinates, Clock.map, Clock.timeDirection, coordinateDirection]
          all_goals ring
        have ht : (fun t => h (c.map e ⟨t, p.position, p.velocity⟩)) =
            fun t => (h ∘ scalarPoint)
              (scalarCoordinates (c.map e p) + (t-p.time) • c.timeDirection) := by
          funext t
          rw [← map_time_line t]
          simp [scalarPoint_coordinates]
        have hx : (fun x => h (c.map e ⟨p.time, fun _ => x, p.velocity⟩)) =
            fun x => (h ∘ scalarPoint)
              (scalarCoordinates (c.map e p) + (x-p.position 0) • c.positionDirection) := by
          funext x
          rw [← map_position_line x]
          simp [scalarPoint_coordinates]
        have hv : (fun v => h (c.map e ⟨p.time, p.position, fun _ => v⟩)) =
            fun v => (h ∘ scalarPoint)
              (scalarCoordinates (c.map e p) + (v-p.velocity 0) • c.velocityDirection) := by
          funext v
          rw [← map_velocity_line v]
          simp [scalarPoint_coordinates]
        rw [kineticPositionGradient_scalar, kineticVelocityHessian_scalar]
        change deriv _ p.time = _ ∧ deriv _ (p.position 0) = _ ∧ deriv (deriv _) (p.velocity 0) = _
        simp
        rw [ht, hx, hv]
        exact ⟨deriv_coordinateLine _ _ _ _ (hh.differentiableAt (by norm_num)),
          deriv_coordinateLine _ _ _ _ (hh.differentiableAt (by norm_num)),
          deriv_deriv_coordinateLine _ _ _ _ hh⟩
      have kinetic_derivatives_directional (p : Point) (hh : ContDiffAt ℝ 2 (h ∘ scalarPoint) (scalarCoordinates p)) :
          kineticTimeDerivative h p =
            directional (h ∘ scalarPoint) (coordinateDirection 0) (scalarCoordinates p) ∧
          kineticPositionGradient h p 0 =
            directional (h ∘ scalarPoint) (coordinateDirection 1) (scalarCoordinates p) ∧
          kineticVelocityHessian h p 0 0 =
            directional (directional (h ∘ scalarPoint) (coordinateDirection 2))
              (coordinateDirection 2) (scalarCoordinates p) := by
        have hf := hh.differentiableAt (by norm_num)
        have h0 := deriv_coordinate_slice (h ∘ scalarPoint) (scalarCoordinates p) 0 hf
        have h1 := deriv_coordinate_slice (h ∘ scalarPoint) (scalarCoordinates p) 1 hf
        have h2 := deriv_deriv_coordinate_slice (h ∘ scalarPoint) (scalarCoordinates p) 2 hh
        simp [scalarPoint_update] at h0 h1 h2
        exact ⟨h0, (kineticPositionGradient_scalar h p).trans h1,
          (kineticVelocityHessian_scalar h p).trans h2⟩
      have ht := pullback_derivatives
      have hn := kinetic_derivatives_directional (c.map e p) hh
      rw [forwardScalarOperator, Clock.normalizedOperator, ht.1, ht.2.1, ht.2.2,
        hn.1, hn.2.1, hn.2.2]
      have hx : directional (h ∘ scalarPoint) c.positionDirection
          (scalarCoordinates (c.map e p)) =
          (1 / (c.vbar * c.r ^ 2)) *
            directional (h ∘ scalarPoint) (coordinateDirection 0)
              (scalarCoordinates (c.map e p)) +
          (1 / c.r ^ 3) * directional (h ∘ scalarPoint) (coordinateDirection 1)
            (scalarCoordinates (c.map e p)) := by
        simp [Clock.positionDirection, directional, map_add, map_smul]
      rw [hx, Clock.timeDirection, directional_smul, Clock.velocityDirection,
        second_directional_smul _ _ _ _ hh]
      have hpos : e.position 0 + c.vbar * c.r ^ 2 * (c.map e p).time = p.position 0 := by
        have he := congrArg (fun q : Point => q.position 0) (c.inverse_map e p)
        exact he
      have hvel : c.vbar + c.r * (c.map e p).velocity 0 = p.velocity 0 := by
        exact congrArg (fun q : Point => q.velocity 0) (c.inverse_map e p)
      simp only [Clock.diffusion, Clock.drift, hpos, hvel]
      have hr := ne_of_gt c.positive
      have hv := c.nonzero
      have hpne : p.velocity 0 ≠ 0 := by
        have hb := (c.active_abs_bounds hp).1
        apply abs_pos.mp
        linarith only [hb, (abs_pos.mpr c.nonzero)]
      have hs := c.active_distance hp
      rcases lt_or_gt_of_ne c.nonzero with hc | hc
      · have hpneg : p.velocity 0 < 0 := by
          rw [abs_of_neg hc] at hs
          have hh' := (abs_lt.mp hs).2
          linarith only [hh', hc]
        rw [abs_of_neg hc, abs_of_neg hpneg]
        simp only [Clock.map]
        field_simp [hr, hv, hpne]
        ring
      · have hppos : 0 < p.velocity 0 := by
          rw [abs_of_pos hc] at hs
          have hh' := (abs_lt.mp hs).1
          linarith only [hh', hc]
        rw [abs_of_pos hc, abs_of_pos hppos]
        simp only [Clock.map]
        field_simp [hr, hv, hpne]
        ring
    have hopen : IsOpen {q : Fin 3 → ℝ | q 2 ∈ normalizedActive} :=
      isOpen_Ioo.preimage (continuous_apply 2)
    have hmem : scalarCoordinates (c.map e p) ∈
        {q : Fin 3 → ℝ | q 2 ∈ normalizedActive} :=
      (c.mem_active_iff (p.velocity 0)).mp hp
    have hlocal : ContDiffAt ℝ 2 (h ∘ scalarPoint) (scalarCoordinates (c.map e p)) :=
      ((hh _ hmem).contDiffAt (hopen.mem_nhds hmem)).of_le (by norm_num)
    rw [← normalizedOperator_eq_transport (c.map e p)]
    exact conjugacy_at hlocal
  have clock_extended_operator_eq (u : Point → ℝ) (p : Point) (hp : p.position 0 ∈ normalizedActive) :
      transportedForwardOperator (c.normalizedCoefficient A.a e) c.normalizedDrift u p =
      transportedForwardOperator (zIndependentCoefficient (c.extendedCoefficient lam A.a e))
        c.extendedVectorDrift u p := by
    have hB : fullKineticCoefficientAt (c.normalizedCoefficient A.a e) p =
        fullKineticCoefficientAt (zIndependentCoefficient (c.extendedCoefficient lam A.a e)) p := by
      ext i j
      exact (extendedDiffusion_eq A.a p.time (p.position 0) hp).symm
    have hb : c.normalizedDrift p.position = c.extendedVectorDrift p.position := by
      ext i
      exact (extendedDrift_eq hp).symm
    rw [transportedForwardOperator_apply, transportedForwardOperator_apply, hB, hb]
  obtain ⟨-, hsm, -, hop⟩ :=
    clockSourcePotential_regular hH hLE hlam hLam A c e R T hRT f hfn hs hz
  rw [conjugacy A.a _ hsm]
  have hi : (sectionTwoPoint (c.map e p)).position 0 ∈ normalizedActive :=
    (c.mem_active_iff (p.velocity 0)).mp hp
  rw [clock_extended_operator_eq _ _ hi]
  have heq : (clockSourcePotential hH hLE hlam hLam A c e T f ∘ sectionTwoPoint) ∘
      sectionTwoPoint = clockSourcePotential hH hLE hlam hLam A c e T f := by
    funext q
    exact congrArg _ (sectionTwoPoint_involutive q)
  rw [heq, hop]
  · rw [sectionTwoPoint_involutive]
    ring
  · rw [intervalDomain, PDE.mem_oneDimensionalAxisBox_iff]
    exact hi


/-- A compact physical probe has a strictly positive cutoff above its entire time support. -/
theorem clock_probe_cutoff (f : exitProbeSubmodule) :
    ∃ R : ℝ, 0 < R ∧
      (∀ p ∈ tsupport (exitProbePhysical f), p.time < R) ∧
      (∀ p, R ≤ p.time → exitProbePhysical f p = 0) := by
  obtain ⟨b, hb⟩ := (((exitProbePhysical_continuous_compact f).2).image continuous_time).bddAbove
  refine ⟨max b 0 + 1, by have := le_max_right b 0; linarith, ?_, ?_⟩
  · intro p hp
    have ht := hb (show p.time ∈ KineticPoint.time '' tsupport (exitProbePhysical f)
      from ⟨p, hp, rfl⟩)
    have := le_max_left b 0
    linarith
  · intro p hp
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have ht := hb (show p.time ∈ KineticPoint.time '' tsupport (exitProbePhysical f)
      from ⟨p, hs, rfl⟩)
    have := le_max_left b 0
    linarith

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

