module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantScaling
public import HypoellipticAleksandrov.Parabolic.LocalClassical
import HypoellipticAleksandrov.Statements.ParabolicHarnack
import HypoellipticAleksandrov.Parabolic.ContDiffOnTwoToScalarC12

/-!
# The Harnack chain of the common terminal minorant (companion paper, Lemma 3.6)

* `normalized_six_step_harnack`: six translated applications of the unit-cylinder
  Harnack inequality `parabolic_harnack_unit_cylinder` join `(1, 0)` to `(4, v)`, `|v| < 1`,
  inside `(0, ∞) × B₄`, giving `𝔥⁶ u (1, 0) ≤ u (4, v)`.
* `normalized_minorant_comparison`: the Harnack inequality is applied to the time-reversed
  classical scalar solutions supplied by the parabolic marginal bundle; testing against smooth
  compactly supported data gives the measure inequality
  `h • P (T-1, T, 0) ≤ P (T-4, T, v)` for `|v| < 1`, with `h = 𝔥⁶`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open Set
open HypoellipticAleksandrov.Parabolic

open scoped MatrixOrder

/-! ### Calculus for the affine change of scalar variables -/

variable {d : ℕ}

/-- Spatial gradient under an affine change of variables. -/
theorem scalarSpatialGradient_comp_scalarAffine  {V : TimeVelocity d → ℝ}
    {α a : ℝ} {c : PDE.Vec d} {e : ℝ} {z : TimeVelocity d}
    (hV : DifferentiableAt ℝ (fun y  => V (α + a * z.1, y)) (c + e • z.2)) :
    scalarSpatialGradient (fun p => V (scalarAffine α a c e p)) z =
      e • scalarSpatialGradient V (scalarAffine α a c e z) := by
  have hA : HasFDerivAt (fun y  => c + e • y)
      (e • ContinuousLinearMap.id ℝ (PDE.Vec d)) z.2 :=
    ((hasFDerivAt_id (𝕜 := ℝ) z.2).const_smul e).const_add c

  funext i
  change fderiv ℝ ((fun y  => V (α + a * z.1, y)) ∘ fun y => c + e • y) z.2
      (PDE.basisVec i) = e * fderiv ℝ (fun y  => V (α + a * z.1, y))
        (c + e • z.2) (PDE.basisVec i)
  rw [(hV.hasFDerivAt.comp z.2 hA).fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

/-- The anisotropic `C^{1,2}` class is stable under affine changes of variables. -/
theorem isScalarC12On_comp_scalarAffine  {u : TimeVelocity d → ℝ}
    {S S' : HypoellipticAleksandrov.Parabolic.Region d} {α a : ℝ} {c : PDE.Vec d} {e : ℝ}
    (hu : IsScalarC12On u S') (hmaps : MapsTo (scalarAffine α a c e) S S') :
    IsScalarC12On (fun p => u (scalarAffine α a c e p)) S := by

  have hcont  := (contDiff_scalarAffine α a c e).continuous
  have hdiff : ∀ z ∈ S, DifferentiableAt ℝ (fun r  => u (r, c + e • z.2)) (α + a * z.1) :=
    fun z hz => hu.timeSlice_differentiableAt (hmaps hz)
  have hspace : ∀ z ∈ S, ContDiffAt ℝ 2 (fun y  => u (α + a * z.1, y))
      (c + e • z.2) := fun z hz => hu.spatialSlice_contDiffAt (hmaps hz)
  refine ⟨hu.continuousOn.comp hcont.continuousOn hmaps, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz

    exact DifferentiableAt.comp (g := fun r  => u (r, c + e • z.2)) z.1 (hdiff z hz) (by fun_prop)
  · intro z hz

    exact ContDiffAt.comp (g := fun y  => u (α + a * z.1, y)) z.2 (hspace z hz) (by fun_prop)
  · refine ContinuousOn.congr (f := fun z => a * scalarTimeDerivative u (scalarAffine α a c e z))
      (continuousOn_const.mul
        (hu.continuousOn_scalarTimeDerivative.comp hcont.continuousOn hmaps)) ?_
    intro z hz
    exact scalarTimeDerivative_comp_scalarAffine (hdiff z hz)
  · refine ContinuousOn.congr (f := fun z => e • scalarSpatialGradient u (scalarAffine α a c e z))
      (ContinuousOn.const_smul
        (hu.continuousOn_scalarSpatialGradient.comp hcont.continuousOn hmaps) e) ?_
    intro z hz
    exact scalarSpatialGradient_comp_scalarAffine
      ((hspace z hz).differentiableAt (by norm_num))
  · refine ContinuousOn.congr
      (f := fun z => e ^ 2 • scalarSpatialHessian u (scalarAffine α a c e z))
      (ContinuousOn.const_smul
        (hu.continuousOn_scalarSpatialHessian.comp hcont.continuousOn hmaps) (e ^ 2)) ?_
    intro z hz
    exact scalarSpatialHessian_comp_scalarAffine (hspace z hz)

/-! ### The six-step Harnack chain -/

/-- **Six-step Harnack chain** (companion paper, Lemma 3.6, analytic part).  Translated
applications of the unit-cylinder Harnack inequality along the points
`(1 + j/2, (j/6) v)`, `j = 0, ..., 6`, with cylinders in `(0, ∞) × B₄`. -/
theorem normalized_six_step_harnack (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∃ hfrak : ℝ, 0 < hfrak ∧
      ∀ (B : CoefficientField d) (u : TimeVelocity d → ℝ),
        IsContinuousCoefficientOn B (Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4) →
        (∀ p ∈ Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4, (coefficientAt B p).IsSymm) →
        HasLowerEllipticityOn lam B (Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4) →
        HasUpperEllipticityOn Lam B (Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4) →
        IsScalarC12On u (Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4) →
        IsNonnegativeOn u (Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4) →
        (∀ p ∈ Ioi (0 : ℝ) ×ˢ PDE.euclideanBall 0 4,
          scalarTimeDerivative u p =
            matrixContraction (coefficientAt B p) (scalarSpatialHessian u p)) →
        ∀ v ∈ PDE.euclideanBall 0 1, hfrak ^ 6 * u (1, 0) ≤ u (4, v) := by
  let sharedTerm_3f822b4daa := (PDE.euclideanBall (0 : PDE.Vec d) (1 / 2 : ℝ))
  let sharedTerm_7fd013b0f3 := ((by norm_num : (0 : ℝ) < 1))
  let sharedTerm_1e1d46bb66 := (abs_of_pos (by norm_num : (0 : ℝ) < 1 / 12))
  let sharedTerm_60747615e5 := ((by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨hf, hfpos, hfH⟩ := parabolic_harnack_unit_cylinder d hd lam hlam Lam hlamLam
  refine ⟨hf, hfpos, ?_⟩
  intro B u hcont hsymm hlow hup hC12 hnn heq v hv
  have hv' : PDE.vecEuclideanNorm v < 1 := by
    have := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (x₀ := (0 : PDE.Vec d))
      sharedTerm_7fd013b0f3).1 hv
    simpa only [sub_zero] using this
  -- one translated application of the Harnack inequality

  -- the chain
  have chain : ∀ j : ℕ, j ≤ 6 →
      hf ^ j * u (1, 0) ≤ u (1 + (j : ℝ) / 2, ((j : ℝ) / 6) • v) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj

      have hjR : (j : ℝ) ≤ 5 := by exact_mod_cast (by omega : j ≤ 5)





      have hstep := (show ∀ (t0 : ℝ) (c p p' : PDE.Vec d), 0 < t0 → c ∈ PDE.euclideanBall 0 1 →
      p - c ∈ PDE.euclideanBall 0 (1 / 2) → p' - c ∈ PDE.euclideanBall 0 (1 / 2) →
      ∀ t t' : ℝ, t = t0 + 3 / 8 → t' = t0 + 7 / 8 → hf * u (t, p) ≤ u (t', p') by
          intro t0 c p p' ht0 hc hp hp' t t' ht ht'
          have hc' : PDE.vecEuclideanNorm c < 1 := by
            have := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (x₀ := (0 : PDE.Vec d))
              sharedTerm_7fd013b0f3).1 hc
            simpa only [sub_zero] using this
          have hmaps : MapsTo (scalarAffine t0 1 c 1)
              (Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec d) 1)
              (Ioi (0 : ℝ) ×ˢ PDE.euclideanBall (0 : PDE.Vec d) 4) := by
            rintro ⟨s, w⟩ ⟨⟨hs0, hs1⟩, hw⟩
            refine ⟨?_, ?_⟩
            · change 0 < t0 + 1 * s
              linarith
            · have hw' : PDE.vecEuclideanNorm w < 1 := by
                have := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (x₀ := (0 : PDE.Vec d))
                  sharedTerm_7fd013b0f3).1 hw
                simpa only [sub_zero] using this
              rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num : (0 : ℝ) < 4), sub_zero]
              change PDE.vecEuclideanNorm (c + (1 : ℝ) • w) < 4
              rw [one_smul]
              linarith [PDE.vecEuclideanNorm_add_le c w]
          have hu12 := isScalarC12On_comp_scalarAffine hC12 hmaps


          have key := hfH (fun s w => B (t0 + 1 * s) (c + (1 : ℝ) • w))
            (fun z => u (scalarAffine t0 1 c 1 z))
            (hcont.comp (contDiff_scalarAffine t0 1 c 1).continuous.continuousOn hmaps)
            (fun z hz => hsymm _ (hmaps hz))
            (fun z hz => hlow _ (hmaps hz)) (fun z hz => hup _ (hmaps hz)) hu12
            (fun z hz => hnn _ (hmaps hz))
            (by
              intro z hz
              have h1 := hC12.timeSlice_differentiableAt (hmaps hz)
              have h2 := hC12.spatialSlice_contDiffAt (hmaps hz)
              rw [scalarTimeDerivative_comp_scalarAffine h1,
                scalarSpatialHessian_comp_scalarAffine h2,
                show coefficientAt (fun s w => B (t0 + 1 * s) (c + (1 : ℝ) • w)) z =
                  coefficientAt B (scalarAffine t0 1 c 1 z) from rfl,
                one_pow, one_smul, one_mul]
              exact heq _ (hmaps hz))
            _ (show ((3 / 8 : ℝ), p - c) ∈ Ioo (1 / 4 : ℝ) (1 / 2 : ℝ) ×ˢ
              sharedTerm_3f822b4daa from ⟨⟨by norm_num, by norm_num⟩, hp⟩) _ (show ((7 / 8 : ℝ), p' - c) ∈ Ioo (3 / 4 : ℝ) 1 ×ˢ
              sharedTerm_3f822b4daa from ⟨⟨by norm_num, by norm_num⟩, hp'⟩)
          have e0 : scalarAffine t0 1 c 1 ((3 / 8 : ℝ), p - c) = (t, p) := by
            simp only [scalarAffine, one_mul, one_smul, ht, add_sub_cancel]
          have e1 : scalarAffine t0 1 c 1 ((7 / 8 : ℝ), p' - c) = (t', p') := by
            simp only [scalarAffine, one_mul, one_smul, ht', add_sub_cancel]
          simpa only [e0, e1] using key) (5 / 8 + (j : ℝ) / 2) (((2 * j + 1) / 12 : ℝ) • v)
        (((j : ℝ) / 6) • v) ((((j + 1 : ℕ) : ℝ) / 6) • v) (by positivity) (by
            rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt sharedTerm_7fd013b0f3, sub_zero,
              PDE.vecEuclideanNorm_smul, abs_of_nonneg (by positivity)]
            nlinarith) (by
            have : ((j : ℝ) / 6) • v - (((2 * j + 1) / 12 : ℝ)) • v = (-(1 / 12 : ℝ)) • v := by
              module
            rw [this, PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt sharedTerm_60747615e5,
              sub_zero, PDE.vecEuclideanNorm_smul, abs_neg, sharedTerm_1e1d46bb66]
            nlinarith) (by
            have : (((j + 1 : ℕ) : ℝ) / 6) • v - (((2 * j + 1) / 12 : ℝ)) • v =
                ((1 / 12 : ℝ)) • v := by
              push_cast
              module
            rw [this, PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt sharedTerm_60747615e5,
              sub_zero, PDE.vecEuclideanNorm_smul, sharedTerm_1e1d46bb66]
            nlinarith)
        (1 + (j : ℝ) / 2) (1 + ((j + 1 : ℕ) : ℝ) / 2) (by ring) (by push_cast; ring)
      calc hf ^ (j + 1) * u (1, 0) = hf * (hf ^ j * u (1, 0)) := by ring
        _ ≤ hf * u (1 + (j : ℝ) / 2, ((j : ℝ) / 6) • v) :=
          mul_le_mul_of_nonneg_left (ih (by omega)) hfpos.le
        _ ≤ u (1 + ((j + 1 : ℕ) : ℝ) / 2, (((j + 1 : ℕ) : ℝ) / 6) • v) := hstep
  have h6 := chain 6 le_rfl
  norm_num at h6
  convert h6 using 2

/-! ### Time reversal of the supplied scalar solutions -/

/-- The time reversal `(θ, v) ↦ (T - θ, v)`, written as an affine scalar change of variables. -/
abbrev timeReversal {d : ℕ} (T : ℝ) : TimeVelocity d → TimeVelocity d :=
  scalarAffine T (-1) 0 1

variable {d : ℕ}

theorem timeReversal_apply  (T θ : ℝ) (v : PDE.Vec d) :
    timeReversal T (θ, v) = (T - θ, v) := by
  simp [timeReversal, scalarAffine, sub_eq_add_neg]

variable {Ω : PDE.VelocityRegion d}

theorem timeReversal_mapsTo   (T : ℝ) :
    MapsTo (timeReversal T) (Ioi (0 : ℝ) ×ˢ Ω)
      (ParabolicProbe.scalarPastOpenCylinder Ω stationary T) := by
  rintro ⟨θ, v⟩ ⟨hθ, hv⟩
  rw [mem_scalarPastOpenCylinder_stationary, timeReversal_apply]
  exact ⟨by simpa using hθ, hv⟩

section
variable (hΩ : IsOpen Ω) {B : CoefficientField d} {T : ℝ} {F : BoundedBorel (PDE.Vec d)} {V : TimeVelocity d → ℝ} (hV : ParabolicProbe.IsClassicalScalarTerminalSolution Ω stationary (zIndependentCoefficient B) T F V)

include hΩ hV
/-- The time-reversed classical scalar solution is `C^{1,2}` on `(0, ∞) × Ω`. -/
theorem timeReversed_isScalarC12On    :
    IsScalarC12On (fun p => V (timeReversal T p)) (Ioi (0 : ℝ) ×ˢ Ω) :=
  isScalarC12On_comp_scalarAffine
    (isScalarC12On_of_isOpen_contDiffOn_two (isOpen_scalarPastOpenCylinder_stationary hΩ T)
      (hV.2.2.1.of_le (by norm_num))) (timeReversal_mapsTo T)

/-- The time-reversed classical scalar solution solves the forward equation with the
reversed coefficient. -/
theorem timeReversed_equation    :
    ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ω,
      scalarTimeDerivative (fun p => V (timeReversal T p)) p =
        matrixContraction (coefficientAt B (timeReversal T p))
          (scalarSpatialHessian (fun p => V (timeReversal T p)) p) := by
  intro p hp
  have hc12 := isScalarC12On_of_isOpen_contDiffOn_two
    (isOpen_scalarPastOpenCylinder_stationary hΩ T) (hV.2.2.1.of_le (by norm_num))


  have hop := hV.2.2.2.1 _ (timeReversal_mapsTo T hp)
  have hgrad : PDE.vecDot ((0 : ℝ → PDE.Vec d → PDE.Vec d)
      (timeReversal T p).1 (timeReversal T p).2)
      (scalarSpatialGradient V (timeReversal T p)) = 0 := by
    simp [PDE.vecDot]
  rw [scalarParabolicOperator_apply, hgrad, add_zero] at hop
  rw [scalarTimeDerivative_comp_scalarAffine (hc12.timeSlice_differentiableAt (timeReversal_mapsTo T hp)), scalarSpatialHessian_comp_scalarAffine (hc12.spatialSlice_contDiffAt (timeReversal_mapsTo T hp)),
    one_pow, one_smul]
  change -1 * scalarTimeDerivative V (timeReversal T p) = _
  have hop' : scalarTimeDerivative V (timeReversal T p) =
      -matrixContraction (coefficientAt B (timeReversal T p))
        (scalarSpatialHessian V (timeReversal T p)) := by
    have : zIndependentCoefficient B (timeReversal T p).1 (timeReversal T p).2 0 =
        coefficientAt B (timeReversal T p) := rfl
    rw [this] at hop
    linarith
  rw [hop']
  ring
end


/-- Smooth coefficients are jointly continuous. -/
theorem continuous_coefficientAt_of_smooth  {B : CoefficientField d}
    (hB : IsSmoothFullKineticCoefficient (zIndependentCoefficient B)) :
    Continuous (coefficientAt B) := by
  refine continuous_matrix fun i j => ?_
  exact (hB i j).continuous.comp
    (continuous_fst.prodMk (continuous_snd.prodMk (continuous_const (y := (0 : PDE.Vec d)))))

/-! ### The measure comparison -/

end HypoellipticAleksandrov.KineticAleksandrov.Decay
