module

public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.EllipsoidGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.EllipsoidBarrierCalculus
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonSobolev
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic
import Batteries.Tactic.Alias
import HypoellipticAleksandrov.Parabolic.MinimumPrinciple
public import PDEFoundation.Calculus.RegularityOrder




/-! # Smooth zero-boundary ellipsoid barriers absorbing bounded drift -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Lieberman
open HypoellipticAleksandrov Parabolic Set Filter Matrix
open scoped Matrix MatrixOrder Topology BigOperators

variable {d : ℕ} {A Q : PDE.Mat d}




/-- Lower Loewner ellipticity controls contraction with a positive-definite matrix. -/
theorem contraction_lower  (hQ : Q.PosDef)
    {lam : ℝ} (hA : lam • (1 : PDE.Mat d) ≤ A) :
    lam * Q.trace ≤ matrixContraction A Q := by
  have hh := _root_.HypoellipticAleksandrov.Parabolic.trace_mul_nonneg_of_posSemidef (Matrix.le_iff.mp hA) hQ.posSemidef
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub,
    Matrix.trace_smul] at hh
  rw [matrixContraction_eq_trace_mul_of_isSymm _ _ hQ.isHermitian.isSymm]
  exact sub_nonneg.mp hh

private theorem drift_absorption {lam t B k s X Y D : ℝ}
    (hlam : 0 < lam) (ht : 0 < t) (hk : 0 < k)
    (hrel : k * lam ^ 2 * t = lam ^ 2 * t + B ^ 2)
    (hX : lam * t ≤ X) (hY : lam * s ^ 2 ≤ Y) (hD : -B * s ≤ D) :
    k * lam * t ≤ 2 * k * X + 4 * k ^ 2 * Y + 2 * k * D := by
  let sharedTerm_3fb9c2d47d := (2 * k ^ 2 * lam * s ^ 2)
  let sharedTerm_92a123dbd5 := (B ^ 2 / (2 * lam))
  have hyoung : 2 * k * B * s ≤ sharedTerm_3fb9c2d47d + sharedTerm_92a123dbd5 := by


    suffices hh : 2 * k * B * s - sharedTerm_3fb9c2d47d ≤ sharedTerm_92a123dbd5 by
      linarith only [hh]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [(sq_nonneg (2 * k * lam * s - B))]
  have hmargin : sharedTerm_92a123dbd5 ≤ k * lam * t := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * lam)).mpr
    nlinarith only [hrel, sq_nonneg B, hlam, ht]



  have hsquare : 0 ≤ sharedTerm_3fb9c2d47d := by positivity
  linarith only [(mul_le_mul_of_nonneg_left hX (show 0 ≤ 2 * k by positivity)), (mul_le_mul_of_nonneg_left hY (show 0 ≤ 4 * k ^ 2 by positivity)), (mul_le_mul_of_nonneg_left hD (show 0 ≤ 2 * k by positivity)), hyoung, hmargin, hsquare]

variable {d : ℕ}

private theorem stationary_operator_congr  {Ω : PDE.VelocityRegion d}
    (hΩ : IsOpen Ω) (f q : PDE.ScalarField d) (heq : EqOn f q Ω)
    (A : CoefficientField d) (b : PDE.TimeVectorField d)
    (z : TimeVelocity d) (hz : z.2 ∈ Ω) :
    scalarParabolicZeroOrderOperator A b (fun _ _ => 0) (fun p => f p.2) z =
      scalarParabolicZeroOrderOperator A b (fun _ _ => 0) (fun p => q p.2) z := by
  have he (y : PDE.Vec d) (hy : y ∈ Ω) : f =ᶠ[𝓝 y] q := by
    filter_upwards [hΩ.mem_nhds hy] with x hx
    exact heq hx
  have hg : PDE.classicalGradient f =ᶠ[𝓝 z.2] PDE.classicalGradient q := by
    filter_upwards [hΩ.mem_nhds hz] with y hy
    exact congrArg (fun L : PDE.Vec d →L[ℝ] ℝ => fun i => L (PDE.basisVec i))
      (he y hy).fderiv_eq
  have hh : scalarSpatialHessian (fun p => f p.2) z =
      scalarSpatialHessian (fun p => q p.2) z := by
    ext i j
    exact congrArg (fun L : PDE.Vec d →L[ℝ] PDE.Vec d => L (PDE.basisVec i) j)
      hg.fderiv_eq
  have hgrad : scalarSpatialGradient (fun p => f p.2) z =
      scalarSpatialGradient (fun p => q p.2) z := hg.eq_of_nhds
  have htf : scalarTimeDerivative (fun p => f p.2) z = 0 := by
    change deriv (fun _ : ℝ => f z.2) z.1 = 0
    exact deriv_const _ _
  have htq : scalarTimeDerivative (fun p => q p.2) z = 0 := by
    change deriv (fun _ : ℝ => q z.2) z.1 = 0
    exact deriv_const _ _
  simp only [scalarParabolicZeroOrderOperator_apply, htf, htq, hh, hgrad,
    zero_mul, add_zero]

/-- A smooth H10 ellipsoid barrier controls the backward operator with bounded drift. -/
theorem exists_h10_ellipsoid_drift_barrier  (hd : 0 < d)
    {Q : PDE.Mat d} (hQ : Q.PosDef) (a T lam M B : ℝ)
    (hlam : 0 < lam) (hM : 0 ≤ M) (_hB : 0 ≤ B)
    (A : CoefficientField d) (b : PDE.TimeVectorField d)
    (_hA : ∀ t y, (A t y).IsSymm)
    (hlo : ∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q),
      lam • (1 : PDE.Mat d) ≤ A z.1 z.2)
    (hb : ∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q),
      PDE.vecEuclideanNorm (b z.1 z.2) ≤ B) :
    ∃ q : PDE.H10Function (openEllipsoid Q),
      ContDiff ℝ PDE.smoothOrder q.toH1Function.toFun ∧
      (∀ y ∈ closure (openEllipsoid Q), 0 ≤ q.toH1Function.toFun y) ∧
      (∀ y ∈ frontier (openEllipsoid Q), q.toH1Function.toFun y = 0) ∧
      ∀ z ∈ Icc a T ×ˢ openEllipsoid Q,
        scalarParabolicZeroOrderOperator A b (fun _ _ => 0)
          (fun p => q.toH1Function.toFun p.2) z ≤ -M := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have ht : 0 < Q.trace := hQ.trace_pos
  let k : ℝ := 1 + B ^ 2 / (lam ^ 2 * Q.trace)
  let C : ℝ := M / (k * lam * Q.trace)
  let f  := fun y => C *
    (Real.exp k - Real.exp (k * PDE.vecDot y (Q *ᵥ y)))
  have hk : 0 < k := by dsimp [k]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrel : k * lam ^ 2 * Q.trace = lam ^ 2 * Q.trace + B ^ 2 := by
    dsimp [k]
    field_simp
  have hCM : C * (k * lam * Q.trace) = M := by
    exact div_mul_cancel₀ M (by positivity)
  obtain ⟨hbounded, hcl, hfront, _hcone⟩ := openEllipsoid_geometry hQ
  have hf : ContDiff ℝ PDE.smoothOrder f := contDiff_const.mul
    (contDiff_const.sub (contDiff_scaled_quadratic Q k).exp)
  have hfn : ∀ y ∈ closure (openEllipsoid Q), 0 ≤ f y := by
    intro y hy
    have hyq : PDE.vecDot y (Q *ᵥ y) ≤ 1 := by rwa [hcl] at hy
    apply mul_nonneg hC
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith only [hyq, hk]))
  have hfz : ∀ y ∈ frontier (openEllipsoid Q), f y = 0 := by
    intro y hy
    have hyq : PDE.vecDot y (Q *ᵥ y) = 1 := by rwa [hfront] at hy
    simp only [f, hyq, mul_one, sub_self, mul_zero]

  obtain ⟨q, hq, _hcompact, heq⟩ := LocalHolder.exists_h10_smooth_barrier_eqOn
    (isOpen_openEllipsoid Q) hbounded.isCompact_closure f hf
    (fun y hy => hfn y (subset_closure hy)) hfz
  refine ⟨q, hq, ?_, ?_, ?_⟩
  · intro y hy
    rw [heq hy]
    exact hfn y hy
  · intro y hy
    rw [heq (frontier_subset_closure hy)]
    exact hfz y hy
  · intro z hz
    rw [stationary_operator_congr (isOpen_openEllipsoid Q) q.toH1Function.toFun f
      (heq.mono subset_closure) A b z hz.2]
    exact (show ∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q),
      scalarParabolicZeroOrderOperator A b (fun _ _ => 0) (fun p => f p.2) z ≤ -M by
        intro z hz
        let p := Q *ᵥ z.2
        let s := PDE.vecEuclideanNorm p

        have hx := contraction_lower hQ (hlo z hz)
        have hy := vecDot_mulVec_lower_of_loewner (hlo z hz) p
        rw [← PDE.vecEuclideanNorm_sq] at hy



        have hexp : 1 ≤ Real.exp (k * PDE.vecDot z.2 (Q *ᵥ z.2)) :=
          Real.one_le_exp (mul_nonneg hk.le (by
              simpa only [PDE.vecDot, dotProduct, star_trivial] using
                hQ.posSemidef.dotProduct_mulVec_nonneg z.2))
        have hepos := Real.exp_pos (k * PDE.vecDot z.2 (Q *ᵥ z.2))
        have hprod := mul_le_mul_of_nonneg_left (drift_absorption hlam ht hk hrel hx hy (show -B * s ≤ PDE.vecDot (b z.1 z.2) p by

            have hb' := mul_le_mul_of_nonneg_right (hb z hz) (PDE.vecEuclideanNorm_nonneg p)

            linarith only [(PDE.abs_vecDot_le_vecEuclideanNorm_mul (b z.1 z.2) p), hb', (neg_abs_le (PDE.vecDot (b z.1 z.2) p))])) (mul_nonneg hC hepos.le)
        have hex := mul_le_mul_of_nonneg_left hexp (mul_nonneg hC
          (by positivity : 0 ≤ k * lam * Q.trace))
        rw [show C * (k * lam * Q.trace) * 1 = M by rw [mul_one, hCM]] at hex
        change scalarParabolicZeroOrderOperator A b (fun _ _ => 0)
          (fun p => C * (Real.exp k - Real.exp (k * PDE.vecDot p.2 (Q *ᵥ p.2)))) z ≤ -M
        rw [scalarOperator_exp_quadratic Q hQ.isHermitian.isSymm]
        nlinarith only [hprod, hex]) z ⟨hz.1, subset_closure hz.2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Lieberman
