module

public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import PDEFoundation.Ambient.EuclideanNorm
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import HypoellipticAleksandrov.KineticAleksandrov.Holder.GaussianBarrierVelocity
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.EllipsoidDirichlet
import PDEFoundation.Geometry.EuclideanBall.Topology
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Group.Bounded
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonSobolev
import Mathlib.Analysis.Matrix.Order
public import HypoellipticAleksandrov.Parabolic.C2ToScalarC12
public import HypoellipticAleksandrov.Coefficients.Ellipticity
import Mathlib.Tactic.Ring
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonTraces
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementEnergyInterior
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonEnergyPointwise
import Mathlib.MeasureTheory.Group.Measure
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonEnergyConstant
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBarrierWeakIdentity
public import HypoellipticAleksandrov.Parabolic.Dirichlet.VariationalEnergy
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperatorBase
import HypoellipticAleksandrov.Parabolic.Dirichlet.SmoothH10DenseRange
import HypoellipticAleksandrov.Parabolic.Dirichlet.SmoothNeighborhoodSpatialSlices
import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTestFunctionSobolevJet
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeVariationalComparison
import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeVariationalNegation
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ParabolicHormanderRegularity
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeVariationalEnvelope
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletComparison
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBarrierPointwise
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Hormander
public import HypoellipticAleksandrov.Parabolic.KrylovCylinder
public import PDEFoundation.Geometry.EuclideanBall.Basic
import HypoellipticAleksandrov.KineticAleksandrov.HormanderBridge

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic

/-- `Ω` has a uniform exterior cone with strictly positive angular opening. -/
def HasUniformNondegenerateExteriorCone {n : ℕ}
    (Ω : Set (PDE.Vec n)) : Prop :=
  ∃ ρ θ : ℝ, 0 < ρ ∧ 0 < θ ∧ θ < 1 ∧
    ∀ y ∈ frontier Ω, ∃ ν : PDE.Vec n,
      PDE.vecEuclideanNorm ν = 1 ∧
        ∀ z : PDE.Vec n,
          0 < PDE.vecEuclideanNorm z →
          PDE.vecEuclideanNorm z < ρ →
          θ * PDE.vecEuclideanNorm z ≤ PDE.vecDot z ν →
          y + z ∉ Ω





end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.KineticAleksandrov.Lieberman
section
open HypoellipticAleksandrov Parabolic
open scoped Matrix BigOperators

/-- The scaled defining quadratic is smooth at every finite order. -/
theorem contDiff_scaled_quadratic {d : ℕ} (Q : PDE.Mat d) (k : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => k * PDE.vecDot x (Q *ᵥ x)) := by
  unfold PDE.vecDot Matrix.mulVec dotProduct
  fun_prop

/-- The native gradient of the scaled symmetric quadratic. -/
theorem gradient_scaled_quadratic {d : ℕ} (Q : PDE.Mat d) (hQ : Q.IsSymm)
    (k : ℝ) (x : PDE.Vec d) :
    PDE.classicalGradient (fun y => k * PDE.vecDot y (Q *ᵥ y)) x =
      (2 * k) • (Q *ᵥ x) := by
  have h := (HasFDerivAt.fun_sum (u := Finset.univ) (fun (i : Fin d) _ =>
    (hasFDerivAt_apply (𝕜 := ℝ) i x).mul
      (HasFDerivAt.fun_sum (u := Finset.univ) (fun (j : Fin d) _ =>
        (hasFDerivAt_apply (𝕜 := ℝ) j x).const_mul (Q i j))))).const_mul k
  ext i
  unfold PDE.classicalGradient
  change fderiv ℝ (fun y => k * ∑ j, y j * ∑ l, Q j l * y l) x
    (PDE.basisVec i) = _
  change HasFDerivAt (fun y : PDE.Vec d => k * ∑ j, y j * ∑ l, Q j l * y l) _ x at h
  rw [h.fderiv]
  simp
  simp [mul_ite, Finset.sum_ite_eq', Finset.mem_univ, Finset.sum_add_distrib]
  have he : (∑ j, x j * Q j i) = ∑ j, Q i j * x j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← hQ.apply i j]
    ring
  rw [he]
  simp only [Matrix.mulVec, dotProduct]
  ring

/-- The native Hessian of the scaled symmetric quadratic. -/
theorem hessian_scaled_quadratic {d : ℕ} (Q : PDE.Mat d) (hQ : Q.IsSymm)
    (k : ℝ) (x : PDE.Vec d) :
    sliceHessian (fun y => k * PDE.vecDot y (Q *ᵥ y)) x = (2 * k) • Q := by
  unfold sliceHessian
  rw [(funext (gradient_scaled_quadratic Q hQ k))]
  ext i j
  change fderiv ℝ (fun y => fun j => (2 * k) * ∑ l, Q j l * y l) x
    (PDE.basisVec i) j = _
  rw [(hasFDerivAt_pi.mpr (fun j : Fin d => (HasFDerivAt.fun_sum (u := Finset.univ) (fun (l : Fin d) _ => (hasFDerivAt_apply (𝕜 := ℝ) l x).const_mul (Q j l))).const_mul (2 * k))).fderiv]
  simp only [ContinuousLinearMap.pi_apply, smul_apply,
    sum_apply, ContinuousLinearMap.proj_apply,
    PDE.basisVec_apply, smul_eq_mul, Matrix.smul_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hQ.apply i j]

/-- The exponential barrier's exact gradient, including its drift sign. -/
theorem gradient_exp_quadratic {d : ℕ} (Q : PDE.Mat d) (hQ : Q.IsSymm)
    (k C : ℝ) (x : PDE.Vec d) :
    PDE.classicalGradient
      (fun y => C * (Real.exp k - Real.exp (k * PDE.vecDot y (Q *ᵥ y)))) x =
      (-2 * C * k * Real.exp (k * PDE.vecDot x (Q *ᵥ x))) • (Q *ᵥ x) := by
  have hq := (contDiff_scaled_quadratic Q (-k)).differentiable (by norm_num) x
  have he : (fun y => C * (Real.exp k - Real.exp (k * PDE.vecDot y (Q *ᵥ y)))) =
      (fun y => C * Real.exp k + (-C) * Real.exp (-((-k) *
        PDE.vecDot y (Q *ᵥ y)))) := by
    funext y
    simp
    ring
  have heDiff : DifferentiableAt ℝ (fun y : PDE.Vec d =>
      (-C) * Real.exp (-((-k) * PDE.vecDot y (Q *ᵥ y)))) x := by
    exact hq.hasFDerivAt.neg.exp.differentiableAt.const_mul (-C)
  have hExDiff : DifferentiableAt ℝ (fun y : PDE.Vec d =>
      Real.exp (-((-k) * PDE.vecDot y (Q *ᵥ y)))) x :=
    hq.hasFDerivAt.neg.exp.differentiableAt
  rw [he, classicalGradient_add (differentiableAt_const _) heDiff,
    classicalGradient_const_mul (-C) hExDiff, (Holder.classicalGradient_exp_neg hq),
    gradient_scaled_quadratic Q hQ]
  ext i
  simp
  ring

/-- The exponential barrier's exact Hessian. -/
theorem hessian_exp_quadratic {d : ℕ} (Q : PDE.Mat d) (hQ : Q.IsSymm)
    (k C : ℝ) (x : PDE.Vec d) (i j : Fin d) :
    sliceHessian
      (fun y => C * (Real.exp k - Real.exp (k * PDE.vecDot y (Q *ᵥ y)))) x i j =
      -C * Real.exp (k * PDE.vecDot x (Q *ᵥ x)) *
        (2 * k * Q i j + 4 * k ^ 2 * (Q *ᵥ x) i * (Q *ᵥ x) j) := by
  have hq : ContDiff ℝ 2 (fun y => (-k) * PDE.vecDot y (Q *ᵥ y)) :=
    (contDiff_scaled_quadratic Q (-k)).of_le (by norm_cast)
  have he : (fun y => C * (Real.exp k - Real.exp (k * PDE.vecDot y (Q *ᵥ y)))) =
      (fun y => C * Real.exp k + (-C) * Real.exp (-((-k) *
        PDE.vecDot y (Q *ᵥ y)))) := by
    funext y
    simp
    ring
  have hc : sliceHessian (fun _ : PDE.Vec d => C * Real.exp k) x = 0 := by
    have hg : PDE.classicalGradient (fun _ : PDE.Vec d => C * Real.exp k) =
        fun _ => 0 := by
      funext y; ext l
      simp
    unfold sliceHessian
    rw [hg, fderiv_const_apply]
    rfl
  rw [he, sliceHessian_add contDiffAt_const (contDiffAt_const.mul hq.contDiffAt.neg.exp),
    hc, zero_add, sliceHessian_const_mul _ hq.contDiffAt.neg.exp,
    Matrix.smul_apply, Holder.sliceHessian_exp_neg hq,
    gradient_scaled_quadratic Q hQ, hessian_scaled_quadratic Q hQ]
  simp
  ring

/-- Exact backward operator of the exponential ellipsoid barrier. -/
theorem scalarOperator_exp_quadratic {d : ℕ} (Q : PDE.Mat d) (hQ : Q.IsSymm)
    (k C : ℝ) (A : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (z : TimeVelocity d) :
    scalarParabolicZeroOrderOperator A b (fun _ _ => 0)
      (fun p => C * (Real.exp k - Real.exp (k * PDE.vecDot p.2 (Q *ᵥ p.2)))) z =
    -C * Real.exp (k * PDE.vecDot z.2 (Q *ᵥ z.2)) *
      (2 * k * matrixContraction (A z.1 z.2) Q +
       4 * k ^ 2 * PDE.vecDot (Q *ᵥ z.2) (A z.1 z.2 *ᵥ (Q *ᵥ z.2)) +
       2 * k * PDE.vecDot (b z.1 z.2) (Q *ᵥ z.2)) := by
  have ht : scalarTimeDerivative
      (fun p : TimeVelocity d => C *
        (Real.exp k - Real.exp (k * PDE.vecDot p.2 (Q *ᵥ p.2)))) z = 0 := by
    change deriv (fun _ : ℝ => C *
      (Real.exp k - Real.exp (k * PDE.vecDot z.2 (Q *ᵥ z.2)))) z.1 = 0
    exact deriv_const _ _
  rw [scalarParabolicZeroOrderOperator_apply, ht]
  simp only [zero_mul, add_zero, zero_add]
  change matrixContraction (A z.1 z.2)
    (sliceHessian (fun y => C * (Real.exp k - Real.exp (k * PDE.vecDot y (Q *ᵥ y))))
      z.2) + PDE.vecDot (b z.1 z.2)
        (PDE.classicalGradient
          (fun y => C * (Real.exp k - Real.exp (k * PDE.vecDot y (Q *ᵥ y)))) z.2) = _
  rw [gradient_exp_quadratic Q hQ]
  have hh : sliceHessian
      (fun y => C * (Real.exp k - Real.exp (k * PDE.vecDot y (Q *ᵥ y)))) z.2 =
      fun i j => -C * Real.exp (k * PDE.vecDot z.2 (Q *ᵥ z.2)) *
        (2 * k * Q i j + 4 * k ^ 2 * (Q *ᵥ z.2) i * (Q *ᵥ z.2) j) := by
    ext i j
    exact hessian_exp_quadratic Q hQ k C z.2 i j
  rw [hh]
  generalize Q *ᵥ z.2 = p
  generalize Real.exp (k * PDE.vecDot z.2 p) = e
  simp [matrixContraction, PDE.vecDot, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  ring_nf
  simp only [mul_assoc, mul_left_comm, mul_comm]
  ring

end
section
open HypoellipticAleksandrov Parabolic Set
open scoped Matrix Topology BigOperators

private theorem quadratic_continuous {d : ℕ} (Q : PDE.Mat d) :
    Continuous (fun x => PDE.vecDot x (Q *ᵥ x)) := by
  unfold PDE.vecDot Matrix.mulVec dotProduct
  fun_prop


private theorem quadratic_nonneg {d : ℕ} {Q : PDE.Mat d} (hQ : Q.PosDef)
    (x : PDE.Vec d) : 0 ≤ PDE.vecDot x (Q *ᵥ x) := by
  simpa only [PDE.vecDot, dotProduct, star_trivial] using
    hQ.posSemidef.dotProduct_mulVec_nonneg x

/-- Every literal open ellipsoid is open, without a definiteness assumption. -/
theorem isOpen_openEllipsoid {d : ℕ} (Q : PDE.Mat d) : IsOpen (openEllipsoid Q) :=
  isOpen_lt (quadratic_continuous Q) continuous_const



private theorem quadratic_add {d : ℕ} {Q : PDE.Mat d} (hQ : Q.IsSymm)
    (x y : PDE.Vec d) :
    PDE.vecDot (x + y) (Q *ᵥ (x + y)) = PDE.vecDot x (Q *ᵥ x) +
      2 * PDE.vecDot y (Q *ᵥ x) + PDE.vecDot y (Q *ᵥ y) := by
  change (x + y) ⬝ᵥ (Q *ᵥ (x + y)) = x ⬝ᵥ (Q *ᵥ x) +
    2 * (y ⬝ᵥ (Q *ᵥ x)) + y ⬝ᵥ (Q *ᵥ y)
  rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
    hQ.dotProduct_mulVec_comm (x := x) (y := y)]
  ring

/-- Positive-definite ellipsoids have bounded closure and Euclidean exterior cones. -/
theorem openEllipsoid_geometry {d : ℕ} {Q : PDE.Mat d} (hQ : Q.PosDef) :
    Bornology.IsBounded (openEllipsoid Q) ∧
    closure (openEllipsoid Q) = {x | PDE.vecDot x (Q *ᵥ x) ≤ 1} ∧
    frontier (openEllipsoid Q) = {x | PDE.vecDot x (Q *ᵥ x) = 1} ∧
    HasUniformNondegenerateExteriorCone (openEllipsoid Q)    := by
  have quadratic_smul {d : ℕ} (Q : PDE.Mat d) (c : ℝ) (x : PDE.Vec d) :
      PDE.vecDot (c • x) (Q *ᵥ (c • x)) = c ^ 2 * PDE.vecDot x (Q *ᵥ x) := by
    simp [Matrix.mulVec_smul, PDE.vecDot]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have ellipsoid_closure {Q : PDE.Mat d} (_hQ : Q.PosDef) :
      closure (openEllipsoid Q) = {x | PDE.vecDot x (Q *ᵥ x) ≤ 1} := by
    apply subset_antisymm
    · exact closure_lt_subset_le (quadratic_continuous Q) continuous_const
    · intro x hx
      have hc : Continuous (fun c : ℝ => c • x) := continuous_id.smul continuous_const
      have him : (fun c : ℝ => c • x) '' Ioo 0 1 ⊆ openEllipsoid Q := by
        rintro y ⟨c, hc', rfl⟩
        change PDE.vecDot (c • x) (Q *ᵥ (c • x)) < 1
        rw [quadratic_smul]
        have hc2 : c ^ 2 < 1 := by nlinarith only [hc'.1, hc'.2]
        exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_left hx (sq_nonneg c)) (by simpa using hc2)
      have h1 : 1 ∈ closure (Ioo (0 : ℝ) 1) := by
        rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
        exact ⟨by norm_num, le_rfl⟩
      have hh := image_closure_subset_closure_image hc (mem_image_of_mem _ h1)
      simpa using (closure_mono him hh)
  have ellipsoid_bounded :
      Bornology.IsBounded (openEllipsoid Q) := by
    obtain ⟨m, hm, hmin⟩ := (isCompact_sphere 0 1).exists_forall_le'
      (quadratic_continuous Q).continuousOn (a := 0) (by
        intro x hx
        have hxne : x ≠ 0 := by
          intro he
          simp [he] at hx
        simpa only [PDE.vecDot, dotProduct, star_trivial] using
          hQ.dotProduct_mulVec_pos hxne)
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨1 + 1 / m, ?_⟩
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      simp only [norm_zero]
      positivity
    have hn := norm_pos_iff.mpr hx0
    have hs : ‖x‖⁻¹ • x ∈ Metric.sphere 0 1 := by
      simp [norm_smul, hn.ne']
    have hh := hmin _ hs
    rw [quadratic_smul] at hh
    have hmul : m * ‖x‖ ^ 2 ≤ PDE.vecDot x (Q *ᵥ x) := by
      have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖x‖)
      field_simp at hh'
      exact hh'
    have hq : PDE.vecDot x (Q *ᵥ x) < 1 := hx
    nlinarith only [hm, hn, hmul, hq, (mul_one_div_cancel hm.ne'), (one_div_pos.mpr hm), sq_nonneg (‖x‖ - 1)]
  have hcl := ellipsoid_closure hQ
  have hf : frontier (openEllipsoid Q) = {x | PDE.vecDot x (Q *ᵥ x) = 1} := by
    rw [(isOpen_openEllipsoid Q).frontier_eq, hcl]
    ext x
    change (_ ≤ 1 ∧ ¬ _ < 1) ↔ _ = 1
    exact ⟨fun h => le_antisymm h.1 (not_lt.mp h.2), fun h => by simp [h]⟩
  refine ⟨ellipsoid_bounded, hcl, hf, 1, 1 / 2, by norm_num, by norm_num,
    by norm_num, ?_⟩
  intro y hy
  have hyq : PDE.vecDot y (Q *ᵥ y) = 1 := by rwa [hf] at hy
  have hyp : Q *ᵥ y ≠ 0 := by
    intro hp
    simp [(hQ.mulVec_injective (hp.trans (Matrix.mulVec_zero Q).symm)), PDE.vecDot] at hyq
  have hn := PDE.vecEuclideanNorm_pos_iff.mpr hyp
  let ν := (PDE.vecEuclideanNorm (Q *ᵥ y))⁻¹ • (Q *ᵥ y)
  refine ⟨ν, ?_, ?_⟩
  · rw [PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  · intro z hz _hr hangle
    have hdot : PDE.vecDot z ν =
        (PDE.vecEuclideanNorm (Q *ᵥ y))⁻¹ * PDE.vecDot z (Q *ᵥ y) := by
      simp [ν, PDE.vecDot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hdot] at hangle
    have hpos : 0 < PDE.vecDot z (Q *ᵥ y) := by
      exact (mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp (lt_of_lt_of_le (by positivity) hangle)
    change ¬ PDE.vecDot (y + z) (Q *ᵥ (y + z)) < 1
    rw [quadratic_add hQ.isHermitian.isSymm, hyq]
    linarith only [hpos, (quadratic_nonneg hQ z)]

/-- A continuous drift is Euclidean-bounded on every bounded closed spatial cylinder. -/
theorem exists_closedCylinder_drift_bound {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : Bornology.IsBounded Ω) (a T : ℝ) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (hb : Continuous (fun z : TimeVelocity d => b z.1 z.2)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ scalarParabolicClosedCylinder a T Ω,
      PDE.vecEuclideanNorm (b z.1 z.2) ≤ B := by
  have hK : IsCompact (scalarParabolicClosedCylinder a T Ω) :=
    isCompact_Icc.prod hΩ.isCompact_closure
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (PDE.continuous_vecEuclideanNorm.comp hb).continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro z hz
  exact (le_abs_self _).trans ((hB z hz).trans (le_max_left _ _))

end
open HypoellipticAleksandrov Parabolic Set Filter Matrix
open scoped Matrix MatrixOrder Topology BigOperators

private theorem trace_mul_nonneg {d : ℕ} {A Q : PDE.Mat d}
    (hA : A.PosSemidef) (hQ : Q.PosSemidef) : 0 ≤ (A * Q).trace := by
  let S := CFC.sqrt Q
  calc
    0 ≤ (S * A * Sᴴ).trace := (hA.mul_mul_conjTranspose_same S).trace_nonneg
    _ = (S * A * S).trace := by rw [((CFC.sqrt_nonneg Q).posSemidef).isHermitian.eq]
    _ = (A * S * S).trace := (Matrix.trace_mul_cycle A S S).symm
    _ = (A * (S * S)).trace := by rw [Matrix.mul_assoc]
    _ = (A * Q).trace := by
      rw [show S * S = Q from CFC.sqrt_mul_sqrt_self Q hQ.nonneg]

/-- Lower Loewner ellipticity controls contraction with a positive-definite matrix. -/
theorem contraction_lower {d : ℕ} {A Q : PDE.Mat d} (hQ : Q.PosDef)
    {lam : ℝ} (hA : lam • (1 : PDE.Mat d) ≤ A) :
    lam * Q.trace ≤ matrixContraction A Q := by
  have hh := trace_mul_nonneg (Matrix.le_iff.mp hA) hQ.posSemidef
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub,
    Matrix.trace_smul] at hh
  rw [matrixContraction_eq_trace_mul_of_isSymm _ _ hQ.isHermitian.isSymm]
  exact sub_nonneg.mp hh

private theorem drift_absorption {lam t B k s X Y D : ℝ}
    (hlam : 0 < lam) (ht : 0 < t) (hk : 0 < k)
    (hrel : k * lam ^ 2 * t = lam ^ 2 * t + B ^ 2)
    (hX : lam * t ≤ X) (hY : lam * s ^ 2 ≤ Y) (hD : -B * s ≤ D) :
    k * lam * t ≤ 2 * k * X + 4 * k ^ 2 * Y + 2 * k * D := by
  have hyoung : 2 * k * B * s ≤ 2 * k ^ 2 * lam * s ^ 2 + B ^ 2 / (2 * lam) := by
    have hd : 0 < 2 * lam := by positivity
    suffices hh : 2 * k * B * s - 2 * k ^ 2 * lam * s ^ 2 ≤ B ^ 2 / (2 * lam) by
      linarith only [hh]
    apply (le_div_iff₀ hd).mpr
    nlinarith only [(sq_nonneg (2 * k * lam * s - B))]
  have hmargin : B ^ 2 / (2 * lam) ≤ k * lam * t := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * lam)).mpr
    nlinarith only [hrel, sq_nonneg B, hlam, ht]
  have hsquare : 0 ≤ 2 * k ^ 2 * lam * s ^ 2 := by positivity
  linarith only [(mul_le_mul_of_nonneg_left hX (show 0 ≤ 2 * k by positivity)), (mul_le_mul_of_nonneg_left hY (show 0 ≤ 4 * k ^ 2 by positivity)), (mul_le_mul_of_nonneg_left hD (show 0 ≤ 2 * k by positivity)), hyoung, hmargin, hsquare]

private theorem stationary_operator_congr {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (f q : PDE.Vec d → ℝ) (heq : EqOn f q Ω)
    (A : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
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
  simp [scalarParabolicZeroOrderOperator_apply, htf, htq, hh, hgrad]

/-- A smooth H10 ellipsoid barrier controls the backward operator with bounded drift. -/
theorem exists_h10_ellipsoid_drift_barrier {d : ℕ} (hd : 0 < d)
    {Q : PDE.Mat d} (hQ : Q.PosDef) (a T lam M B : ℝ)
    (hlam : 0 < lam) (hM : 0 ≤ M) (_hB : 0 ≤ B)
    (A : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (_hA : ∀ t y, (A t y).IsSymm)
    (hlo : ∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q),
      lam • (1 : PDE.Mat d) ≤ A z.1 z.2)
    (hb : ∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q),
      PDE.vecEuclideanNorm (b z.1 z.2) ≤ B) :
    ∃ q : PDE.H10Function (openEllipsoid Q),
      ContDiff ℝ (⊤ : ℕ∞) q.toH1Function.toFun ∧
      (∀ y ∈ closure (openEllipsoid Q), 0 ≤ q.toH1Function.toFun y) ∧
      (∀ y ∈ frontier (openEllipsoid Q), q.toH1Function.toFun y = 0) ∧
      ∀ z ∈ Icc a T ×ˢ openEllipsoid Q,
        scalarParabolicZeroOrderOperator A b (fun _ _ => 0)
          (fun p => q.toH1Function.toFun p.2) z ≤ -M := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have ht := hQ.trace_pos
  let k : ℝ := 1 + B ^ 2 / (lam ^ 2 * Q.trace)
  let C : ℝ := M / (k * lam * Q.trace)
  let f : PDE.Vec d → ℝ := fun y => C *
    (Real.exp k - Real.exp (k * PDE.vecDot y (Q *ᵥ y)))
  have hk : 0 < k := by dsimp [k]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrel : k * lam ^ 2 * Q.trace = lam ^ 2 * Q.trace + B ^ 2 := by
    dsimp [k]
    field_simp
  have hCM : C * (k * lam * Q.trace) = M := by
    exact div_mul_cancel₀ M (by positivity)
  obtain ⟨hbounded, hcl, hfront, _hcone⟩ := openEllipsoid_geometry hQ
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_const.mul
    (contDiff_const.sub (contDiff_scaled_quadratic Q k).exp)
  have hfn : ∀ y ∈ closure (openEllipsoid Q), 0 ≤ f y := by
    intro y hy
    have hyq : PDE.vecDot y (Q *ᵥ y) ≤ 1 := by rwa [hcl] at hy
    apply mul_nonneg hC
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith only [hyq, hk]))
  have hfz : ∀ y ∈ frontier (openEllipsoid Q), f y = 0 := by
    intro y hy
    have hyq : PDE.vecDot y (Q *ᵥ y) = 1 := by rwa [hfront] at hy
    simp [f, hyq]
  have hbound : ∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q),
      scalarParabolicZeroOrderOperator A b (fun _ _ => 0) (fun p => f p.2) z ≤ -M := by
    intro z hz
    let p := Q *ᵥ z.2
    let s := PDE.vecEuclideanNorm p
    have hs : 0 ≤ s := PDE.vecEuclideanNorm_nonneg p
    have hy := vecDot_mulVec_lower_of_loewner (hlo z hz) p
    rw [← PDE.vecEuclideanNorm_sq] at hy
    have hd' : -B * s ≤ PDE.vecDot (b z.1 z.2) p := by
      have hb' := mul_le_mul_of_nonneg_right (hb z hz) hs
      have hh' := neg_abs_le (PDE.vecDot (b z.1 z.2) p)
      linarith only [(PDE.abs_vecDot_le_vecEuclideanNorm_mul (b z.1 z.2) p), hb', hh']
    have hbr := drift_absorption hlam ht hk hrel (contraction_lower hQ (hlo z hz)) hy hd'
    have hq0 : 0 ≤ PDE.vecDot z.2 (Q *ᵥ z.2) := by
      simpa only [PDE.vecDot, dotProduct, star_trivial] using
        hQ.posSemidef.dotProduct_mulVec_nonneg z.2
    have hexp : 1 ≤ Real.exp (k * PDE.vecDot z.2 (Q *ᵥ z.2)) :=
      Real.one_le_exp (mul_nonneg hk.le hq0)
    have hepos := Real.exp_pos (k * PDE.vecDot z.2 (Q *ᵥ z.2))
    have hprod := mul_le_mul_of_nonneg_left hbr (mul_nonneg hC hepos.le)
    have hex := mul_le_mul_of_nonneg_left hexp (mul_nonneg hC
      (by positivity : 0 ≤ k * lam * Q.trace))
    rw [show C * (k * lam * Q.trace) * 1 = M by rw [mul_one, hCM]] at hex
    change scalarParabolicZeroOrderOperator A b (fun _ _ => 0)
      (fun p => C * (Real.exp k - Real.exp (k * PDE.vecDot p.2 (Q *ᵥ p.2)))) z ≤ -M
    rw [scalarOperator_exp_quadratic Q hQ.isHermitian.isSymm]
    nlinarith only [hprod, hex]
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
    exact hbound z ⟨hz.1, subset_closure hz.2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Lieberman

section



namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open TimeVelocityMultiIndex
open scoped Matrix.Norms.Elementwise

/-- Every finite coordinate derivative of an infinitely differentiable function is smooth. -/
theorem contDiff_coordinateIteratedFDeriv_infty {d : ℕ}
    (alpha : TimeVelocityMultiIndex d) (w : TimeVelocity d → ℝ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateIteratedFDeriv alpha w) := by
  unfold coordinateIteratedFDeriv
  have hi := hw.iteratedFDeriv_right
    (m := (⊤ : ℕ∞)) (i := alpha.coordinateList.length) (by simp)
  exact (contDiff_const (c := ContinuousMultilinearMap.apply ℝ _ _
    (fun i => timeVelocityBasis (alpha.coordinateList.get i)))).clm_apply hi


/-- Every Hessian entry of a smooth ambient extension is smooth. -/
theorem contDiff_scalarSpatialHessian_entry_infty {d : ℕ} (w : TimeVelocity d → ℝ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (i j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => scalarSpatialHessian w z i j) := by
  have h := contDiff_coordinateIteratedFDeriv_infty
    (Pi.single (velocityCoord j) 1 + Pi.single (velocityCoord i) 1) w hw
  have heq : (fun z => scalarSpatialHessian w z i j) =
      coordinateIteratedFDeriv
        (Pi.single (velocityCoord j) 1 + Pi.single (velocityCoord i) 1) w :=
    funext (fun z => scalarSpatialHessian_apply_eq_coordinateIteratedFDeriv_of_contDiff_two
      (hw.of_le (by simp)) z i j)
  rw [heq]
  exact h

/-- The signed backward residual of a smooth ambient extension is an actual smooth source. -/
theorem contDiff_smooth_backward_residual {d : ℕ} (A : CoefficientField d)
    (hA : IsSmoothCoefficient A) (w : TimeVelocity d → ℝ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => scalarTimeDerivative w z +
      matrixContraction (coefficientAt A z) (scalarSpatialHessian w z))  := by
  have contDiff_scalarTimeDerivative_infty :
      ContDiff ℝ (⊤ : ℕ∞) (scalarTimeDerivative w) := by
    have h := contDiff_coordinateIteratedFDeriv_infty (Pi.single (timeCoord d) 1) w hw
    have heq : scalarTimeDerivative w =
        coordinateIteratedFDeriv (Pi.single (timeCoord d) 1) w :=
      funext (scalarTimeDerivative_eq_coordinateIteratedFDeriv_of_contDiff_two
        (hw.of_le (by simp)))
    rw [heq]
    exact h
  apply (contDiff_scalarTimeDerivative_infty).add
  unfold matrixContraction
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact ((contDiff_apply ℝ ℝ j).comp
    ((contDiff_apply ℝ (Fin d → ℝ) i).comp hA)).mul
      (contDiff_scalarSpatialHessian_entry_infty w hw i j)

end HypoellipticAleksandrov.Parabolic.LocalHolder

namespace HypoellipticAleksandrov.KineticAleksandrov.Lieberman
open HypoellipticAleksandrov.Parabolic HypoellipticAleksandrov.Parabolic.LocalHolder Set Filter
open scoped Topology Matrix

private theorem scalarTimeDerivative_add {n : ℕ} {u v : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D)
    {z : TimeVelocity n} (hz : z ∈ D) :
    scalarTimeDerivative (fun q => u q + v q) z =
      scalarTimeDerivative u z + scalarTimeDerivative v z := by
  exact ((hu.timeSlice_hasDerivAt hz).add (hv.timeSlice_hasDerivAt hz)).deriv

private theorem scalarSpatialGradient_add {n : ℕ} {u v : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D)
    {z : TimeVelocity n} (hz : z ∈ D) :
    scalarSpatialGradient (fun q => u q + v q) z =
      scalarSpatialGradient u z + scalarSpatialGradient v z := by
  ext i
  change fderiv ℝ (fun y : PDE.Vec n => u (z.1, y) + v (z.1, y)) z.2
      (PDE.basisVec i) = _
  rw [fderiv_fun_add ((hu.spatialSlice_contDiffAt hz).differentiableAt (by norm_num))
    ((hv.spatialSlice_contDiffAt hz).differentiableAt (by norm_num))]
  rfl

private theorem scalarSpatialHessian_apply_eq_sndFDeriv {n : ℕ}
    {u : TimeVelocity n → ℝ} {z : TimeVelocity n}
    (hu : ContDiffAt ℝ 2 (fun y : PDE.Vec n => u (z.1, y)) z.2)
    (i j : Fin n) :
    scalarSpatialHessian u z i j =
      fderiv ℝ (fderiv ℝ (fun y : PDE.Vec n => u (z.1, y))) z.2
        (PDE.basisVec i) (PDE.basisVec j) := by
  let g : PDE.Vec n → ℝ := fun y => u (z.1, y)
  have hsecond : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) z.2) z.2 :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hdiff : ∀ j : Fin n,
      DifferentiableAt ℝ (fun y : PDE.Vec n => fderiv ℝ g y (PDE.basisVec j)) z.2 := by
    intro j
    exact (hsecond.clm_apply (hasFDerivAt_const (PDE.basisVec j) z.2)).differentiableAt
  change (fderiv ℝ (fun y : PDE.Vec n => fun j =>
      fderiv ℝ g y (PDE.basisVec j)) z.2 (PDE.basisVec i)) j = _
  rw [fderiv_pi hdiff]
  have hj := (hsecond.clm_apply (hasFDerivAt_const (PDE.basisVec j) z.2)).fderiv
  have hjApply := congrArg (fun L : PDE.Vec n →L[ℝ] ℝ => L (PDE.basisVec i)) hj
  simpa [ContinuousLinearMap.flip_apply] using hjApply

private theorem scalarSpatialHessian_add {n : ℕ} {u v : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D)
    {z : TimeVelocity n} (hz : z ∈ D) :
    scalarSpatialHessian (fun q => u q + v q) z =
      scalarSpatialHessian u z + scalarSpatialHessian v z := by
  let g_u : PDE.Vec n → ℝ := fun y => u (z.1, y)
  let g_v : PDE.Vec n → ℝ := fun y => v (z.1, y)
  have hfirst : fderiv ℝ (fun y => g_u y + g_v y) =ᶠ[𝓝 z.2]
      fun y => fderiv ℝ g_u y + fderiv ℝ g_v y := by
    filter_upwards [(hu.spatialSlice_contDiffAt hz).eventually (by norm_num),
      (hv.spatialSlice_contDiffAt hz).eventually (by norm_num)] with y huy hvy
    exact fderiv_fun_add (huy.differentiableAt (by norm_num))
      (hvy.differentiableAt (by norm_num))
  have huSecond : HasFDerivAt (fun y : PDE.Vec n => fderiv ℝ g_u y)
      (fderiv ℝ (fderiv ℝ g_u) z.2) z.2 :=
    ((hu.spatialSlice_contDiffAt hz).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hvSecond : HasFDerivAt (fun y : PDE.Vec n => fderiv ℝ g_v y)
      (fderiv ℝ (fderiv ℝ g_v) z.2) z.2 :=
    ((hv.spatialSlice_contDiffAt hz).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hsecond : fderiv ℝ (fderiv ℝ (fun y => g_u y + g_v y)) z.2 =
      fderiv ℝ (fderiv ℝ g_u) z.2 + fderiv ℝ (fderiv ℝ g_v) z.2 := by
    calc
      fderiv ℝ (fderiv ℝ (fun y => g_u y + g_v y)) z.2 =
          fderiv ℝ (fun y => fderiv ℝ g_u y + fderiv ℝ g_v y) z.2 :=
        hfirst.fderiv_eq
      _ = fderiv ℝ (fderiv ℝ g_u) z.2 + fderiv ℝ (fderiv ℝ g_v) z.2 :=
        fderiv_fun_add huSecond.differentiableAt hvSecond.differentiableAt
  ext i j
  rw [Matrix.add_apply,
    scalarSpatialHessian_apply_eq_sndFDeriv
    ((hu.spatialSlice_contDiffAt hz).add (hv.spatialSlice_contDiffAt hz)) i j,
    scalarSpatialHessian_apply_eq_sndFDeriv (hu.spatialSlice_contDiffAt hz) i j,
    scalarSpatialHessian_apply_eq_sndFDeriv (hv.spatialSlice_contDiffAt hz) i j,
    hsecond]
  rfl

private theorem isScalarC12On_add {n : ℕ} {u v : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D) :
    IsScalarC12On (fun q => u q + v q) D := by
  refine ⟨hu.continuousOn.add hv.continuousOn, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hu.timeSlice_differentiableAt hz).add (hv.timeSlice_differentiableAt hz)
  · intro z hz
    exact (hu.spatialSlice_contDiffAt hz).add (hv.spatialSlice_contDiffAt hz)
  · apply (hu.continuousOn_scalarTimeDerivative.add
      hv.continuousOn_scalarTimeDerivative).congr
    intro z hz
    exact scalarTimeDerivative_add hu hv hz
  · apply (hu.continuousOn_scalarSpatialGradient.add
      hv.continuousOn_scalarSpatialGradient).congr
    intro z hz
    exact scalarSpatialGradient_add hu hv hz
  · apply (hu.continuousOn_scalarSpatialHessian.add
      hv.continuousOn_scalarSpatialHessian).congr
    intro z hz
    exact scalarSpatialHessian_add hu hv hz

private theorem scalarParabolicZeroOrderOperator_add {n : ℕ}
    (a : CoefficientField n) (b : ℝ → PDE.Vec n → PDE.Vec n)
    (c : ℝ → PDE.Vec n → ℝ) {u v : TimeVelocity n → ℝ}
    {D : Set (TimeVelocity n)} (hu : IsScalarC12On u D) (hv : IsScalarC12On v D)
    {z : TimeVelocity n} (hz : z ∈ D) :
    scalarParabolicZeroOrderOperator a b c (fun q => u q + v q) z =
      scalarParabolicZeroOrderOperator a b c u z +
        scalarParabolicZeroOrderOperator a b c v z := by
  rw [scalarParabolicZeroOrderOperator_apply, scalarParabolicZeroOrderOperator_apply,
    scalarParabolicZeroOrderOperator_apply, scalarTimeDerivative_add hu hv hz,
    scalarSpatialGradient_add hu hv hz, scalarSpatialHessian_add hu hv hz]
  have hHessian : matrixContraction (a z.1 z.2)
      (scalarSpatialHessian u z + scalarSpatialHessian v z) =
      matrixContraction (a z.1 z.2) (scalarSpatialHessian u z) +
        matrixContraction (a z.1 z.2) (scalarSpatialHessian v z) := by
    unfold matrixContraction
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  have hGradient : PDE.vecDot (b z.1 z.2)
      (scalarSpatialGradient u z + scalarSpatialGradient v z) =
      PDE.vecDot (b z.1 z.2) (scalarSpatialGradient u z) +
        PDE.vecDot (b z.1 z.2) (scalarSpatialGradient v z) := by
    unfold PDE.vecDot
    simp [mul_add, Finset.sum_add_distrib]
  rw [hHessian, hGradient]
  ring

/-- The negative operator of a smooth stationary terminal lift is smooth. -/
theorem contDiff_terminal_lift_source {d : ℕ}
    (A : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (φ : PDE.Vec d → ℝ) (hA : IsSmoothCoefficient A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2))
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d =>
      -scalarParabolicZeroOrderOperator A b (fun _ _ => 0) (fun p => φ p.2) z) := by
  have hw : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => φ z.2) :=
    hφ.comp contDiff_snd
  have hg (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : TimeVelocity d => scalarSpatialGradient (fun p => φ p.2) z j) := by
    have heq : (fun z : TimeVelocity d => scalarSpatialGradient (fun p => φ p.2) z j) =
        TimeVelocityMultiIndex.coordinateIteratedFDeriv
          (Pi.single (velocityCoord j) 1) (fun p => φ p.2) :=
      funext (fun z => scalarSpatialGradient_apply_eq_coordinateIteratedFDeriv_of_contDiff_two
        (hw.of_le (by simp)) z j)
    rw [heq]
    exact contDiff_coordinateIteratedFDeriv_infty _ _ hw
  have hdot : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d =>
      PDE.vecDot (b z.1 z.2) (scalarSpatialGradient (fun p => φ p.2) z)) := by
    unfold PDE.vecDot
    apply ContDiff.sum
    intro j _
    exact ((contDiff_apply ℝ ℝ j).comp hb).mul (hg j)
  have hres := (contDiff_smooth_backward_residual A hA (fun p => φ p.2) hw).add hdot
  simpa [scalarParabolicZeroOrderOperator_apply, coefficientAt]
    using hres.neg

/-- Adding the smooth terminal lift cancels the correction's negative source. -/
theorem terminal_lift_assembly {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (a T : ℝ) (A : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (φ : PDE.Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hs : tsupport φ ⊆ Ω)
    (W : TimeVelocity d → ℝ)
    (hW : IsClassicalBackwardDirichletSolution a T Ω A b (fun _ _ => 0)
      (fun t y => -scalarParabolicZeroOrderOperator A b (fun _ _ => 0)
        (fun p => φ p.2) (t, y)) (fun _ => 0) (fun _ => 0) W) :
    IsClassicalBackwardDirichletSolution a T Ω A b
      (fun _ _ => 0) (fun _ _ => 0) φ (fun _ => 0) (fun z => φ z.2 + W z) := by
  have hreg : IsScalarC12On (fun z : TimeVelocity d => φ z.2)
      (scalarParabolicOpenCylinder a T Ω) := isScalarC12On_of_contDiff_two
    ((hφ.comp (contDiff_snd : ContDiff ℝ (⊤ : ℕ∞) (Prod.snd : TimeVelocity d → _))).of_le
      (by simp)) (scalarParabolicOpenCylinder a T Ω)
  refine ⟨(hφ.continuous.comp continuous_snd).continuousOn.add hW.1,
    isScalarC12On_add hreg hW.2.1, ?_, ?_, ?_⟩
  · intro z hz
    rw [scalarParabolicZeroOrderOperator_add A b (fun _ _ => 0) hreg hW.2.1 hz,
      hW.2.2.1 z hz]
    exact add_neg_cancel _
  · intro y hy
    change φ y + W (T, y) = φ y
    rw [hW.2.2.2.1 y hy, add_zero]
  · intro z hz
    have hn : z.2 ∉ Ω := by
      have hf := hz.2
      rw [hΩ.frontier_eq] at hf
      exact hf.2
    have hzero : φ z.2 = 0 := image_eq_zero_of_notMem_tsupport (fun h => hn (hs h))
    change φ z.2 + W z = 0
    rw [hzero, hW.2.2.2.2 z hz, zero_add]

end HypoellipticAleksandrov.KineticAleksandrov.Lieberman

end

section



namespace HypoellipticAleksandrov.KineticAleksandrov.Lieberman
open HypoellipticAleksandrov.Parabolic Filter Set HypoellipticAleksandrov.Parabolic.LocalHolder MeasureTheory HypoellipticAleksandrov.Parabolic.Dirichlet
open scoped Topology ENNReal MatrixOrder Matrix.Norms.Elementwise

/-- The spatial barrier gives ambient continuity of the zero extension at lateral points. -/
private theorem continuousAt_source_zeroExtension_lateral_domain {d : ℕ}
    {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (a T : ℝ) (q : PDE.Vec d → ℝ) (hq : Continuous q)
    (hqf : ∀ y ∈ frontier Ω, q y = 0) (w : TimeVelocity d → ℝ)
    (hb : ∀ z ∈ scalarParabolicOpenCylinder a T Ω,
      |w z| ≤ q z.2)
    (p : TimeVelocity d) (hp : p.2 ∈ frontier Ω) :
    ContinuousAt (sourceInteriorZeroExtension a T Ω w) p := by
  classical
  let U := scalarParabolicOpenCylinder a T Ω
  let W := sourceInteriorZeroExtension a T Ω w
  have hpo : p.2 ∉ Ω := by
    rw [hΩ.frontier_eq] at hp
    exact hp.2
  have hpW : W p = 0 := by
    exact piecewise_eq_of_notMem U w (fun _ => 0) (fun h => hpo h.2)
  have hbW (z : TimeVelocity d) : ‖W z‖ ≤ |q z.2| := by
    by_cases hz : z ∈ U
    · rw [show W z = w z from piecewise_eq_of_mem U w (fun _ => 0) hz,
        Real.norm_eq_abs]
      exact (hb z hz).trans (le_abs_self _)
    · rw [show W z = 0 from piecewise_eq_of_notMem U w (fun _ => 0) hz, norm_zero]
      exact abs_nonneg _
  have hc : Continuous (fun z : TimeVelocity d => |q z.2|) :=
    (hq.comp continuous_snd).abs
  have hz : Tendsto (fun z : TimeVelocity d => |q z.2|)
      (𝓝 p) (𝓝 0) := by
    simpa [hqf p.2 hp] using
      (hc.continuousAt (x := p)).tendsto
  change Tendsto W (𝓝 p) (𝓝 (W p))
  rw [hpW]
  exact tendsto_zero_iff_norm_tendsto_zero.2
    (squeeze_zero (fun _ => norm_nonneg _) hbW hz)

/-- A time collar and both envelopes give continuity on the entire closed cylinder. -/
theorem continuousOn_source_zeroExtension_closed_domain {d : ℕ}
    {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (a₀ a T M : ℝ) (ha : a₀ < a) (hM : 0 ≤ M)
    (q : PDE.Vec d → ℝ) (hq : Continuous q)
    (hqf : ∀ y ∈ frontier Ω, q y = 0) (w : TimeVelocity d → ℝ)
    (hw : ContinuousOn w (scalarParabolicOpenCylinder a₀ T Ω))
    (ht : ∀ z ∈ scalarParabolicOpenCylinder a₀ T Ω,
      |w z| ≤ M * (T - z.1))
    (hs : ∀ z ∈ scalarParabolicOpenCylinder a₀ T Ω,
      |w z| ≤ q z.2) :
    ContinuousOn (sourceInteriorZeroExtension a₀ T Ω w)
      (scalarParabolicClosedCylinder a T Ω) := by
  classical
  intro p hp
  by_cases hpt : p.1 = T
  · exact (continuousWithinAt_source_zeroExtension_terminal a₀ T M hM w ht p hpt).mono
      (prod_mono (Icc_subset_Icc ha.le le_rfl) (Subset.refl _))
  · by_cases hpy : p.2 ∈ Ω
    · let U := scalarParabolicOpenCylinder a₀ T Ω
      have hU : IsOpen U := isOpen_Ioo.prod (hΩ)
      have hpu : p ∈ U := ⟨⟨lt_of_lt_of_le ha hp.1.1,
        lt_of_le_of_ne hp.1.2 hpt⟩, hpy⟩
      have he : sourceInteriorZeroExtension a₀ T Ω w =ᶠ[𝓝 p] w := by
        filter_upwards [hU.mem_nhds hpu] with z hz
        exact piecewise_eq_of_mem U w (fun _ => 0) hz
      exact ((hw.continuousAt (hU.mem_nhds hpu)).congr_of_eventuallyEq he).continuousWithinAt
    · have hpf : p.2 ∈ frontier Ω := by
        rw [hΩ.frontier_eq]
        exact ⟨hp.2, hpy⟩
      have hc := continuousAt_source_zeroExtension_lateral_domain hΩ a₀ T q hq hqf w hs p hpf
      exact hc.continuousWithinAt


/-- A stationary source supersolution bounds the absolute value of the energy solution. -/
theorem variational_abs_le_stationary_withDrift {d : ℕ}
    {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (a T : ℝ) (haT : a < T) (lam : ℝ) (hlam : 0 < lam)
    (A : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (hb : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2))
    (hA : IsSmoothCoefficient A)
    (hlo : HasLowerEllipticity lam A) (F G : TimeVelocity d → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (q : PDE.H10Function Ω) (hq : ContDiff ℝ 2 q.toH1Function.toFun)
    (hqn : ∀ y ∈ Ω, 0 ≤ q.toH1Function.toFun y)
    (heq : ∀ z ∈ Icc a T ×ˢ Ω,
      scalarParabolicZeroOrderOperator A b (fun _ _ => 0)
        (fun z => q.toH1Function.toFun z.2) z = G z)
    (hGF : ∀ z ∈ scalarParabolicClosedCylinder a T Ω, G z ≤ -|F z|)
    (u : ReverseTimeL2V hΩ (T - a)) (g : ReverseTimeL2VStar hΩ (T - a))
    (hdu : HasGelfandWeakTimeDerivative hΩ (T - a) (sub_pos.mpr haT) u g)
    (hu : IsReverseTimeVariationalEnergySolution a T haT hΩ hΩb A
      b (fun _ _ => 0) (fun t y => F (t, y))
      ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩ 0 u g hdu) :
    ∀ τ : ℝ, ∀ hτ : τ ∈ Icc 0 (T - a), ∀ᵐ y ∂PDE.volumeOn Ω,
      |reverseTimeHilbertRepresentative hΩ (T - a) (sub_pos.mpr haT)
        u g hdu ⟨τ, hτ⟩ y| ≤ q.toH1Function.toFun y  := by
  have stationarySourceCurve_withDrift {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (a : ℝ) (T : ℝ) (haT : a < T) (A : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (hb : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2)) (hA : IsSmoothCoefficient A) (F : TimeVelocity d → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (q : PDE.H10Function Ω) (hq : ContDiff ℝ 2 q.toH1Function.toFun) (heq : ∀ z ∈ Icc a T ×ˢ Ω,
      scalarParabolicZeroOrderOperator A b (fun _ _ => 0)
        (fun z => q.toH1Function.toFun z.2) z = F z) :
      IsReverseTimeVariationalEnergySolution a T haT hΩ hΩb A
      b (fun _ _ => 0) (fun t y => F (t, y))
      ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩
      (valueCLM hΩ (h10HilbertGraphOfH10Function hΩ q))
      (stationarySourceCurve hΩ (T - a) (h10HilbertGraphOfH10Function hΩ q)) 0
      (stationarySourceCurve_hasWeakTimeDerivative hΩ (T - a) (sub_pos.mpr haT)
        (h10HilbertGraphOfH10Function hΩ q)) := by
    let Q := h10HilbertGraphOfH10Function hΩ q
    let hAs : IsSmoothOnNeighborhood (fun z : TimeVelocity d => A z.1 z.2)
        (scalarParabolicClosedCylinder a T Ω) :=
      ⟨univ, isOpen_univ, subset_univ _, hA.contDiffOn⟩
    let hbs : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
        (scalarParabolicClosedCylinder a T Ω) :=
      ⟨univ, isOpen_univ, subset_univ _, hb.contDiffOn⟩
    let hcs : IsSmoothOnNeighborhood (fun _ : TimeVelocity d => (0 : ℝ))
        (scalarParabolicClosedCylinder a T Ω) :=
      ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
    let hFs : IsSmoothOnNeighborhood F (scalarParabolicClosedCylinder a T Ω) :=
      ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩
    constructor
    · change reverseTimeHilbertRepresentative hΩ (T - a) (sub_pos.mpr haT)
        (stationarySourceCurve hΩ (T - a) Q) 0
        (stationarySourceCurve_hasWeakTimeDerivative hΩ (T - a) (sub_pos.mpr haT) Q)
        ⟨0, ⟨le_rfl, (sub_pos.mpr haT).le⟩⟩ = valueCLM hΩ Q
      rw [stationarySourceCurve_hilbertRepresentative]
      rfl
    · filter_upwards [stationarySourceCurve_ae hΩ (T - a) Q,
        Lp.coeFn_zero (H10HilbertGraphDual hΩ) 2 (reverseTimeVolume (T - a))]
        with τ hqτ hgτ
      intro hτ v
      rw [hqτ, hgτ]
      change 0 + reverseTimeSpatialForm hΩ T τ A b (fun _ _ => 0) Q v = _
      rw [zero_add]
      have hτc : τ ∈ Icc 0 (T - a) := ⟨hτ.1.le, hτ.2.le⟩
      let fτ := reverseTimeSourceSlice T τ (fun t y => F (t, y))
        (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood a T hΩ hΩb
          (fun t y => F (t, y)) hFs τ hτc)
      let L := reverseTimeSpatialFormOperator a T haT hΩ hΩb A
        b (fun _ _ => 0) hAs hbs hcs ⟨τ, hτc⟩ Q
      let R := reverseTimeSourceFunctional hΩ fτ
      have hLR : L = R := by
        apply ContinuousLinearMap.coeFn_injective
        apply Continuous.ext_on
          (denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ)
          L.continuous R.continuous
        rintro _ ⟨ψ, rfl⟩
        change L (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ) =
          R (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ)
        have ha : ∀ i j, ContDiffOn ℝ 1 (fun y => A (T - τ) y i j) Ω := by
          intro i j
          exact contDiffOn_one_coefficientEntry_spatialSlice_of_smoothOnNeighborhood
            a T (T - τ) A hAs (by constructor <;> linarith [hτ.1, hτ.2]) i j
        rw [show L _ = reverseTimeSpatialForm hΩ T τ A b
          (fun _ _ => 0) Q _ from reverseTimeSpatialFormOperator_apply
            a T haT hΩ hΩb A b (fun _ _ => 0) hAs hbs hcs ⟨τ, hτc⟩ Q _,
          reverseTimeSpatialForm_stationary_barrier_weakIdentity hΩ T τ A
            b (fun _ _ => 0) q hq ha
            (continuousOn_vectorEntry_spatialSlice_of_smoothOnNeighborhood
              a T (T - τ) b hbs (by constructor <;> linarith [hτ.1, hτ.2])) continuousOn_const ψ]
        change _ = reverseTimeSourceFunctional hΩ fτ _
        rw [reverseTimeSourceFunctional_apply, L2.inner_def, ← integral_neg]
        apply integral_congr_ae
        filter_upwards [coeFn_reverseTimeSourceSlice T τ (fun t y => F (t, y))
          (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood a T hΩ hΩb
            (fun t y => F (t, y)) hFs τ hτc),
          ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ,
          ae_restrict_mem hΩ.measurableSet] with y hFy hψ hy
        rw [hFy, hψ, heq (T - τ, y)
          ⟨by constructor <;> linarith [hτ.1, hτ.2], hy⟩]
        simp only [RCLike.inner_apply, conj_trivial]
        ring
      rw [← reverseTimeSpatialFormOperator_apply a T haT hΩ hΩb A
        b (fun _ _ => 0) hAs hbs hcs ⟨τ, hτc⟩ Q v]
      exact congrArg (fun D : H10HilbertGraphDual hΩ => D v) hLR
  let Q := h10HilbertGraphOfH10Function hΩ q
  let hAs : IsSmoothOnNeighborhood (fun z : TimeVelocity d => A z.1 z.2)
      (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, hA.contDiffOn⟩
  let hbs : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, hb.contDiffOn⟩
  let hcs : IsSmoothOnNeighborhood (fun _ : TimeVelocity d => (0 : ℝ))
      (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  let hFs : IsSmoothOnNeighborhood F (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩
  let hGs : IsSmoothOnNeighborhood G (scalarParabolicClosedCylinder a T Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, hG.contDiffOn⟩
  have hinit : ∀ᵐ y ∂PDE.volumeOn Ω,
      (0 : PDE.ScalarLp Ω 2) y ≤ valueCLM hΩ Q y := by
    filter_upwards [Lp.coeFn_zero ℝ 2 (PDE.volumeOn Ω),
      valueCLM_h10HilbertGraphOfH10Function hΩ q,
      ae_restrict_mem hΩ.measurableSet] with y hy hqy hyo
    rw [hy, hqy]
    exact hqn y hyo
  have hqenergy := stationarySourceCurve_withDrift
    hΩ hΩb a T haT A b hb hA G hG q hq heq
  have hupper := reverseTimeVariationalEnergySolution_le a T lam haT hlam hΩ hΩb
    A b (fun _ _ => 0) (fun t y => F (t, y)) (fun t y => G (t, y))
    hAs hbs hcs hFs hGs (fun z _ => hlo z.1 z.2) (fun _ _ => le_rfl)
    (fun z hz => (hGF z hz).trans (neg_abs_le (F z)))
    0 (valueCLM hΩ Q) hinit u g hdu hu
    (stationarySourceCurve hΩ (T - a) Q) 0
    (stationarySourceCurve_hasWeakTimeDerivative hΩ (T - a) (sub_pos.mpr haT) Q) hqenergy
  have hninit : ∀ᵐ y ∂PDE.volumeOn Ω,
      (-(0 : PDE.ScalarLp Ω 2)) y ≤ valueCLM hΩ Q y := by
    simpa using hinit
  have hneg := reverseTimeVariationalEnergySolution_le a T lam haT hlam hΩ hΩb
    A b (fun _ _ => 0) (fun t y => -F (t, y)) (fun t y => G (t, y))
    hAs hbs hcs (IsSmoothOnNeighborhood.neg hFs) hGs
    (fun z _ => hlo z.1 z.2) (fun _ _ => le_rfl)
    (fun z hz => (hGF z hz).trans (neg_le_neg (le_abs_self (F z))))
    (-0) (valueCLM hΩ Q) hninit ((-1 : ℝ) • u) ((-1 : ℝ) • g)
    (hdu.smul (-1)) hu.neg (stationarySourceCurve hΩ (T - a) Q) 0
    (stationarySourceCurve_hasWeakTimeDerivative hΩ (T - a) (sub_pos.mpr haT) Q) hqenergy
  rw [stationarySourceCurve_hilbertRepresentative] at hupper hneg
  rw [reverseTimeHilbertRepresentative_neg_eq] at hneg
  intro τ hτ
  filter_upwards [hupper τ hτ, hneg τ hτ,
    valueCLM_h10HilbertGraphOfH10Function hΩ q,
    Lp.coeFn_neg (reverseTimeHilbertRepresentative hΩ (T - a) (sub_pos.mpr haT)
      u g hdu ⟨τ, hτ⟩)] with y hu₁ hu₂ hqy hn
  change _ ≤ valueCLM hΩ Q y at hu₁
  change (-reverseTimeHilbertRepresentative hΩ (T - a) (sub_pos.mpr haT)
    u g hdu ⟨τ, hτ⟩) y ≤ valueCLM hΩ Q y at hu₂
  rw [hn, Pi.neg_apply, hqy] at hu₂
  rw [hqy] at hu₁
  exact abs_le.mpr ⟨by linarith, hu₁⟩

end HypoellipticAleksandrov.KineticAleksandrov.Lieberman

namespace HypoellipticAleksandrov.KineticAleksandrov
set_option autoImplicit false
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Lieberman Set MeasureTheory Filter HypoellipticAleksandrov.Parabolic.Dirichlet HypoellipticAleksandrov.Parabolic.LocalHolder
open scoped Matrix ENNReal Topology MatrixOrder Matrix.Norms.Elementwise BigOperators

private theorem exists_signed_source_ellipsoid_correction
    {d : ℕ} (hd : 0 < d) {Q : PDE.Mat d} (hQ : Q.PosDef)
    (a T lam Lam : ℝ) (haT : a < T) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (hsym : ∀ t y, (A t y).IsSymm) (hA : IsSmoothCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (hb : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2))
    (F : TimeVelocity d → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ∃ W : TimeVelocity d → ℝ,
      IsClassicalBackwardDirichletSolution a T (openEllipsoid Q) A b
        (fun _ _ => 0) (fun t y => F (t, y)) (fun _ => 0) (fun _ => 0) W  := by
  have classical_abs_le_source_time_withDrift {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (a : ℝ) (T : ℝ) (lam : ℝ) (haT : a < T) (hlam : 0 < lam) (A : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (hb : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2)) (hA : IsSmoothCoefficient A) (hlo : HasLowerEllipticity lam A) (F : TimeVelocity d → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (M : ℝ) (hM : 0 ≤ M) (hFM : ∀ z ∈ scalarParabolicClosedCylinder a T Ω, |F z| ≤ M) (u : ReverseTimeL2V hΩ (T - a)) (g : ReverseTimeL2VStar hΩ (T - a)) (hdu : HasGelfandWeakTimeDerivative hΩ (T - a) (sub_pos.mpr haT) u g) (hu : IsReverseTimeVariationalEnergySolution a T haT hΩ hΩb A
      b (fun _ _ => 0) (fun t y => F (t, y))
      ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩ 0 u g hdu) (w : TimeVelocity d → ℝ) (hw : ContinuousOn w (scalarParabolicOpenCylinder a T Ω)) (hwslice : ∀ᵐ t ∂volume.restrict (Ioo a T),
      (fun y => w (t, y)) =ᵐ[PDE.volumeOn Ω] fun y => valueCLM hΩ (u (T - t)) y) :
      ∀ z ∈ scalarParabolicOpenCylinder a T Ω, |w z| ≤ M * (T - z.1) := by
    have hAs : IsSmoothOnNeighborhood (fun z : TimeVelocity d => A z.1 z.2)
        (scalarParabolicClosedCylinder a T Ω) :=
      ⟨univ, isOpen_univ, subset_univ _, hA.contDiffOn⟩
    have hbs : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
        (scalarParabolicClosedCylinder a T Ω) :=
      ⟨univ, isOpen_univ, subset_univ _, hb.contDiffOn⟩
    have hcs : IsSmoothOnNeighborhood (fun _ : TimeVelocity d => (0 : ℝ))
        (scalarParabolicClosedCylinder a T Ω) :=
      ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
    have hFs : IsSmoothOnNeighborhood F (scalarParabolicClosedCylinder a T Ω) :=
      ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩
    have henv := hu.abs_reverseTimeHilbertRepresentative_le_affine a T lam haT hlam
      hΩ hΩb A b (fun _ _ => 0) (fun t y => F (t, y)) hAs hbs hcs hFs
      (fun z _ => hlo z.1 z.2) (fun _ _ => le_rfl) 0 M le_rfl hM hFM 0
      (by filter_upwards [Lp.coeFn_zero ℝ 2 (PDE.volumeOn Ω)] with y hy
          rw [hy]; simp [le_refl]) u g hdu
    have hraw : ∀ᵐ τ ∂reverseTimeVolume (T - a),
        ∀ hτ : τ ∈ Ioo 0 (T - a),
          ∀ᵐ y ∂PDE.volumeOn Ω, |valueCLM hΩ (u τ) y| ≤ M * τ := by
      filter_upwards [(reverseTimeHilbertRepresentative_spec hΩ (T - a)
        (sub_pos.mpr haT) u g hdu).1] with τ hrep hτ
      have hb := henv τ ⟨hτ.1.le, hτ.2.le⟩
      rw [hrep hτ] at hb
      simpa [mul_comm] using hb
    have horig := (sourceTimeReflection_measurePreserving a T).quasiMeasurePreserving.ae hraw
    have hbound : ∀ᵐ t ∂volume.restrict (Ioo a T),
        ∀ᵐ y ∂PDE.volumeOn Ω, |w (t, y)| ≤ M * (T - t) := by
      filter_upwards [hwslice, horig, ae_restrict_mem measurableSet_Ioo] with t hs hr ht
      have ht' : T - t ∈ Ioo 0 (T - a) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      filter_upwards [hs, hr ht'] with y hy hb
      rw [hy]
      exact hb
    exact abs_le_source_time_of_continuousOn_of_ae_slices hΩ a T M w hw hbound
  classical
  let Ω := openEllipsoid Q
  have hΩ : IsOpen Ω := isOpen_openEllipsoid Q
  have hΩb : Bornology.IsBounded Ω := (openEllipsoid_geometry hQ).1
  have hleft : a - 1 < a := sub_lt_self a zero_lt_one
  have hleftT : a - 1 < T := hleft.trans haT
  obtain ⟨C, hC⟩ := (isCompact_scalarParabolicClosedCylinder (a - 1) T
    hΩb).exists_bound_of_continuousOn hF.continuous.continuousOn
  let M := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hFM : ∀ z ∈ scalarParabolicClosedCylinder (a - 1) T Ω, |F z| ≤ M := fun z hz =>
    (Real.norm_eq_abs _ ▸ hC z hz).trans (le_max_left _ _)
  obtain ⟨B, hB, hbB⟩ := exists_closedCylinder_drift_bound hΩb (a - 1) T b hb.continuous
  obtain ⟨q, hq, hqn, hqf, hqop⟩ := exists_h10_ellipsoid_drift_barrier hd hQ (a - 1) T lam M B
    hlam hM hB A b hsym (fun z _ => hlo z.1 z.2) hbB
  obtain ⟨u, g, hdu, hu, w, _, hs, hw, he⟩ := exists_classicalInterior_of_variational_hormander
    hΩ hΩb (a - 1) T hleftT lam Lam hlam hLam A b hA hb hlo hhi F hF
  have ht := classical_abs_le_source_time_withDrift hΩ hΩb (a - 1) T lam hleftT hlam A b hb hA
    hlo F hF M hM hFM u g hdu hu w hw.continuousOn hs
  let G : TimeVelocity d → ℝ := scalarParabolicZeroOrderOperator A b (fun _ _ => 0)
    (fun p => q.toH1Function.toFun p.2)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := by
    simpa only [neg_neg] using (contDiff_terminal_lift_source A b q.toH1Function.toFun hA hb hq).neg
  have hcl : closure (scalarParabolicOpenCylinder (a - 1) T Ω) =
      scalarParabolicClosedCylinder (a - 1) T Ω := by
    unfold scalarParabolicOpenCylinder scalarParabolicClosedCylinder
    rw [closure_prod_eq, closure_Ioo hleftT.ne]
  have hGF : ∀ z ∈ scalarParabolicClosedCylinder (a - 1) T Ω, G z ≤ -|F z| := fun z hz =>
    (le_on_closure (fun p hp => hqop p ⟨⟨hp.1.1.le, hp.1.2.le⟩, hp.2⟩)
      hG.continuous.continuousOn continuous_const.continuousOn (hcl.symm ▸ hz)).trans
      (neg_le_neg (hFM z hz))
  have henergy := variational_abs_le_stationary_withDrift hΩ hΩb (a - 1) T hleftT lam hlam A b hb
    hA hlo F G hF hG q (hq.of_le (by simp)) (fun y hy => hqn y (subset_closure hy))
    (fun _ _ => rfl) hGF u g hdu hu
  have hspace := classicalEnergyRepresentative_abs_le_continuous_barrier hΩ (a - 1) T hleftT
    u g hdu q.toH1Function.toFun hq.continuous henergy w hw.continuousOn hs
  let U := scalarParabolicOpenCylinder (a - 1) T Ω
  let D := scalarParabolicOpenCylinder a T Ω
  let W := sourceInteriorZeroExtension (a - 1) T Ω w
  have hsub : D ⊆ U := prod_mono (Ioo_subset_Ioo hleft.le le_rfl) Subset.rfl
  have hWD : EqOn W w D := fun _ hz => piecewise_eq_of_mem U w (fun _ => 0) (hsub hz)
  have hwD : IsScalarC12On w D :=
    ⟨hw.continuousOn.mono hsub, fun _ hz => hw.timeSlice_differentiableAt (hsub hz),
      fun _ hz => hw.spatialSlice_contDiffAt (hsub hz),
      hw.continuousOn_scalarTimeDerivative.mono hsub,
      hw.continuousOn_scalarSpatialGradient.mono hsub,
      hw.continuousOn_scalarSpatialHessian.mono hsub⟩
  have hD : IsOpen D := isOpen_Ioo.prod hΩ
  obtain ⟨hdt, hdg, hdd⟩ := Occupation.scalarJet_eqOn_of_eqOn_open hD hWD
  refine ⟨W, continuousOn_source_zeroExtension_closed_domain hΩ (a - 1) a T M hleft hM
      q.toH1Function.toFun hq.continuous hqf w hw.continuousOn ht hspace,
    Occupation.isScalarC12On_congr_open hD hwD hWD, ?_,
    fun _ _ => piecewise_eq_of_notMem U w (fun _ => 0) fun h => lt_irrefl T h.1.2,
    fun z hz => piecewise_eq_of_notMem U w (fun _ => 0) fun h =>
      (hΩ.frontier_eq ▸ hz.2).2 h.2⟩
  intro z hz
  simp only [scalarParabolicZeroOrderOperator_apply, zero_mul, add_zero, hdt hz, hdg hz, hdd hz]
  simpa only [coefficientAt] using he z (hsub hz)

theorem ellipsoidDirichlet_aux
    {N : ℕ} {r₀ r₁ : ℝ} {Q : PDE.Mat N}
    (hQ : Q.PosDef) (hr : r₀ < r₁) (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (a : CoefficientField N) (b : ℝ → PDE.Vec N → PDE.Vec N)
    (haSymm : ∀ t v, (a t v).IsSymm) (haSmooth : IsSmoothCoefficient a)
    (haLower : ∀ t v, lam • (1 : PDE.Mat N) ≤ a t v)
    (haUpper : ∀ t v, a t v ≤ Lam • (1 : PDE.Mat N))
    (hbSmooth : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity N => b z.1 z.2))
    (φ : PDE.Vec N → ℝ) (hφSmooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (_hφCompact : HasCompactSupport φ) (hφSupport : tsupport φ ⊆ openEllipsoid Q) :
    ∃ u : TimeVelocity N → ℝ,
      IsClassicalBackwardDirichletSolution
        r₀ r₁ (openEllipsoid Q) a b (fun _ _ => 0) (fun _ _ => 0) φ (fun _ => 0) u ∧
      ∀ v : TimeVelocity N → ℝ,
        IsClassicalBackwardDirichletSolution
          r₀ r₁ (openEllipsoid Q) a b (fun _ _ => 0) (fun _ _ => 0) φ (fun _ => 0) v →
          Set.EqOn v u (scalarParabolicClosedCylinder r₀ r₁ (openEllipsoid Q))  := by
  have dimension_zero_solution (r₀ r₁ : ℝ) (Q : PDE.Mat 0) (A : CoefficientField 0) (b : ℝ → PDE.Vec 0 → PDE.Vec 0) (φ : PDE.Vec 0 → ℝ) :
      IsClassicalBackwardDirichletSolution r₀ r₁ (openEllipsoid Q) A b
      (fun _ _ => 0) (fun _ _ => 0) φ (fun _ => 0) (fun z => φ z.2) := by
    have heq : (fun z : TimeVelocity 0 => φ z.2) = fun _ => φ 0 :=
      funext (fun _ => congrArg φ (Subsingleton.elim _ _))
    have hΩ : openEllipsoid Q = univ := by
      ext x
      simp [openEllipsoid, PDE.vecDot]
    rw [heq]
    refine ⟨continuous_const.continuousOn,
      isScalarC12On_of_contDiff_two contDiff_const _, ?_, ?_, ?_⟩
    · intro z _
      simp [scalarParabolicZeroOrderOperator_apply, scalarTimeDerivative,
        matrixContraction, PDE.vecDot]
    · intro y _
      exact congrArg φ (Subsingleton.elim _ _)
    · intro z hz
      have hf : z.2 ∈ frontier (openEllipsoid Q) := hz.2
      rw [hΩ, frontier_univ] at hf
      exact hf.elim
  have hΩ := isOpen_openEllipsoid Q
  have hex : ∃ u : TimeVelocity N → ℝ,
      IsClassicalBackwardDirichletSolution r₀ r₁ (openEllipsoid Q) a b
        (fun _ _ => 0) (fun _ _ => 0) φ (fun _ => 0) u := by
    cases N with
    | zero => exact ⟨fun z => φ z.2, dimension_zero_solution r₀ r₁ Q a b φ⟩
    | succ n =>
      obtain ⟨W, hW⟩ := exists_signed_source_ellipsoid_correction (Nat.succ_pos n)
        hQ r₀ r₁ lam Lam hr hlam hlamLam a b haSymm haSmooth haLower haUpper hbSmooth _
        (contDiff_terminal_lift_source a b φ haSmooth hbSmooth hφSmooth)
      exact ⟨fun z => φ z.2 + W z, terminal_lift_assembly hΩ r₀ r₁ a b φ hφSmooth hφSupport W hW⟩
  obtain ⟨u, hu⟩ := hex
  exact ⟨u, hu, fun v hv => eqOn_closedCylinder_of_isClassicalBackwardDirichletSolution
    hΩ (openEllipsoid_geometry hQ).1 hr a b (fun _ _ => 0) (fun _ _ => 0) φ (fun _ => 0) v u
    haSmooth.continuous hbSmooth.continuous
    (fun t y => (HasLowerEllipticity.posDef haLower hlam t y).posSemidef) (fun _ _ => le_rfl) hv hu⟩

set_option autoImplicit false


def HormanderHypoellipticityStatement : Prop :=
  ∀ {k N : ℕ} {Ω : Set (PDE.Vec N)}
    (_ : IsOpen Ω)
    (X : Fin (k + 1) → PDE.Vec N → PDE.Vec N)
    (c g u : PDE.Vec N → ℝ)
    (_ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (_ : LieAlgebraSpansOn Ω X)
    (_ : ContDiffOn ℝ (⊤ : ℕ∞) c Ω)
    (_ : HasWeakHormanderEquation Ω X c g u),
    ∃ f : PDE.Vec N → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧
        u =ᵐ[Measure.restrict volume Ω] f

theorem hormanderHypoellipticityStatement_holds : HormanderHypoellipticityStatement :=
  @exists_smooth_aeRepresentative_of_hormander_aux

def LiebermanEllipsoidDirichletStatement : Prop :=
  ∀ {N : ℕ} {r₀ r₁ : ℝ} {Q : PDE.Mat N}
    (_ : Q.PosDef)
    (_ : r₀ < r₁)
    (lam Lam : ℝ)
    (_ : 0 < lam)
    (_ : lam ≤ Lam)
    (a : CoefficientField N)
    (b : ℝ → PDE.Vec N → PDE.Vec N)
    (_ : ∀ t v, (a t v).IsSymm)
    (_ : IsSmoothCoefficient a)
    (_ : ∀ t v, lam • (1 : PDE.Mat N) ≤ a t v)
    (_ : ∀ t v, a t v ≤ Lam • (1 : PDE.Mat N))
    (_ : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : TimeVelocity N => b z.1 z.2))
    (φ : PDE.Vec N → ℝ)
    (_ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (_ : HasCompactSupport φ)
    (_ : tsupport φ ⊆ openEllipsoid Q),
    ∃ u : TimeVelocity N → ℝ,
      IsClassicalBackwardDirichletSolution
        r₀ r₁ (openEllipsoid Q) a b
        (fun _ _ => 0) (fun _ _ => 0) φ (fun _ => 0) u ∧
      ∀ v : TimeVelocity N → ℝ,
        IsClassicalBackwardDirichletSolution
          r₀ r₁ (openEllipsoid Q) a b
          (fun _ _ => 0) (fun _ _ => 0) φ (fun _ => 0) v →
          Set.EqOn v u
            (scalarParabolicClosedCylinder r₀ r₁ (openEllipsoid Q))

theorem liebermanEllipsoidDirichletStatement_holds : LiebermanEllipsoidDirichletStatement :=
  @ellipsoidDirichlet_aux

end HypoellipticAleksandrov.KineticAleksandrov

end

