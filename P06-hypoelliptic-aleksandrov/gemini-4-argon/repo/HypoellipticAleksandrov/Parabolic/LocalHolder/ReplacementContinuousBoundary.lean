module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxUniform
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxClosedLimitRegularity
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovRegularity
import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxBoundary
import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementEnergyBoundary
import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementSmoothBoundary
import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementSmoothResidual
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparison
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBoundaryStability
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonCalculus
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Cauchy

/-! # Homogeneous backward replacement for continuous closed-ball data

Smooth boundary approximation converges uniformly with the exact traces. The internally
proved local energy and compactness argument establishes the limit's classical equation.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped Topology Matrix.Norms.Elementwise
open Dirichlet KineticAleksandrov
open scoped MatrixOrder

/- Arbitrary continuous closed-ball data have an actual classical homogeneous replacement. -/
theorem exists_continuous_backward_homogeneous_replacement {d } (hd : 0 < d)
    (v₀ : PDE.Vec d) (r ) (hr : 0 < r) (a T : ℝ) (haT : a < T)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (A ) (hA : IsSmoothCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (w : TimeVelocity d → ℝ)
    (hw : ContinuousOn w (scalarParabolicClosedCylinder a T (PDE.euclideanBall v₀ r))) :
    ∃ v : TimeVelocity d → ℝ,
      IsClassicalBackwardDirichletSolution a T (PDE.euclideanBall v₀ r) A
        (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun y => w (T, y)) w v := by
  classical
  let Ω := PDE.euclideanBall v₀ r
  let K := scalarParabolicClosedCylinder a T Ω
  obtain ⟨f, u, U, V, hf, hfb, hu, hUeq, hlim, htrace⟩ : ∃ (f v : ℕ → TimeVelocity d → ℝ)
      (U : ℕ → C(scalarParabolicClosedCylinder a T (PDE.euclideanBall v₀ r), ℝ))
      (V : C(scalarParabolicClosedCylinder a T (PDE.euclideanBall v₀ r), ℝ)),
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n)) ∧
      (∀ n, ∀ z ∈ scalarParabolicClosedCylinder a T (PDE.euclideanBall v₀ r),
        |f n z - w z| < 1 / ((n : ℝ) + 1)) ∧
      (∀ n, IsClassicalBackwardDirichletSolution a T (PDE.euclideanBall v₀ r) A
        (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
        (fun y => f n (T, y)) (f n) (v n)) ∧
      (∀ n z, U n z = v n z) ∧ Tendsto U atTop (𝓝 V) ∧
      ∀ z : scalarParabolicClosedCylinder a T (PDE.euclideanBall v₀ r),
        (z : TimeVelocity d) ∈ scalarParabolicTerminalLateralBoundary a T
        (PDE.euclideanBall v₀ r) → V z = w z := by
    classical
    let Ω := PDE.euclideanBall v₀ r
    let K := scalarParabolicClosedCylinder a T Ω
    have hΩ : IsOpen Ω := PDE.isOpen_euclideanBall v₀ r
    have hΩb : Bornology.IsBounded Ω := Occupation.isBounded_euclideanBall v₀ hr
    have hK : IsCompact K := isCompact_scalarParabolicClosedCylinder a T hΩb
    let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    have hεpos (n : ℕ) : 0 < ε n := one_div_pos.mpr (by positivity)
    have happrox (n : ℕ) : ∃ f : TimeVelocity d → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) f ∧ ∀ z ∈ K, |f z - w z| < ε n := by
      obtain ⟨f, hf, _, _, hb⟩ := exists_smooth_compact_boundary_approx hK
        isOpen_univ (subset_univ _) w hw (hεpos n)
      exact ⟨f, hf, hb⟩
    choose f hf hfb using happrox
    have hvex (n : ℕ) : ∃ v : TimeVelocity d → ℝ,
        IsClassicalBackwardDirichletSolution a T (PDE.euclideanBall v₀ r) A
          (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
          (fun y => (f n) (T, y)) (f n) v := by
      let w := (f n)
      have hw := (hf n)
      let F : TimeVelocity d → ℝ := fun z => scalarTimeDerivative w z +
        matrixContraction (coefficientAt A z) (scalarSpatialHessian w z)
      have hF := contDiff_smooth_backward_residual A hA w hw
      obtain ⟨u, hu⟩ := exists_signed_source_ball_correction hd v₀ r hr a T haT
        lam Lam hlam hlamLam A hA hlo hhi F hF
      have hwr := isScalarC12On_of_contDiff_two (hw.of_le (by simp))
        (scalarParabolicOpenCylinder a T (PDE.euclideanBall v₀ r))
      refine ⟨fun z => w z - u z,
        hw.continuous.continuousOn.sub hu.1, isScalarC12On_sub hwr hu.2.1, ?_, ?_, ?_⟩
      · intro z hz
        rw [scalarParabolicZeroOrderOperator_sub A (fun _ _ => 0) (fun _ _ => 0)
          hwr hu.2.1 hz, hu.2.2.1 z hz]
        have hwF : scalarParabolicZeroOrderOperator A (fun _ _ => 0) (fun _ _ => 0) w z = F z := by
          simp only [scalarParabolicZeroOrderOperator_apply, Pi.zero_apply, PDE.vecDot,
            zero_mul, Finset.sum_const_zero, add_zero]
          rfl
        rw [hwF, sub_self]
      · intro y hy
        change w (T, y) - u (T, y) = w (T, y)
        rw [hu.2.2.2.1 y hy, sub_zero]
      · intro z hz
        change w z - u z = w z
        rw [hu.2.2.2.2 z hz, sub_zero]
    choose v hv using hvex
    let U : ℕ → C(K, ℝ) := fun n =>
      ⟨fun z => v n z, continuousOn_iff_continuous_domRestrict.mp (hv n).1⟩
    have hdiff (n m : ℕ) : dist (U n) (U m) ≤ 2 * (ε n + ε m) := by
      rw [dist_eq_norm]
      apply (ContinuousMap.norm_le _ (by positivity)).2
      intro z
      change |v n z - v m z| ≤ _
      apply abs_homogeneous_solution_sub_le_boundary_error hΩ hΩb a T haT A
        hA.continuous (Occupation.posSemidef_of_lower_loewner hlam hlo)
        (fun y => f n (T, y)) (fun y => f m (T, y)) (f n) (f m) (v n) (v m)
        (hv n) (hv m) (ε n + ε m) (by positivity) ?_ ?_ z z.property
      · intro y hy
        have hz : (T, y) ∈ K := ⟨⟨haT.le, le_rfl⟩, hy⟩
        calc
          |f n (T, y) - f m (T, y)| ≤ |f n (T, y) - w (T, y)| +
              |f m (T, y) - w (T, y)| := by
                simpa only [abs_sub_comm (w (T, y)) (f m (T, y))] using
                  abs_sub_le (f n (T, y)) (w (T, y)) (f m (T, y))
          _ ≤ ε n + ε m := add_le_add (hfb n _ hz).le (hfb m _ hz).le
      · intro z hz
        have hzK : z ∈ K := ⟨hz.1, frontier_subset_closure hz.2⟩
        calc
          |f n z - f m z| ≤ |f n z - w z| + |f m z - w z| := by
            simpa only [abs_sub_comm (w z) (f m z)] using abs_sub_le (f n z) (w z) (f m z)
          _ ≤ ε n + ε m := add_le_add (hfb n _ hzK).le (hfb m _ hzK).le
    have hε : Tendsto ε atTop (𝓝 0) := by
      simpa only [ε, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have _h_xinl_0 : CauchySeq U := by
      rw [Metric.cauchySeq_iff]
      intro δ hδ
      obtain ⟨N, hN⟩ := eventually_atTop.mp
        (hε.eventually_lt_const (show 0 < δ / 4 by positivity))
      refine ⟨N, fun n hn m hm => ?_⟩
      have hnδ := hN n hn
      have hmδ := hN m hm
      exact lt_of_le_of_lt (hdiff n m) (by linarith)
    obtain ⟨V, hV⟩ := cauchySeq_tendsto_of_complete
      _h_xinl_0
    refine ⟨f, v, U, V, hf, hfb, hv, fun _ _ => rfl, hV, ?_⟩
    intro z hz
    have hfz : Tendsto (fun n => f n z) atTop (𝓝 (w z)) := by
      apply tendsto_iff_dist_tendsto_zero.2
      apply squeeze_zero (fun _ => dist_nonneg)
        (fun n => (show dist (f n z) (w z) < ε n by
          simpa only [Real.dist_eq] using hfb n z z.property).le) hε
    have hUz : ∀ n, U n z = f n z := by
      intro n
      change v n z = f n z
      rcases hz with hz | hz
      · have ht : z.val.1 = T := mem_singleton_iff.mp hz.1
        simpa only [← ht, Prod.mk.eta] using (hv n).2.2.2.1 z.val.2 hz.2
      · exact (hv n).2.2.2.2 z hz
    have hlim :=
      ((continuous_eval_const z).tendsto V).comp hV
    have hlimw : Tendsto (fun n => U n z) atTop (𝓝 (w z)) := by
      simpa only [hUz] using hfz
    exact tendsto_nhds_unique hlim hlimw
  have hEq (n : ℕ) (z : TimeVelocity d) (hz : z ∈ Ioo a T ×ˢ Ω) :
      scalarTimeDerivative (u n) z +
        matrixContraction (coefficientAt A z) (scalarSpatialHessian (u n) z) = 0 := by
    have he := (hu n).2.2.1 z hz
    simpa only [scalarParabolicZeroOrderOperator_apply, coefficientAt, PDE.vecDot, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero, add_zero] using he
  obtain ⟨hv12, hveq⟩ := homogeneous_continuousMap_limit_is_classical a T Ω
    (PDE.isOpen_euclideanBall v₀ r)
    (KineticAleksandrov.Occupation.isBounded_euclideanBall v₀ hr).isCompact_closure
    A hA lam Lam hlam hlamLam hlo hhi u (fun n => (hu n).2.1) hEq U V hUeq hlim
  refine ⟨continuousMapZeroExtension V,
    continuousOn_continuousMapZeroExtension V, hv12, ?_, ?_, ?_⟩
  · intro z hz
    simpa only [scalarParabolicZeroOrderOperator_apply, coefficientAt, PDE.vecDot, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero, add_zero] using hveq z hz
  · intro y hy
    have hzK : (T, y) ∈ K := ⟨⟨haT.le, le_rfl⟩, hy⟩
    change continuousMapZeroExtension V (T, y) = w (T, y)
    rw [continuousMapZeroExtension, dite_eq_left hzK]
    exact htrace ⟨(T, y), hzK⟩ (Or.inl ⟨mem_singleton T, hy⟩)
  · intro z hz
    have hzK : z ∈ K := ⟨hz.1, frontier_subset_closure hz.2⟩
    rw [continuousMapZeroExtension, dite_eq_left hzK]
    exact htrace ⟨z, hzK⟩ (Or.inr hz)

end HypoellipticAleksandrov.Parabolic.LocalHolder
