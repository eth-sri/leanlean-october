module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakGradientBallwiseGluing
public import PDEFoundation.Sobolev.H1.Composition

/-!
# Weak chain rule on general open sets

The bounded-derivative chain rule is localized to Euclidean balls and then
glued over an arbitrary open set.  The normalization at zero supplies the
global `L²` control of the composed representative.
-/

 public section

namespace PDE.H1Function

open MeasureTheory Set

/-- A `C¹` real composition with bounded derivative has the expected weak
gradient on an arbitrary open set, provided the composition fixes zero. -/
theorem hasWeakGradient_comp_contDiff_of_deriv_bounded_of_isOpen
    {d : ℕ} {U : PDE.VelocityRegion d} (hU : IsOpen U)
    (u : PDE.H1Function U) {G : ℝ → ℝ}
    (hG : ContDiff ℝ 1 G) (hG0 : G 0 = 0)
    {M : ℝ} (hM : 0 ≤ M) (hderiv : ∀ t, |deriv G t| ≤ M) :
    PDE.HasWeakGradientOn U (fun x => G (u.toFun x))
      (fun x i => deriv G (u.toFun x) * u.grad x i) := by



  have hcompLocal  :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((show MemLp (fun x => G (u.toFun x)) 2 (volume.restrict U) by
          simpa only [Function.comp_def, PDE.volumeOn] using
            (PDE.lipschitzWith_of_abs_deriv_le hM (hG.differentiable (by norm_num)) hderiv).comp_memLp hG0 u.memL2).locallyIntegrable (by norm_num))

  have hgradMem (i : Fin d) :
      MemLp (fun x => deriv G (u.toFun x) * u.grad x i)
        2 (volume.restrict U) := by
    refine MemLp.of_le_mul (c := M) (u.gradMemL2 i) ?_ ?_
    · exact
        ((hG.continuous_deriv (by norm_num)).comp_aestronglyMeasurable
          u.memL2.aestronglyMeasurable).mul
          (u.gradMemL2 i).aestronglyMeasurable
    · filter_upwards with x
      simp only [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (hderiv (u.toFun x)) (abs_nonneg (u.grad x i))
  apply PDE.HasWeakGradientOn.of_ballwise hU hcompLocal
    (fun i => locallyIntegrableOn_of_locallyIntegrable_restrict
      ((hgradMem i).locallyIntegrable (by norm_num)))
  intro x hx
  rcases Metric.isOpen_iff.1 hU x hx with ⟨δ, hδ, hball⟩
  let R : ℝ := δ / 2
  have hR : 0 < R := by
    dsimp only [R]
    positivity
  have hclosed : PDE.euclideanClosedBall x R ⊆ U :=
    (PDE.euclideanClosedBall_subset_supClosedBall hR.le).trans
      ((Metric.closedBall_subset_ball (by
        dsimp only [R]
        linarith)).trans hball)
  refine ⟨R, hR, hclosed, ?_⟩
  let uR  :=
    u.restrict (PDE.isOpen_euclideanBall x R)
      ((PDE.euclideanBall_subset_euclideanClosedBall x R).trans hclosed)
  exact PDE.H1Function.hasWeakGradient_comp_contDiff_of_deriv_bounded
      (PDE.isOpenBoundedConvexDomain_euclideanBall x hR)
      uR hG hM hderiv

end PDE.H1Function
