module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelInnerSequence
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.DifferentiationGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
import Mathlib.Tactic.Ring



/-! # Fixed-margin exhaustion and local cylinders below the terminal face -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Filter Holder.Covering


variable {d : ℕ}

/-- The shifted centers preserve the free-transport position coordinate exactly. -/
theorem borelInnerCentre_relativePosition  (P₀ P : KineticPoint d)
    (R : ℝ) (n : ℕ) :
    relativePosition (borelInnerCentre P₀ R n) P = relativePosition P₀ P := by
  ext <;> simp_all [relativePosition, borelInnerCentre] <;> ring

/-- Each fixed positive interior fraction is exhausted with that same fraction. -/
theorem borel_inner_fraction_exhaustion  (P₀ : KineticPoint d)
    (R : ℝ) (hR : 0 < R) (θ : ℝ) (hθ : 0 < θ)
    (P : KineticPoint d) (hP : P ∈ backwardCylinder P₀ (θ * R)) :
    ∀ᶠ n in atTop, P ∈ backwardCylinder (borelInnerCentre P₀ R n)
      (θ * borelInnerRadius R hR n) := by
  have hrad := (borelInnerRadius_tendsto R hR).const_mul θ
  have hdelta := borelInnerDelta_tendsto R






  filter_upwards [((tendsto_order.mp (by simpa only [sub_zero] using (((tendsto_const_nhds (x := P₀.time)).sub hdelta).sub (hrad.pow 2)))).2 P.time hP.1), ((tendsto_order.mp (by simpa only [sub_zero] using ((tendsto_const_nhds (x := P₀.time)).sub hdelta))).1 P.time hP.2.1), (tendsto_order.mp hrad).1 _ ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (mul_pos hθ hR)).mp hP.2.2.1),
    (tendsto_order.mp (hrad.pow 3)).1 _ (by
        simpa only [sub_zero] using
          (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos (mul_pos hθ hR) 3)).mp hP.2.2.2)] with n hnlo hnhi hnV hnX
  refine ⟨hnlo, hnhi, ?_, ?_⟩
  · exact (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (mul_pos hθ (borelInnerRadius_pos R hR n))).mpr hnV
  · rw [borelInnerCentre_relativePosition]
    exact (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (pow_pos (mul_pos hθ (borelInnerRadius_pos R hR n)) 3)).mpr
      (by simpa only [sub_zero] using hnX)

/-- Every interior point has a compactly contained cylinder with a fixed spatial margin. -/
theorem exists_inner_margin_cylinder  {D : Set (KineticPoint d)}
    (hD : IsOpen D) {P : KineticPoint d} (hP : P ∈ D) :
    ∃ (P₁ : KineticPoint d) (r : ℝ), 0 < r ∧
      closure (backwardCylinder P₁ r) ⊆ D ∧ P ∈ backwardCylinder P₁ (3 * r / 4) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hD P hP
  obtain ⟨r₀, hr₀, hsmall⟩ := centeredCylinder_subset_ball P (half_pos hε)
  let r := r₀ / 2
  have hr : 0 < r := half_pos hr₀
  have hsub : closure (centeredCylinder P r) ⊆ Metric.closedBall P (ε / 2) :=
    closure_minimal ((hsmall r hr (by dsimp [r]; linarith)).trans
      Metric.ball_subset_closedBall) Metric.isClosed_closedBall
  refine ⟨centeredTop P r, r, hr, hsub.trans (fun Q hQ => hball
    (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hQ).trans_lt (by linarith)))), ?_⟩
  have hr2  := sq_pos_of_pos hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · change P.time + r ^ 2 / 2 - (3 * r / 4) ^ 2 < P.time
    nlinarith only [hr2]
  · change P.time < P.time + r ^ 2 / 2
    linarith
  · exact PDE.center_mem_euclideanBall P.velocity (by positivity)
  · rw [relativePosition_centeredTop]
    simp only [relativePosition_self]
    exact PDE.center_mem_euclideanBall 0 (pow_pos (by positivity) 3)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
