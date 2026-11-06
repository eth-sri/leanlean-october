module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundaryFunctionalComparison
public import PDEFoundation.Calculus.RegularityOrder


/-! # Trace order for the actual smooth boundary solution values -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open SectionTwo TheoremA

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

variable (a T : ℝ)

/-- The literal boundary solution is bounded on its full closed strip. -/
theorem ballBoundarySolution_bounded
     (_haT : a < T) (φ : HypoellipticAleksandrov.KineticScalarField d)
    (hφ : ContDiff ℝ PDE.smoothOrder (φ ∘ (KineticPoint.equivProd d).symm))
    (hc : HasCompactSupport φ) :
    ∃ M : ℝ, ∀ P ∈ localClosedStrip a T v₀ R,
      |ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR a T φ P| ≤ M := by
  let F := forwardKineticOperator (ofTimeVelocityCoefficient B) φ
  obtain ⟨hFc, M, hM, hFb⟩ := boundary_probe_operator_bounded B hB φ hφ hc
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous (boundary_probe_continuous φ hφ)
  have hgb := (boundedBallSource_extension a T M v₀ R hM F hFc.measurable
    (fun P _ => hFb P)).2
  refine ⟨C + (T - a) * M, ?_⟩
  intro P hP
  have hw := abs_duhamelPotential_le (localBallKernel hH hLE hd hlam hLam B hB v₀ hR)
    _ M hM hgb (sectionTwoPoint P) T hP.2.1

  change |φ P + ballSourcePotential hH hLE hd hlam hLam B hB v₀ hR a T F P| ≤ _
  exact (abs_add_le _ _).trans (add_le_add (hC P) (hw.trans (mul_le_mul_of_nonneg_right (sub_le_sub_left hP.1 T) hM)))

/-- Boundary order controls the actual solution at every closed-strip point. -/
theorem ballBoundarySolution_le_of_trace
     (haT : a < T) (φ : HypoellipticAleksandrov.KineticScalarField d)
    (hφ : ContDiff ℝ PDE.smoothOrder (φ ∘ (KineticPoint.equivProd d).symm))
    (hc : HasCompactSupport φ) (c : ℝ)
    (htrace : ∀ P ∈ localTrace a T v₀ R, φ P ≤ c) :
    ∀ P ∈ localClosedStrip a T v₀ R,
      ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR a T φ P ≤ c := by
  obtain ⟨hsm, he, hcont, htr⟩ :=
    ballBoundarySolution_smooth_traces hH hLE hd hlam hLam B hB v₀ hR a T haT φ hφ hc
  exact bounded_homogeneous_trace_comparison B hB a T haT v₀ R _ hsm he hcont
    (ballBoundarySolution_bounded hH hLE hd hlam hLam B hB v₀ hR a T haT φ hφ hc)
    c (fun P hP => by rw [htr hP]; exact htrace P hP)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
