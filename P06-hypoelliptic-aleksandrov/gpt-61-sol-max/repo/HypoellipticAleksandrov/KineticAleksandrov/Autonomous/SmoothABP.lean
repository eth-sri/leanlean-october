module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothABPPotentials
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstract

/-! # The forward autonomous ABP estimate conditional on improved cylinder density -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open scoped MatrixOrder Matrix.Norms.Elementwise

/-- The source conjugate exponent is involutive and has the required scaling power. -/
theorem autonomous_conjugate_identities (p : ℝ) (hp : 1 < p) :
    (p / (p - 1)) / (p / (p - 1) - 1) = p ∧
      6 / (p / (p - 1)) - 4 = 2 - 6 / p := by


  have hq : p / (p - 1) - 1 ≠ 0 := by
    have : 1 < p / (p - 1) := (one_lt_div (sub_pos.mpr hp)).mpr (by linarith)
    exact sub_ne_zero.mpr this.ne'
  constructor <;> field_simp [(ne_of_gt (lt_trans zero_lt_one hp)), (sub_ne_zero.mpr hp.ne'), hq] <;> ring

/-- The uniform smooth forward estimate uses no additional analytic hypothesis beyond
the exact improved density statement. -/
theorem forward_autonomous_abp_of_below_four_density
    (hdensity : BelowFourDensityStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (p : ℝ)
    (hp : criticalP ⟨Lam / lam, (le_div_iff₀ hlam).2
      (by simpa)⟩ < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (Z₀ : Point) (R : ℝ) (hR : 0 < R) (u g : Point → ℝ),
      ContinuousOn u (closure (forwardCylinder Z₀ R hR)) →
      IsKineticC112On u (forwardCylinder Z₀ R hR) →
      (∀ P ∈ forwardCylinder Z₀ R hR, 0 ≤ g P) →
      MemLp g (ENNReal.ofReal p) (volume.restrict (forwardCylinder Z₀ R hR)) →
      (∀ᵐ P ∂volume.restrict (forwardCylinder Z₀ R hR),
        -g P ≤ forwardScalarOperator A.a u P) →
      ∀ P ∈ closure (forwardCylinder Z₀ R hR), u P ≤
        sSup ((fun P => max (u P) 0) '' exitBoundary Z₀ R hR) +
          C * R ^ (2 - 6 / p) *
            (eLpNorm ({P | 0 < u P}.indicator g) (ENNReal.ofReal p)
              (volume.restrict (forwardCylinder Z₀ R hR))).toReal := by
  obtain ⟨alpha, ha, ha1, -, hq, hqa⟩ := exists_autonomous_exponents lam Lam hlam hLam p hp
  obtain ⟨C, hC, hden⟩ := hdensity hH hLE lam Lam hlam hLam alpha (p / (p - 1))
    ⟨ha, ha1⟩ ⟨hq, hqa⟩
  have hcritical := (criticalP_bounds ⟨Lam / lam, (le_div_iff₀ hlam).2
    (by simpa)⟩).1

  have hid := autonomous_conjugate_identities p (by linarith only [hcritical, hp])
  refine ⟨C, hC, ?_⟩
  intro A Z₀ R hR u g hcont hreg hg0 hLp hsub





  have hb := kinetic_abp_abstract_of_continuous Z₀ R hR (autonomousCoefficient A.a)
    (by
        apply continuousOn_pi.mpr
        intro i
        apply continuousOn_pi.mpr
        intro j
        exact (A.smooth.continuous.comp
          (((continuous_apply 0).comp continuous_position).prodMk
            ((continuous_apply 0).comp continuous_velocity))).continuousOn) (by
        intro P _
        have heq : autonomousCoefficient A.a P.time P.position P.velocity =
            A.a (P.position 0) (P.velocity 0) • (1 : PDE.Mat 1) := by
          ext i j
          fin_cases i
          fin_cases j
          simp [autonomousCoefficient]
        rw [heq]
        exact Matrix.PosSemidef.smul Matrix.PosSemidef.one
          (hlam.le.trans (A.bounds _ _).1)) (p / (p - 1)) hq (C * R ^ (2 - 6 / p))
    (mul_pos hC (Real.rpow_pos_of_pos hR _))
    (autonomousCylinderGreen hH hLE hlam hLam A Z₀ R hR)
    (autonomous_cylinder_green_potentials hH hLE hlam hLam A Z₀ R hR)
    (by
        intro P hP
        obtain ⟨G, hG, hG0, heq, hGLp, hGN⟩ := hden A Z₀ R hR P hP
        rw [hid.2] at hGN
        refine ⟨G, hG, hG0, ?_, hGN, hGLp⟩
        simp only [autonomousCylinderGreen, dite_eq_left hP]
        exact heq) u g hcont hreg hg0 (by rwa [hid.1]) (by
        simpa only [forwardOperator_autonomous] using hsub)
  simpa only [hid.1] using hb

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
