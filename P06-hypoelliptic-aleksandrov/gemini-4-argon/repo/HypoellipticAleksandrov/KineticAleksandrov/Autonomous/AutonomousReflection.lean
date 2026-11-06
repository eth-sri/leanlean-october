module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothABP
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateReflection
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothABPPotentials
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstract
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CriticalP
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.UniversalBarrierParameters
import Mathlib.Tactic

/-! # Reflection of the conditional smooth autonomous estimate -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic TheoremA

/- The backward smooth estimate retains the positive-set source and the same constant. -/
theorem autonomous_smooth_localised_of_below_four_density
    (hdensity : BelowFourDensityStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (p )
    (hp : criticalP ⟨Lam / lam, (le_div_iff₀ hlam).2
      (by simpa only [one_mul] using hLam)⟩ < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (P₀ : Point) (R : ℝ), 0 < R → ∀ (u f : Point → ℝ),
      ContinuousOn u (closure (backwardCylinder P₀ R)) →
      IsKineticC112On u (backwardCylinder P₀ R) →
      MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) →
      (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
        autonomousScalarOperator A.a u P ≤ f P) →
      ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
        sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
          C * R ^ (2 - 6 / p) *
            (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0))
              (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R))).toReal := by
  obtain ⟨C, hC, hforward⟩ : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
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
    obtain ⟨alpha, ha, ha1, -, hq, hqa⟩ : ∃ alpha : ℝ,
      bellmanAdjointExponent (Lam / lam) ((le_div_iff₀ hlam).2
        (by simpa only [one_mul] using hLam)) - 2 < alpha ∧
      alpha < 1 ∧ alpha < p - 3 ∧
      1 < p / (p - 1) ∧ p / (p - 1) < (4 - (1 - alpha)) / (3 - (1 - alpha)) := by
      let ratio : {r : ℝ // 1 ≤ r} :=
        ⟨Lam / lam, (le_div_iff₀ hlam).2 (by simpa only [one_mul] using hLam)⟩
      have hb := bellmanAdjointExponent_range ratio.1 ratio.2
      have hp' : 1 + bellmanAdjointExponent ratio.1 ratio.2 < p := hp
      have hinterval : bellmanAdjointExponent ratio.1 ratio.2 - 2 < min 1 (p - 3) :=
        lt_min (by linarith only [hb.2]) (by linarith only [hp'])
      obtain ⟨alpha, ha, hupper⟩ := exists_between hinterval
      have ha1 := (lt_min_iff.mp hupper).1
      have hap := (lt_min_iff.mp hupper).2
      have hapos : 0 < alpha := by linarith only [hb.1, ha]
      have hpm : 0 < p - 1 := by linarith only [hb.1, hp']
      have hden : 0 < 3 - (1 - alpha) := by linarith only [hapos]
      refine ⟨alpha, ha, ha1, hap, ?_, ?_⟩
      · exact (one_lt_div hpm).2 (by linarith)
      · apply (div_lt_div_iff₀ hpm hden).2
        nlinarith only [hap]
    obtain ⟨C, hC, hden⟩ := hdensity hH hLE lam Lam hlam hLam alpha (p / (p - 1))
      ⟨ha, ha1⟩ ⟨hq, hqa⟩
    have hcritical := (criticalP_bounds ⟨Lam / lam, (le_div_iff₀ hlam).2
      (by simpa only [one_mul] using hLam)⟩).1
    have hp1 : 1 < p := by linarith only [hcritical, hp]
    have hid : (p / (p - 1)) / (p / (p - 1) - 1) = p ∧
        6 / (p / (p - 1)) - 4 = 2 - 6 / p := by
        have hp0 := ne_of_gt (lt_trans zero_lt_one hp1)
        have hpm : p - 1 ≠ 0 := sub_ne_zero.mpr hp1.ne'
        have hq : p / (p - 1) - 1 ≠ 0 := by
          have : 1 < p / (p - 1) := (one_lt_div (sub_pos.mpr hp1)).mpr (by linarith)
          exact sub_ne_zero.mpr this.ne'
        constructor <;> field_simp [hp0, hpm, hq] <;> ring

      /- The uniform smooth forward estimate uses no additional analytic hypothesis beyond
      the exact improved density statement. -/
    refine ⟨C, hC, ?_⟩
    intro A Z₀ R hR u g hcont hreg hg0 hLp hsub
    have hAc : ContinuousOn (fun P : Point =>
        autonomousCoefficient A.a P.time P.position P.velocity) (forwardCylinder Z₀ R hR) := by
      apply continuousOn_pi.mpr
      intro i
      apply continuousOn_pi.mpr
      intro j
      exact (A.smooth.continuous.comp
        (((continuous_apply 0).comp continuous_position).prodMk
          ((continuous_apply 0).comp continuous_velocity))).continuousOn
    have hpos : ∀ P ∈ forwardCylinder Z₀ R hR,
        (autonomousCoefficient A.a P.time P.position P.velocity).PosSemidef := by
      intro P _
      have heq : autonomousCoefficient A.a P.time P.position P.velocity =
          A.a (P.position 0) (P.velocity 0) • (1 : PDE.Mat 1) := by
        ext i j
        fin_cases i
        fin_cases j
        simp [autonomousCoefficient]
      rw [heq]
      exact Matrix.PosSemidef.smul Matrix.PosSemidef.one
        (hlam.le.trans (A.bounds _ _).1)
    have hden' : ∀ P ∈ forwardCylinder Z₀ R hR, ∃ G : Point → ℝ,
        Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        autonomousCylinderGreen hH hLE hlam hLam A Z₀ R hR P =
          (volume.restrict (forwardCylinder Z₀ R hR)).withDensity
            (fun z => ENNReal.ofReal (G z)) ∧
        (eLpNorm G (ENNReal.ofReal (p / (p - 1)))
          (volume.restrict (forwardCylinder Z₀ R hR))).toReal ≤ C * R ^ (2 - 6 / p) ∧
        MemLp G (ENNReal.ofReal (p / (p - 1)))
          (volume.restrict (forwardCylinder Z₀ R hR)) := by
      intro P hP
      obtain ⟨G, hG, hG0, heq, hGLp, hGN⟩ := hden A Z₀ R hR P hP
      rw [hid.2] at hGN
      refine ⟨G, hG, hG0, ?_, hGN, hGLp⟩
      simp only [autonomousCylinderGreen, dite_eq_left hP]
      exact heq
    have hs : ∀ᵐ P ∂volume.restrict (forwardCylinder Z₀ R hR),
        -g P ≤ forwardKineticOperator (autonomousCoefficient A.a) u P := by
      simpa only [forwardOperator_autonomous] using hsub
    have hl : MemLp g (ENNReal.ofReal ((p / (p - 1)) / (p / (p - 1) - 1)))
        (volume.restrict (forwardCylinder Z₀ R hR)) := by rwa [hid.1]
    have hb := kinetic_abp_abstract_of_continuous Z₀ R hR (autonomousCoefficient A.a)
      hAc hpos (p / (p - 1)) hq (C * R ^ (2 - 6 / p))
      (mul_pos hC (Real.rpow_pos_of_pos hR _))
      (autonomousCylinderGreen hH hLE hlam hLam A Z₀ R hR)
      (autonomous_cylinder_green_potentials hH hLE hlam hLam A Z₀ R hR)
      hden' u g hcont hreg hg0 hl hs
    simpa only [hid.1] using hb
  refine ⟨C, hC, ?_⟩
  intro A P₀ R hR u f hcont hreg hLp hsub P hP
  let B : SmoothAutonomous lam Lam :=
    ⟨reflectedAutonomous A.a, reflectedAutonomous_smooth A, reflectedAutonomous_bounds A⟩
  let Z₀ := kineticReflection P₀
  let Q := forwardCylinder Z₀ R hR
  let U := u ∘ kineticReflection
  let g := (fun P => max (f P) 0) ∘ kineticReflection
  have hmp := measurePreserving_reflection_forward P₀ R hR
  have hUc : ContinuousOn U (closure Q) := by
    have hc := hcont.comp (continuous_kineticReflection 1).continuousOn
      (fun x hx => hx : MapsTo kineticReflection
        (kineticReflection ⁻¹' closure (backwardCylinder P₀ R)) _)
    simpa only [preimage_closure_backwardCylinder_reflection P₀ R hR] using hc
  have hUr : IsKineticC112On U Q := by
    simpa only [preimage_backwardCylinder_reflection P₀ R hR] using
      isKineticC112On_kineticReflection u (backwardCylinder P₀ R) hreg
  have hgLp :=
    hLp.comp_measurePreserving hmp
  have hUs : ∀ᵐ P ∂volume.restrict Q, -g P ≤ forwardScalarOperator B.a U P := by
    filter_upwards [hmp.quasiMeasurePreserving.ae hsub] with P hP
    rw [autonomousScalarOperator_reflection]
    exact neg_le_neg (hP.trans (le_max_left _ _))
  have hbound := hforward B Z₀ R hR U g hUc hUr (fun _ _ => le_max_right _ _) hgLp hUs
  have hPr : kineticReflection P ∈ closure Q := by
    rw [← preimage_closure_backwardCylinder_reflection P₀ R hR]
    change kineticReflection (kineticReflection P) ∈ closure (backwardCylinder P₀ R)
    rw [kineticReflection_involutive P]
    exact hP
  have hresult := hbound (kineticReflection P) hPr
  have hnorm : eLpNorm ({P | 0 < U P}.indicator g) (ENNReal.ofReal p)
      (volume.restrict Q) =
      eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) := by
    have hL := borelSource_memLp (isOpen_backwardCylinder P₀ R hR) true u f
      hreg.continuousOn hLp
    change MemLp ({P | 0 < u P}.indicator (fun P => max (f P) 0)) _ _ at hL
    have hfun : {P | 0 < U P}.indicator g =
        ({P | 0 < u P}.indicator (fun P => max (f P) 0)) ∘ kineticReflection := rfl
    rw [hfun]
    exact eLpNorm_comp_measurePreserving hL.aestronglyMeasurable hmp
  rw [hnorm, boundarySup_reflection P₀ R hR u] at hresult
  simpa only [U, Function.comp_apply, kineticReflection_involutive P] using hresult

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
