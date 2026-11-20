module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothABPPotentials
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstract

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.RestartTailStatement
import Mathlib.Tactic

/-! # From an autonomous Green density bound to a cylinder maximum principle -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open scoped MatrixOrder Matrix.Norms.Elementwise

abbrev SmoothForwardABP (lam Lam p C : ℝ) : Prop :=
  ∀ (A : SmoothAutonomous lam Lam)
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
          (volume.restrict (forwardCylinder Z₀ R hR))).toReal

/-- The source conjugate exponent is involutive and has the required scaling power. -/
theorem autonomous_conjugate_identities (p : ℝ) (hp : 1 < p) :
    (p / (p - 1)) / (p / (p - 1) - 1) = p ∧
      6 / (p / (p - 1)) - 4 = 2 - 6 / p := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hpm : p - 1 ≠ 0 := sub_ne_zero.mpr hp.ne'
  have hq : p / (p - 1) - 1 ≠ 0 := by
    have : 1 < p / (p - 1) := (one_lt_div (sub_pos.mpr hp)).mpr (by linarith)
    exact sub_ne_zero.mpr this.ne'
  constructor <;> field_simp [hp0, hpm, hq] <;> ring

/-- A density bound for the canonical autonomous cylinder Green measure yields the smooth ABP bound. -/
theorem forward_autonomous_abp_of_density_bound
    {lam Lam : ℝ} (hlam : 0 < lam) (A : SmoothAutonomous lam Lam)
    (Z₀ : Point) (R : ℝ) (hR : 0 < R) {p K : ℝ} (hp : 1 < p) (hK : 0 < K)
    (hden : ∀ P ∈ forwardCylinder Z₀ R hR,
      enlargedDensityBound (autonomousCylinderGreen A Z₀ R hR P) (forwardCylinder Z₀ R hR) (p / (p - 1)) K)
    (u g : Point → ℝ) (hcont : ContinuousOn u (closure (forwardCylinder Z₀ R hR)))
    (hreg : IsKineticC112On u (forwardCylinder Z₀ R hR)) (hg0 : ∀ P ∈ forwardCylinder Z₀ R hR, 0 ≤ g P)
    (hLp : MemLp g (ENNReal.ofReal p) (volume.restrict (forwardCylinder Z₀ R hR)))
    (hsub : ∀ᵐ P ∂volume.restrict (forwardCylinder Z₀ R hR), -g P ≤ forwardScalarOperator A.a u P) :
    ∀ P ∈ closure (forwardCylinder Z₀ R hR), u P ≤
      sSup ((fun P => max (u P) 0) '' exitBoundary Z₀ R hR) +
        K * (eLpNorm ({P | 0 < u P}.indicator g) (ENNReal.ofReal p)
          (volume.restrict (forwardCylinder Z₀ R hR))).toReal := by
  have hq : 1 < p / (p - 1) := (one_lt_div (sub_pos.mpr hp)).2 (by linarith)
  have hid := (autonomous_conjugate_identities p hp).1
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
  have hs : ∀ᵐ P ∂volume.restrict (forwardCylinder Z₀ R hR),
      -g P ≤ forwardKineticOperator (autonomousCoefficient A.a) u P := by
    simpa only [forwardOperator_autonomous] using hsub
  have hl : MemLp g (ENNReal.ofReal ((p / (p - 1)) / (p / (p - 1) - 1)))
      (volume.restrict (forwardCylinder Z₀ R hR)) := by rwa [hid]
  simpa only [hid] using kinetic_abp_abstract_of_continuous Z₀ R hR (autonomousCoefficient A.a)
    hAc hpos (p / (p - 1)) hq K hK (autonomousCylinderGreen A Z₀ R hR)
    (autonomous_cylinder_green_potentials A Z₀ R hR)
    (fun P hP => by
      obtain ⟨G, ⟨hm, hn, he⟩, hG, hb⟩ := hden P hP
      exact ⟨G, hm, hn, he, hb, hG⟩) u g hcont hreg hg0 hl hs

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
