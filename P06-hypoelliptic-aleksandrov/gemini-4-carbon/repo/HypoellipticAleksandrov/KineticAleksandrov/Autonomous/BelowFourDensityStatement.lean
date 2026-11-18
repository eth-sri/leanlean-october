module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.DegreeGap
import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.UniversalBarrierParameters
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CapacityCylinder
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous

/-- The source threshold is one plus the characterized homogeneous adjoint exponent. -/
def criticalP (ratio : {r : ℝ // 1 ≤ r}) : ℝ :=
  1 + bellmanAdjointExponent ratio.1 ratio.2

/-- The source threshold lies in the half-open interval from three to four. -/
theorem criticalP_bounds (ratio : {r : ℝ // 1 ≤ r}) :
    3 ≤ criticalP ratio ∧ criticalP ratio < 4 := by
  obtain ⟨hl, hu⟩ := bellmanAdjointExponent_range ratio.1 ratio.2
  unfold criticalP
  constructor <;> linarith only [hl, hu]


/-- Choose the barrier degree before any coefficient, cylinder, or solution data. -/
theorem exists_autonomous_exponents (lam Lam : ℝ) (hlam : 0 < lam)
    (hLam : lam ≤ Lam) (p : ℝ)
    (hp : criticalP ⟨Lam / lam, (le_div_iff₀ hlam).2
      (by simpa only [one_mul] using hLam)⟩ < p) :
    ∃ alpha : ℝ,
      bellmanAdjointExponent (Lam / lam) ((le_div_iff₀ hlam).2
        (by simpa only [one_mul] using hLam)) - 2 < alpha ∧
      alpha < 1 ∧ alpha < p - 3 ∧
      1 < p / (p - 1) ∧ p / (p - 1) < (4 - (1 - alpha)) / (3 - (1 - alpha)) := by
  let ratio : {r : ℝ // 1 ≤ r} :=
    ⟨Lam / lam, (le_div_iff₀ hlam).2 (by simpa using hLam)⟩
  have hb := bellmanAdjointExponent_range ratio.1 ratio.2
  have hp' : 1 + bellmanAdjointExponent ratio.1 ratio.2 < p := hp
  have hinterval : bellmanAdjointExponent ratio.1 ratio.2 - 2 < min 1 (p - 3) :=
    lt_min (by linarith only [hb.2]) (by linarith only [hp'])
  obtain ⟨alpha, ha, hupper⟩ := exists_between hinterval
  have hap := (lt_min_iff.mp hupper).2
  have hapos : 0 < alpha := by linarith only [hb.1, ha]
  have hpm : 0 < p - 1 := by linarith only [hb.1, hp']
  have hden : 0 < 3 - (1 - alpha) := by linarith only [hapos]
  refine ⟨alpha, ha, ((lt_min_iff.mp hupper).1), hap, ?_, ?_⟩
  · exact (one_lt_div hpm).2 (by linarith)
  · apply (div_lt_div_iff₀ hpm hden).2
    nlinarith only [hap]

open Set MeasureTheory

/-- The source's improved density assertion for the canonical strip Green measure. -/
def BelowFourDensityStatement : Prop :=
  ∀ (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (alpha q : ℝ),
    (bellmanAdjointExponent (Lam / lam) ((le_div_iff₀ hlam).2
      (by simpa only [one_mul] using hLam)) - 2 < alpha ∧ alpha < 1) →
    (1 < q ∧ q < (4 - (1 - alpha)) / (3 - (1 - alpha))) →
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (Z₀ : Point) (R : ℝ) (hR : 0 < R) (P : Point)
      (hP : P ∈ forwardCylinder Z₀ R hR),
      ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        (stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z₀ R hR)
          (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)).restrict
            (forwardCylinder Z₀ R hR) =
          (volume.restrict (forwardCylinder Z₀ R hR)).withDensity
            (fun z => ENNReal.ofReal (G z)) ∧
        MemLp G (ENNReal.ofReal q) (volume.restrict (forwardCylinder Z₀ R hR)) ∧
        (eLpNorm G (ENNReal.ofReal q)
          (volume.restrict (forwardCylinder Z₀ R hR))).toReal ≤ C * R ^ (6 / q - 4)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

