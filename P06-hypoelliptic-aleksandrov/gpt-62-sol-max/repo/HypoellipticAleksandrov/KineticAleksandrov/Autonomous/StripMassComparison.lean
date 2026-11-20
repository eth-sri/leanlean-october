module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PackedSliceRegularity

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripDuhamel

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassQuadraticCalculus

/-! # Quadratic comparison for compact interior source potentials -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo Evolution Occupation
open scoped Topology

/-- Closing the native interval gives precisely the scalar endpoint inequalities. -/
theorem intervalDomain_closure_bounds (H : Interval) {v : PDE.Vec 1}
    (hv : v ∈ closure (intervalDomain H)) : H.lo ≤ v 0 ∧ v 0 ≤ H.hi := by
  constructor
  · exact closure_minimal (fun y hy =>
      (PDE.mem_oneDimensionalAxisBox_iff.mp hy).1.le)
      (isClosed_le continuous_const (continuous_apply 0)) hv
  · exact closure_minimal (fun y hy =>
      (PDE.mem_oneDimensionalAxisBox_iff.mp hy).2.le)
      (isClosed_le (continuous_apply 0) continuous_const) hv

/-- The literal interval barrier is continuous on spacetime. -/
theorem stripQuadraticBarrier_continuous (H : Interval) (lam : ℝ) :
    Continuous (stripQuadraticBarrier H lam) := by
  have heq : stripQuadraticBarrier H lam = fun p =>
      (p.position 0 - H.lo) * (H.hi - p.position 0) / (2 * lam) :=
    funext (stripQuadraticBarrier_eq H lam)
  rw [heq]
  have hv : Continuous (fun p : Point => p.position 0) :=
    (continuous_apply 0).comp continuous_position
  exact ((hv.sub continuous_const).mul (continuous_const.sub hv)).div_const _

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
  (hE : IsStripEvolution A H E) (T : ℝ)
include Lam A hE

/-- The exact `1/(2 lambda)` barrier bounds each nonnegative compact interior unit source. -/
theorem strip_duhamel_le_quadratic (g : Point → ℝ)
    (hgn : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1)
    (hgs : ContDiff ℝ (⊤ : ℕ∞) (rawLift g)) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T)
    (p₀ : Point) (hp₀ : p₀ ∈ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T) :
    duhamelPotential E.2 T g p₀ ≤ stripQuadraticBarrier H lam p₀ := by
  refine autonomous_duhamel_le_barrier A (intervalDomain_admissible H) E hE T g (stripQuadraticBarrier H lam)
    hgn hgs hgc hgU (stripQuadraticBarrier_continuous H lam) (fun p _ => stripQuadraticBarrier_regular H lam p)
    ?_ ?_ p₀ hp₀
  · intro p hp
    apply stripQuadraticBarrier_nonneg H A.positive p
    apply intervalDomain_closure_bounds H
    simpa only [mem_closure_movingDomain_iff, sub_zero] using hp.2
  · intro p _
    rw [stripQuadraticBarrier_operator, neg_div]
    have hb := (A.bounds (p.velocity 0) (p.position 0)).1
    have hv : 1 ≤ A.a (p.velocity 0) (p.position 0) / lam :=
      (le_div_iff₀ A.positive).2 (by simpa using hb)
    linarith [hg1 p]

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
