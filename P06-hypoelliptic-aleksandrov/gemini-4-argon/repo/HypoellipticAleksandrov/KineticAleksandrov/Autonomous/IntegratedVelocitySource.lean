module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocityComparison
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocityProfile
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsKernel

/-! # Actual compact convex-profile source tests -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory
open SectionTwo

/- Positive forcing density supplied by the convex velocity profile. -/
def velocityOccupationDensity (r v : ℝ) : ℝ :=
  r ^ 2 / Real.sqrt (r ^ 2 + v ^ 2) ^ 3

/- The convex forcing density is smooth. -/
theorem velocityOccupationDensity_contDiff {r } (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (velocityOccupationDensity r) := by
  apply contDiff_const.div
    (((contDiff_const.add (contDiff_id.pow 2)).sqrt
      (fun v => ne_of_gt (by nlinarith [sq_pos_of_pos hr, sq_nonneg v]))).pow 3)
  intro v
  exact pow_ne_zero _ (ne_of_gt (Real.sqrt_pos.2
    (by nlinarith [sq_pos_of_pos hr, sq_nonneg v])))

/- The forcing density is nonnegative everywhere. -/
theorem velocityOccupationDensity_nonneg (r v : ℝ) : 0 ≤ velocityOccupationDensity r v := by
  unfold velocityOccupationDensity
  positivity

/- A smooth compact unit probe multiplied by the density is a valid compact source. -/
theorem velocity_profile_source_bound (hH : HormanderHypoellipticityStatement)
    {lam Lam r } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (hr : 0 < r) (T )
    (f : ℝ × EvolutionAmbientState 1 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ {q | q.1 < T})
    (hf01 : ∀ q, 0 ≤ f q ∧ f q ≤ 1) (p : Point) (hp : p.time < T) :
    duhamelPotential E.2 T
      (fun q => f (q.time, q.position, q.velocity) *
        (lam * velocityOccupationDensity r (q.position 0))) p ≤
      Real.sqrt (2 * Lam * (T - p.time)) := by
  let g := fun q : Point => f (q.time, q.position, q.velocity) *
    (lam * velocityOccupationDensity r (q.position 0))
  have hgs : ContDiff ℝ (⊤ : ℕ∞) (rawLift g) := by
    exact hf.mul (contDiff_const.mul ((velocityOccupationDensity_contDiff hr).comp
      ((contDiff_apply ℝ ℝ 0).comp contDiff_snd.fst)))
  have hc : HasCompactSupport g :=
    (hfc.comp_homeomorph (KineticPoint.homeomorphProd 1)).mul_right
  have hu : tsupport g ⊆ evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T := by
    intro q hq
    have hqf := tsupport_mul_subset_left hq
    have hraw : (q.time, q.position, q.velocity) ∈ tsupport f := by
      exact tsupport_comp_subset_preimage f
        (KineticPoint.homeomorphProd 1).continuous hqf
    refine ⟨hfU hraw, ?_⟩
    change q.position ∈ movingDomain (wholeSpace 1) (fun _ => 0) q.time
    rw [movingDomain_wholeSpace]
    trivial
  have hLn := hlam.le.trans hLam
  have hpoint : p ∈ evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T := by
    refine ⟨hp, ?_⟩
    change p.position ∈ movingDomain (wholeSpace 1) (fun _ => 0) p.time
    rw [movingDomain_wholeSpace]
    trivial
  have _h_xinl_0 : Continuous (velocityOccupationBarrier r Lam T) := by
    unfold velocityOccupationBarrier velocityHeatProfile velocityConvexProfile
    apply Continuous.sub <;> apply Real.continuous_sqrt.comp <;>
      exact (continuous_const.add (continuous_const.mul
        (continuous_const.sub continuous_time))).add
          ((continuous_apply 0).comp continuous_position |>.pow 2)
  have hb := velocity_duhamel_le_barrier hH hlam hLam A E hE T g
    (velocityOccupationBarrier r Lam T)
    (fun q => mul_nonneg (hf01 _).1
      (mul_nonneg hlam.le (velocityOccupationDensity_nonneg r _))) hgs hc hu
    _h_xinl_0
    (velocityOccupationBarrier_regular hr hLn T)
    (fun q hq => (velocityOccupationBarrier_bounds hr hLn T q hq.1).1)
    (fun q hq => by
      have he : transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) (velocityOccupationBarrier r Lam T) q ≤ -lam * (r ^ 2 / Real.sqrt (r ^ 2 + (q.position 0) ^ 2) ^ 3) := by
        have hp := hq.1.le
        have hLam := (hlam.le.trans (A.bounds 0 0).1).trans (A.bounds 0 0).2
        have hR : 0 < r ^ 2 + 2 * Lam * (T - q.time) :=
          add_pos_of_pos_of_nonneg (sq_pos_of_pos hr)
            (mul_nonneg (mul_nonneg (by norm_num) hLam) (sub_nonneg.mpr hp))
        have h0 : 0 < r ^ 2 + 2 * 0 * (T - q.time) := by simpa using sq_pos_of_pos hr
        have he : velocityOccupationBarrier r Lam T =
            (fun q => (velocityHeatProfile (r ^ 2) Lam T ∘ terminalPhysicalPoint) q -
              (velocityHeatProfile (r ^ 2) 0 T ∘ terminalPhysicalPoint) q) := rfl
        rw [← viscousTransportedOperator_zero, he,
          viscousTransportedOperator_sub (velocityHeatProfile_native_regular _ _ _ q hR)
            (velocityHeatProfile_native_regular _ _ _ q h0),
          viscousTransportedOperator_zero, viscousTransportedOperator_zero,
          terminalPhysicalPoint_operator, terminalPhysicalPoint_operator,
          velocityHeatProfile_operator (terminalPhysicalPoint q) h0 A.a]
        have hh := velocityHeatProfile_operator_nonpos (terminalPhysicalPoint q) hR hLam
          A.a (A.bounds _ _).2
        have hl := (A.bounds (q.velocity 0) (q.position 0)).1
        have hd : 0 ≤ r ^ 2 / Real.sqrt (r ^ 2 + (q.position 0) ^ 2) ^ 3 := by positivity
        dsimp only [terminalPhysicalPoint] at hh ⊢
        simp only [mul_zero, zero_mul, add_zero, neg_zero, zero_div, zero_add]
        rw [mul_div_assoc]
        have hm := mul_le_mul_of_nonneg_right hl hd
        linarith
      have hm := mul_le_mul_of_nonneg_right (hf01 (q.time, q.position, q.velocity)).2
        (mul_nonneg hlam.le (velocityOccupationDensity_nonneg r (q.position 0)))
      change _ ≤ -(f _ * (lam * velocityOccupationDensity r (q.position 0)))
      change _ ≤ -lam * velocityOccupationDensity r (q.position 0) at he
      linarith) p hpoint
  exact hb.trans (velocityOccupationBarrier_bounds hr hLn T p hp.le).2

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
