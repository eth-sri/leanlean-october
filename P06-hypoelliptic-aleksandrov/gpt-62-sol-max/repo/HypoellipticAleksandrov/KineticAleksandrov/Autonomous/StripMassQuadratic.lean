module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimits
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassComparison
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelCutoffSequence

/-! # Quadratic mass by interior smooth exhaustion and bounded comparison -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo TheoremA Evolution Occupation
open scoped Topology ENNReal

/-- Bounds on compact interior sources pass to nonnegative smooth profiles by monotone exhaustion. -/
theorem stripGreen_lintegral_le_of_compact_sources
    (H : Interval) (E : StripEvolution H) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (k : Point → ℝ) (K : ℝ) (hk : ContDiff ℝ (⊤ : ℕ∞) (rawLift k)) (hkn : ∀ p, 0 ≤ k p)
    (hcmp : ∀ g : Point → ℝ, (∀ p, 0 ≤ g p) → (∀ p, g p ≤ k p) →
      ContDiff ℝ (⊤ : ℕ∞) (rawLift g) → HasCompactSupport g →
      tsupport g ⊆ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T →
      sectionTwoPoint e.1 ∈ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T →
      duhamelPotential E.2 T g (sectionTwoPoint e.1) ≤ K) :
    ∫⁻ p, ENNReal.ofReal (k (sectionTwoPoint p)) ∂stripGreenOfKernel H E.2 T e ≤ ENNReal.ofReal K := by
  classical
  have hkcont : Continuous k := hk.continuous.comp
    (KineticPoint.homeomorphProd 1).continuous
  let D := evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T
  let U := (KineticPoint.equivProd 1).symm ⁻¹' D
  have hD : IsOpen D := isOpen_duhamelCylinder
    (γ := fun _ => 0) (isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible H))
    continuous_const T
  have hU : IsOpen U := hD.preimage (KineticPoint.homeomorphProd 1).symm.continuous
  obtain ⟨χ, hχ, hb, hmono, hcover⟩ := exists_increasing_smooth_interior_cutoffs hU
  let g (n : ℕ) (p : Point) : ℝ :=
    χ n (KineticPoint.equivProd 1 p) * k p
  have hgc (n : ℕ) : HasCompactSupport (g n) :=
    ((hχ n).2.1.comp_homeomorph (KineticPoint.homeomorphProd 1)).mul_right
  have hgs (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (rawLift (g n)) :=
    (hχ n).1.mul hk
  have hgcont (n : ℕ) : Continuous (g n) :=
    ((hχ n).1.continuous.comp (KineticPoint.homeomorphProd 1).continuous).mul
      hkcont
  have hgn (n : ℕ) (p : Point) : 0 ≤ g n p := mul_nonneg (hb n _).1 (hkn _)
  have hgD (n : ℕ) : tsupport (g n) ⊆ D := by
    intro p hp
    have hx := tsupport_mul_subset_left hp
    have hy := (tsupport_comp_subset_preimage (χ n)
      (KineticPoint.homeomorphProd 1).continuous) hx
    have hu := (hχ n).2.2 hy
    change (KineticPoint.equivProd 1).symm (KineticPoint.equivProd 1 p) ∈ D at hu
    simpa only [Equiv.symm_apply_apply] using hu
  have hgb (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p, |g n p| ≤ C := by
    obtain ⟨B, hB⟩ := (hgcont n).bounded_above_of_compact_support (hgc n)
    refine ⟨max B 0, le_max_right _ _, fun p => ?_⟩
    have hh : |g n p| ≤ B := by simpa only [Real.norm_eq_abs] using hB p
    exact hh.trans (le_max_left _ _)
  let F (n : ℕ) : BoundedBorel Point :=
    ⟨g n ∘ sectionTwoPoint,
      (hgcont n).measurable.comp (continuous_sectionTwoPoint 1).measurable, by
        obtain ⟨C, hC, hh⟩ := hgb n
        exact ⟨C, hC, fun p => hh (sectionTwoPoint p)⟩⟩
  have hle (n : ℕ) (p : Point) : g n p ≤ k p := mul_le_of_le_one_left (hkn p) (hb n _).2
  have heT : e.1.time < T := WithTop.coe_lt_coe.mp e.2.1
  have heD : sectionTwoPoint e.1 ∈ D := ⟨heT, (stripPoleState H T e).2.1⟩
  have hbound (n : ℕ) : stripPotentialOfKernel H E.2 T (F n) e ≤ K := by
    have hpot := duhamelPotential_eq_greenMeasure E.2 (intervalDomain_measurable H)
      continuous_const T (g n) (hgn n) (hgcont n) (hgc n)
      e.1.time heT (stripPoleState H T e)
    have heq : stripPotentialOfKernel H E.2 T (F n) e =
        duhamelPotential E.2 T (g n) (sectionTwoPoint e.1) := by
      rw [stripPotentialOfKernel, stripGreenOfKernel,
        integral_map (measurable_elapsedPhysicalPoint _ _).aemeasurable (F n).measurable.aestronglyMeasurable]
      exact hpot.symm
    rw [heq]
    exact hcmp (g n) (hgn n) (hle n) (hgs n) (hgc n) (hgD n) heD
  have hfun : (fun p => ENNReal.ofReal (k (sectionTwoPoint p))) =ᵐ[
      stripGreenOfKernel H E.2 T e] fun p => ⨆ n, ENNReal.ofReal (F n p) := by
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e] with p hp
    have hnp : sectionTwoPoint p ∈ D := by
      refine ⟨hp.1, ?_⟩
      apply PDE.mem_translateSet_iff_sub_mem.mpr
      simpa only [sub_zero, intervalDomain, PDE.mem_oneDimensionalAxisBox_iff,
        PDE.vecOneCoordinate, sectionTwoPoint, Interval.carrier] using hp.2
    have hnU : KineticPoint.equivProd 1 (sectionTwoPoint p) ∈ U := by
      simpa only [U, mem_preimage, Equiv.symm_apply_apply] using hnp
    obtain ⟨N, hN⟩ := hcover _ hnU
    apply le_antisymm
    · apply le_iSup_of_le N
      change ENNReal.ofReal (k (sectionTwoPoint p)) ≤
        ENNReal.ofReal (χ N (KineticPoint.equivProd 1 (sectionTwoPoint p)) *
          k (sectionTwoPoint p))
      rw [hN N le_rfl, one_mul]
    · apply iSup_le
      intro n
      exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (hkn _) (hb n _).2)
  rw [lintegral_congr_ae hfun, lintegral_iSup]
  · apply iSup_le
    intro n
    have hi := stripGreen_integrable_boundedBorel H E.2 T e (F n)
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall (fun p => hgn n (sectionTwoPoint p)))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  · intro n
    exact (F n).measurable.ennreal_ofReal
  · intro i j hij p
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hmono _ hij) (hkn _))

section
variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (H : Interval)

/-- Finite-horizon quadratic mass follows from actual compact interior sources by exhaustion. -/
theorem stripGreenOfRealization_quadratic_mass (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    stripGreenOfKernel H E.2 T e univ ≤
      ENNReal.ofReal ((e.1.velocity 0 - H.lo) * (H.hi - e.1.velocity 0) / (2 * lam)) := by
  have h := stripGreen_lintegral_le_of_compact_sources H E T e (fun _ => 1)
    (stripQuadraticBarrier H lam (sectionTwoPoint e.1)) contDiff_const (fun _ => zero_le_one)
    (fun g hg0 hg1 hs hc hD he => strip_duhamel_le_quadratic A H E hE T g hg0 hg1 hs hc hD _ he)
  simpa only [ENNReal.ofReal_one, lintegral_const, one_mul, stripQuadraticBarrier_eq, sectionTwoPoint] using h

/-- The canonical autonomous measure obeys the exact finite-horizon quadratic bound. -/
theorem stripGreen_finite_quadratic_mass (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) :
    stripGreen A H T e univ ≤
      ENNReal.ofReal ((e.1.velocity 0 - H.lo) * (H.hi - e.1.velocity 0) / (2 * lam)) :=
  stripGreenOfRealization_quadratic_mass A H _
    (stripEvolution_spec A H) T e

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
