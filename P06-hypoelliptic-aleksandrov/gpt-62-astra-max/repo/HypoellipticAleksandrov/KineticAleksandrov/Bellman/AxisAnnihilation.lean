module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AxisAnnihilationTesting
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic

/-! # An axis-supported stationary compared Radon pair vanishes -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Filter
open scoped Topology

/-- Axis-supported stationarity and ellipticity force both measures to vanish on the punctured
plane. -/
theorem stationary_axis_pair_eq_zero (R : ℝ) (_hR : 1 ≤ R)
    (μ η : Measure BellmanPuncturedPlane) (hμ : IsBellmanRadon μ) (_hη : IsBellmanRadon η)
    (_hlo : μ ≤ η) (hhi : η ≤ ENNReal.ofReal R • μ)
    (heq : IsBellmanStationaryAdjointPair μ η)
    (haxis : μ {q | q.val.1 ≠ 0} = 0) : μ = 0 ∧ η = 0 := by
  let := hμ.1
  let := hμ.2
  have hηaxis := bellman_axis_support_comparison R μ η hhi haxis
  have hzero : μ = 0 := by
    apply Measure.support_eq_empty_iff.mp
    rw [eq_empty_iff_forall_notMem]
    intro q
    by_cases hqx : q.val.1 = 0
    · have hqv : q.val.2 ≠ 0 := by
        grind
      obtain ⟨χ, hsχ, hcχ, hχ, hrχ, hχq⟩ :=
        exists_contDiff_tsupport_subset (n := ⊤) ((isClosed_singleton.isOpen_compl).mem_nhds q.property)
      let w := fun p : ℝ × ℝ => p.2 ^ 2 * χ p
      have hw := (continuous_snd.pow 2).mul hχ.continuous
      have hcw : HasCompactSupport w := hcχ.mul_left
      have hsw : tsupport w ⊆ {p : ℝ × ℝ | p ≠ (0, 0)} :=
        tsupport_mul_subset_right.trans hsχ
      have hi : Integrable (fun p : BellmanPuncturedPlane => w p.val) μ :=
        (hw.comp continuous_subtype_val).integrable_of_hasCompactSupport (bellman_test_compact_subtype hcw hsw)
      have hn : ∀ᵐ p : BellmanPuncturedPlane ∂μ, 0 ≤ w p.val := by
        apply ae_of_all
        intro p
        exact mul_nonneg (sq_nonneg p.val.2) (hrχ ⟨p.val, rfl⟩).1
      have ha := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp (bellman_axis_velocity_test_zero μ η heq haxis hηaxis χ hχ hcχ hsχ)
      let U : Set BellmanPuncturedPlane := {p | w p.val ≠ 0}
      have hqU : q ∈ U := by
        grind
      have hμU : μ U = 0 := by
        exact ae_iff.mp ha
      exact Measure.notMem_support_iff_exists.mpr ⟨U, (isOpen_ne_fun (hw.comp continuous_subtype_val) continuous_const).mem_nhds hqU, hμU⟩
    · exact Measure.notMem_support_iff_exists.mpr
        ⟨{p | p.val.1 ≠ 0}, (isOpen_ne_fun (continuous_fst.comp continuous_subtype_val) continuous_const).mem_nhds hqx, haxis⟩
  simp_all <;> grind

end HypoellipticAleksandrov.KineticAleksandrov
