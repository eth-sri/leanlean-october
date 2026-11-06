module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationOffAxis
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AxisAnnihilation
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilation
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationReflectionStationary
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AxisAnnihilationJets
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AxisAnnihilationTesting
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureFubini
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Support

/-! # Exclusion of every admissible density degree at least three -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set
open Filter
open scoped Topology

/- Every degree of a genuine normalized stationary homogeneous Radon pair is below three. -/
theorem admissible_degree_lt_three (R ) (hR : 1 ≤ R) (β )
    (hβ : β ∈ bellmanAdmissibleDegrees R) : β < 3 := by
  by_contra hn
  have hge := le_of_not_gt hn
  obtain ⟨μ, η, hp⟩ := (mem_bellmanAdmissibleDegrees_iff R β).mp hβ
  have haxis : μ {q | q.val.1 ≠ 0} = 0 ∧ η {q | q.val.1 ≠ 0} = 0 := by
    have hpos := bellmanAdjointPair_positive_position_zero R β hR hge μ η hp
    have hneg := bellmanAdjointPair_positive_position_zero R β hR hge
      (Measure.map bellmanReflection μ) (Measure.map bellmanReflection η) hp.reflect
    have hm : MeasurableSet {q : BellmanPuncturedPlane | 0 < q.val.1} := by measurability
    rw [Measure.map_apply bellmanReflection.measurable hm,
      Measure.map_apply bellmanReflection.measurable hm] at hneg
    have he : bellmanReflection ⁻¹' {q : BellmanPuncturedPlane | 0 < q.val.1} =
        {q : BellmanPuncturedPlane | q.val.1 < 0} := by
      ext q
      change (0 < -q.val.1) ↔ q.val.1 < 0
      exact neg_pos
    rw [he] at hneg
    have hunion : {q : BellmanPuncturedPlane | q.val.1 ≠ 0} =
        {q | 0 < q.val.1} ∪ {q | q.val.1 < 0} := by
      ext q
      simp only [mem_ofPred_eq, mem_union]
      exact ⟨fun h => (lt_or_gt_of_ne h).symm, fun h => h.elim LT.lt.ne' LT.lt.ne⟩
    rw [hunion]
    exact ⟨measure_union_null hpos.1 hneg.1, measure_union_null hpos.2 hneg.2⟩
  have hlo : μ ≤ η := by
    simpa only [ENNReal.ofReal_one, one_smul] using hp.2.2.2.1
  obtain ⟨hμ, _⟩ : μ = 0 ∧ η = 0 := by
    have hμ := hp.1
    let _hη := hp.2.1
    have hhi := hp.2.2.2.2.1
    have heq := hp.2.2.2.2.2.1
    have haxis := haxis.1
    let : IsFiniteMeasureOnCompacts μ := hμ.1
    let : Measure.InnerRegular μ := hμ.2
    have hηaxis : η {q | q.val.1 ≠ 0} = 0 := by
        have he := hhi {q | q.val.1 ≠ 0}
        rw [Measure.smul_apply, smul_eq_mul, haxis, mul_zero] at he
        exact le_antisymm he bot_le

      /- A normal-factor test isolates the nonnegative velocity-weighted first measure on the axis. -/
    have hzero : μ = 0 := by
      apply Measure.support_eq_empty_iff.mp
      rw [eq_empty_iff_forall_notMem]
      intro q
      by_cases hqx : q.val.1 = 0
      · have hqv : q.val.2 ≠ 0 := by
          intro hv
          apply q.property
          exact Prod.ext hqx hv
        have ho : IsOpen {p : ℝ × ℝ | p ≠ (0, 0)} := isClosed_singleton.isOpen_compl
        obtain ⟨χ, hsχ, hcχ, hχ, hrχ, hχq⟩ :=
          exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (ho.mem_nhds q.property)
        let w := fun p : ℝ × ℝ => p.2 ^ 2 * χ p
        have hw : Continuous w := (continuous_snd.pow 2).mul hχ.continuous
        have hcw : HasCompactSupport w := hcχ.mul_left
        have hsw : tsupport w ⊆ {p : ℝ × ℝ | p ≠ (0, 0)} :=
          tsupport_mul_subset_right.trans hsχ
        have hcwP : HasCompactSupport (fun p : BellmanPuncturedPlane => w p.val) :=
          bellman_test_compact_subtype hcw hsw
        have hi : Integrable (fun p : BellmanPuncturedPlane => w p.val) μ :=
          (hw.comp continuous_subtype_val).integrable_of_hasCompactSupport hcwP
        have hn : ∀ᵐ p : BellmanPuncturedPlane ∂μ, 0 ≤ w p.val := by
          apply ae_of_all
          intro p
          exact mul_nonneg (sq_nonneg p.val.2) (hrχ ⟨p.val, rfl⟩).1
        have hz : (∫ p : BellmanPuncturedPlane, w p.val ∂μ) = 0 := by
          let g := fun q : ℝ × ℝ => q.2 * χ q
          let φ := fun q : ℝ × ℝ => q.1 * g q
          have hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_snd.mul hχ
          have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := contDiff_fst.mul hg
          have hcφ : HasCompactSupport φ := (hcχ.mul_left).mul_left
          have hsφ : tsupport φ ⊆ {q : ℝ × ℝ | q ≠ (0, 0)} :=
            tsupport_mul_subset_right.trans (tsupport_mul_subset_right.trans hsχ)
          have he := heq φ hφ hcφ hsφ
          have haμ : ∀ᵐ q ∂μ, q.val.1 = 0 := by simpa only [ae_iff] using haxis
          have haη : ∀ᵐ q ∂η, q.val.1 = 0 := by simpa only [ae_iff] using hηaxis
          have h1 : (∫ q : BellmanPuncturedPlane,
              q.val.2 * fderiv ℝ φ q.val (1, 0) ∂μ) =
              ∫ q : BellmanPuncturedPlane, q.val.2 ^ 2 * χ q.val ∂μ := by
            apply integral_congr_ae
            filter_upwards [haμ] with q hq
            change q.val.2 * fderiv ℝ (fun z => z.1 * g z) q.val (1, 0) = _
            rw [bellman_position_mul_fderiv g hg, hq]
            dsimp [g]
            ring
          have h2 : (∫ q : BellmanPuncturedPlane,
              fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) q.val (0, 1) ∂η) = 0 := by
            calc
              _ = ∫ _q : BellmanPuncturedPlane, (0 : ℝ) ∂η := by
                apply integral_congr_ae
                filter_upwards [haη] with q hq
                change fderiv ℝ (fun z => fderiv ℝ (fun w => w.1 * g w) z (0, 1))
                  q.val (0, 1) = 0
                rw [bellman_position_mul_second_velocity g hg, hq, zero_mul]
              _ = 0 := integral_zero _ _
          rw [h1, h2, add_zero] at he
          exact he
        have ha := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
        let U : Set BellmanPuncturedPlane := {p | w p.val ≠ 0}
        have hU : IsOpen U := isOpen_ne_fun (hw.comp continuous_subtype_val) continuous_const
        have hqU : q ∈ U := by
          change q.val.2 ^ 2 * χ q.val ≠ 0
          rw [hχq, mul_one]
          exact pow_ne_zero 2 hqv
        have hμU : μ U = 0 := by
          have ha' : ∀ᵐ p ∂μ, w p.val = 0 := ha
          exact ae_iff.mp ha'
        exact Measure.notMem_support_iff_exists.mpr ⟨U, hU.mem_nhds hqU, hμU⟩
      · have ho : IsOpen {p : BellmanPuncturedPlane | p.val.1 ≠ 0} :=
          isOpen_ne_fun (continuous_fst.comp continuous_subtype_val) continuous_const
        exact Measure.notMem_support_iff_exists.mpr
          ⟨{p | p.val.1 ≠ 0}, ho.mem_nhds hqx, haxis⟩
    refine ⟨hzero, le_antisymm ?_ bot_le⟩
    simpa only [hzero, smul_zero] using hhi
  exact hp.left_ne_zero hμ

end HypoellipticAleksandrov.KineticAleksandrov
