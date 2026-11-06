module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.PairSetting
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationHomogeneity
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpaceGeometry
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Dyadic annuli cover every nonzero homogeneous measure -/

@[expose] public section
noncomputable section
open Set MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov

/- The source's closed unit annulus on the punctured carrier. -/
def bellmanUnitAnnulus : Set BellmanPuncturedPlane :=
  {q | 1 ≤ bellmanGauge q.val ∧ bellmanGauge q.val ≤ 2}

/- A dyadic annulus is the literal dilation image of the unit annulus. -/
def bellmanDyadicAnnulus (j : ℤ) : Set BellmanPuncturedPlane :=
  bellmanDilation (2 ^ j) (zpow_pos (by norm_num) j) '' bellmanUnitAnnulus

/- Closed positive-radius shells are compact on the punctured carrier. -/
theorem bellman_shell_punctured_isCompact (a b : ℝ) (ha : 0 < a) :
    IsCompact {q : BellmanPuncturedPlane | a ≤ bellmanGauge q.val ∧
      bellmanGauge q.val ≤ b} := by
  have _h_xinl_0 : IsCompact {q : ℝ × ℝ | a ≤ bellmanGauge q ∧ bellmanGauge q ≤ b} := by
    have hc : IsClosed {q : ℝ × ℝ | a ≤ bellmanGauge q ∧ bellmanGauge q ≤ b} :=
      (isClosed_le continuous_const bellmanGauge_continuous).inter
        (isClosed_le bellmanGauge_continuous continuous_const)
    apply IsCompact.of_isClosed_subset
      (bellmanGaugePower_sublevel_isCompact (max 0 (b ^ 6)) (le_max_left _ _)) hc
    intro q hq
    change bellmanGaugePower q ≤ max 0 (b ^ 6)
    rw [← bellmanGauge_pow_six]
    exact (pow_le_pow_left₀ (bellmanGauge_nonneg q) hq.2 6).trans (le_max_right _ _)
  apply Topology.IsInducing.subtypeVal.isCompact_preimage'
    _h_xinl_0
  intro q hq
  refine ⟨⟨q, ?_⟩, rfl⟩
  intro he
  have hn := hq.1
  rw [he] at hn
  norm_num [bellmanGauge, bellmanGaugePower] at hn
  linarith only [hn, ha]

/- The closed unit annulus is compact. -/
theorem bellmanUnitAnnulus_isCompact : IsCompact bellmanUnitAnnulus :=
  bellman_shell_punctured_isCompact 1 2 (by norm_num)

/- Membership in a dyadic annulus is the corresponding gauge interval. -/
theorem mem_bellmanDyadicAnnulus_iff (j : ℤ) (q : BellmanPuncturedPlane) :
    q ∈ bellmanDyadicAnnulus j ↔
      2 ^ j ≤ bellmanGauge q.val ∧ bellmanGauge q.val ≤ 2 * 2 ^ j := by
  let r : ℝ := 2 ^ j
  have hr : 0 < r := zpow_pos (by norm_num) _
  constructor
  · rintro ⟨p, hp, rfl⟩
    change r ≤ bellmanGauge (bellmanPlaneDilation r p.val) ∧
      bellmanGauge (bellmanPlaneDilation r p.val) ≤ 2 * r
    rw [bellmanGauge_dilation r hr]
    exact ⟨by nlinarith only [hp.1, hr], by nlinarith only [hp.2, hr]⟩
  · intro hq
    let T := bellmanDilationHomeomorph r hr
    refine ⟨T.symm q, ?_, T.apply_symm_apply q⟩
    have he : bellmanGauge q.val = r * bellmanGauge (T.symm q).val := by
      have h := bellmanGauge_dilation r hr (T.symm q).val
      change bellmanGauge (T (T.symm q)).val = _ at h
      rw [T.apply_symm_apply] at h
      exact h
    change 1 ≤ bellmanGauge (T.symm q).val ∧ bellmanGauge (T.symm q).val ≤ 2
    constructor <;> nlinarith only [hq.1, hq.2, he, hr]

/- Every punctured point belongs to some dyadic annulus. -/
theorem bellmanDyadicAnnulus_iUnion : (⋃ j : ℤ, bellmanDyadicAnnulus j) = univ := by
  apply eq_univ_of_forall
  intro q
  obtain ⟨j, hj⟩ := exists_mem_Ico_zpow (bellmanGauge_pos q.val q.property)
    (by norm_num : (1 : ℝ) < 2)
  apply mem_iUnion.mpr
  refine ⟨j, (mem_bellmanDyadicAnnulus_iff j q).mpr ⟨hj.1, ?_⟩⟩
  simpa only [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, mul_comm] using hj.2.le

/- Nonzero homogeneous Radon measures have positive mass on the closed unit annulus. -/
end HypoellipticAleksandrov.KineticAleksandrov
