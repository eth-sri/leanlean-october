module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.GeneralOpenWeakChainRule
public import PDEFoundation.Measure.LpDominatedConvergence
public import PDEFoundation.Sobolev.W1p.Truncation
import Mathlib.Tactic.NormNum



/-!
# Shifted positive parts on general open sets

The smooth one-sided regularizers are composed using the general-open weak
chain rule.  Their values and gradients then converge in `L²` by dominated
convergence; the nonnegative level ensures that the value regularizers are
dominated by the original representative even when the domain has infinite
measure.
-/

 public section

namespace PDE.H1Function

open Filter MeasureTheory Set
open scoped ENNReal Topology

private theorem tendsto_eLpNorm_two_zero_of_ae_dominated
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {F : ℕ → α → E} {bound : α → E}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hboundMem : MemLp bound (2 ) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ ‖bound x‖)
    (hzero : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) (2 ) μ) atTop (𝓝 0) := by
  let G  := fun n x => ‖F n x‖ₑ ^ (2 : ℝ)
  let B  := fun x => ‖bound x‖ₑ ^ (2 : ℝ)


  have hBFinite  :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 )) (by norm_num) (by norm_num) (memLp_iff.mp hboundMem)).ne


  simpa only [Function.comp_def, G, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (hF _), ENNReal.toReal_ofNat, one_div,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)] using
    ((ENNReal.continuous_rpow_const :
      Continuous (fun a : ℝ≥0∞ => a ^ ((2 : ℝ)⁻¹))).tendsto 0).comp (by
          simpa only [lintegral_zero] using
            tendsto_lintegral_of_dominated_convergence' B (show ∀ n, AEMeasurable (G n) μ from fun n => (hF n).enorm.pow_const _) (show ∀ n, G n ≤ᵐ[μ] B by
                intro n
                filter_upwards [hbound n] with x hx
                exact ENNReal.rpow_le_rpow (by
                  simpa only [ofReal_norm_eq_enorm] using ENNReal.ofReal_le_ofReal hx) (by norm_num)) hBFinite (show ∀ᵐ x ∂μ, Tendsto (fun n => G n x) atTop (𝓝 0) by
                filter_upwards [hzero] with x hx

                simpa only [G, Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] using
                  ((ENNReal.continuous_rpow_const : Continuous (fun a : ℝ≥0∞ => a ^ (2 : ℝ))).tendsto 0).comp
                    (by
                        simpa only [Function.comp_def, enorm_zero] using (continuous_enorm.tendsto 0).comp hx)))

/-- The positive part above a nonnegative constant belongs to `H¹` on an
arbitrary open set, with the strict-superlevel representative of its weak
gradient. -/
theorem exists_h1PositivePartSubConst_of_isOpen
    {d : ℕ} {U : PDE.VelocityRegion d}
    (hU : IsOpen U) (u : PDE.H1Function U) (c : ℝ) (hc : 0 ≤ c) :
    ∃ v : PDE.H1Function U,
      v.toFun = (fun x => max (u.toFun x - c) 0) ∧
      v.grad = (({y | c < u.toFun y}.indicator u.grad)) := by
  let δ : ℕ → ℝ := fun n => 1 / (n + 1)
  have hδPos : ∀ n, 0 < δ n := by
    intro n
    dsimp only [δ]
    positivity
  have hδTendsto : Tendsto δ atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let f  := fun x => max (u.toFun x - c) 0
  let Du  :=
    ({y | c < u.toFun y}.indicator u.grad)
  let valueSeq  :=
    fun n x => PDE.smoothPositivePartApprox c (δ n) (u.toFun x)
  let gradSeq  :=
    fun n x i =>
      PDE.smoothPositivePartStep c (δ n) (u.toFun x) * u.grad x i
  have hDuCoord : ∀ x i,
      Du x i = (if c < u.toFun x then (1 : ℝ) else 0) * u.grad x i := by
    intro x i
    by_cases hx : c < u.toFun x <;> simp [Du, hx]
  have hvalueSeqAesm : ∀ n,
      AEStronglyMeasurable (valueSeq n) (PDE.volumeOn U) := by
    intro n
    exact
      (PDE.smoothPositivePartApprox_contDiff_one c (δ n)).continuous
        |>.comp_aestronglyMeasurable u.memL2.aestronglyMeasurable
  have hgradSeqAesm : ∀ i n,
      AEStronglyMeasurable (fun x => gradSeq n x i) (PDE.volumeOn U) := by
    intro i n
    exact
      ((PDE.smoothPositivePartStep_continuous c (δ n))
        |>.comp_aestronglyMeasurable u.memL2.aestronglyMeasurable).mul
        (u.gradMemL2 i).aestronglyMeasurable

  have hgradTendsto : ∀ i x,
      Tendsto (fun n => gradSeq n x i) atTop (𝓝 (Du x i)) := by
    intro i x
    have htendsto :=
      (PDE.tendsto_smoothPositivePartStep
        (c := c) hδPos hδTendsto (u.toFun x)).mul_const (u.grad x i)
    simpa only [gradSeq, hDuCoord x i] using htendsto
  have hfAesm : AEStronglyMeasurable f (PDE.volumeOn U) :=
    (((continuous_id.sub continuous_const).max continuous_const)
      |>.comp_aestronglyMeasurable u.memL2.aestronglyMeasurable)
  have hfMem : PDE.MemL2On U f := by
    refine MemLp.of_le u.memL2 hfAesm ?_
    filter_upwards with x
    simp only [f, Real.norm_eq_abs]
    rcases le_or_gt (u.toFun x - c) 0 with hnonpos | hpos
    · simp only [max_eq_right hnonpos, abs_zero, abs_nonneg]
    · rw [max_eq_left hpos.le, abs_of_pos hpos]
      calc
        u.toFun x - c ≤ u.toFun x := sub_le_self _ hc
        _ ≤ |u.toFun x| := le_abs_self _
  have hDuAesm : ∀ i,
      AEStronglyMeasurable (fun x => Du x i) (PDE.volumeOn U) := by
    intro i
    exact aestronglyMeasurable_of_tendsto_ae atTop
      (hgradSeqAesm i)
      (Filter.Eventually.of_forall (hgradTendsto i))
  have hDuMem : PDE.GradMemL2On U Du := by
    intro i
    refine MemLp.of_le (u.gradMemL2 i) (hDuAesm i) ?_
    filter_upwards with x
    rw [hDuCoord x i]
    split_ifs
    · norm_num
    · simpa only [zero_mul, norm_zero] using norm_nonneg (u.grad x i)
  have hvalueSeqBound : ∀ n x, ‖valueSeq n x‖ ≤ ‖u.toFun x‖ := by
    intro n
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hnonneg := PDE.smoothPositivePartApprox_nonneg
      (c := c) (hδPos n) (u.toFun x)
    rw [abs_of_nonneg hnonneg]
    rcases le_or_gt (u.toFun x) c with hx | hx
    · rw [PDE.smoothPositivePartApprox_eq_zero_of_le (hδPos n) hx]
      exact abs_nonneg _
    · calc
        PDE.smoothPositivePartApprox c (δ n) (u.toFun x)
            ≤ |u.toFun x - c| :=
          le_trans (le_abs_self _)
            (PDE.abs_smoothPositivePartApprox_le c (δ n) (u.toFun x))
        _ = u.toFun x - c := abs_of_pos (sub_pos.2 hx)
        _ ≤ u.toFun x := sub_le_self _ hc
        _ ≤ |u.toFun x| := le_abs_self _

  have hgradSeqBound : ∀ n i x, ‖gradSeq n x i‖ ≤ ‖u.grad x i‖ := by
    intro n i x
    change ‖PDE.smoothPositivePartStep c (δ n) (u.toFun x) * u.grad x i‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs]
    calc
      |PDE.smoothPositivePartStep c (δ n) (u.toFun x)| * ‖u.grad x i‖
          ≤ 1 * ‖u.grad x i‖ :=
        mul_le_mul_of_nonneg_right
          (PDE.abs_smoothPositivePartStep_le_one c (δ n) (u.toFun x))
          (norm_nonneg (u.grad x i))
      _ = ‖u.grad x i‖ := one_mul _




  have hweak  :=
    PDE.HasWeakGradientOn.of_tendsto_eLpNorm
      hfMem hDuMem (by
          intro n
          exact MemLp.of_le u.memL2 (hvalueSeqAesm n)
            (Filter.Eventually.of_forall (hvalueSeqBound n))) (by
          intro n i
          exact MemLp.of_le (u.gradMemL2 i) (hgradSeqAesm i n)
            (Filter.Eventually.of_forall (hgradSeqBound n i))) (by
          intro n

          simpa only [valueSeq, gradSeq, PDE.deriv_smoothPositivePartApprox] using
            hasWeakGradient_comp_contDiff_of_deriv_bounded_of_isOpen
              hU u (PDE.smoothPositivePartApprox_contDiff_one c (δ n)) (PDE.smoothPositivePartApprox_eq_zero_of_le (hδPos n) hc)
              zero_le_one (PDE.abs_deriv_smoothPositivePartApprox_le c (δ n))) (by
          apply tendsto_eLpNorm_two_zero_of_ae_dominated
            (bound := fun x => (2 : ℝ) * u.toFun x)
          · intro n
            exact (hvalueSeqAesm n).sub hfAesm
          · exact u.memL2.const_mul 2
          · intro n
            filter_upwards with x
            rw [Pi.sub_apply, norm_mul]
            exact (norm_sub_le _ _).trans (by
              rw [mul_comm]
              calc
                ‖valueSeq n x‖ + ‖f x‖ ≤ ‖u.toFun x‖ + ‖u.toFun x‖ := add_le_add
                  (hvalueSeqBound n x) (by
                    change ‖max (u.toFun x - c) 0‖ ≤ ‖u.toFun x‖
                    rcases le_or_gt (u.toFun x - c) 0 with hx | hx
                    · simp [hx]
                    · rw [max_eq_left hx.le, Real.norm_eq_abs, abs_of_pos hx]
                      exact (sub_le_self _ hc).trans (le_abs_self _))
                _ = ‖u.toFun x‖ * ‖(2 : ℝ)‖ := by norm_num; ring)
          · filter_upwards with x
            exact tendsto_sub_nhds_zero_iff.2 ((show ∀ x,
      Tendsto (fun n => valueSeq n x) atTop (𝓝 (f x)) by
                intro x
                rw [tendsto_iff_norm_sub_tendsto_zero]

                refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by
                    simpa only [mul_zero] using hδTendsto.const_mul (2 : ℝ))
                rw [Real.norm_eq_abs]
                exact PDE.abs_smoothPositivePartApprox_sub_le
                  (hδPos n) (u.toFun x)) x)) (by
          intro i
          apply tendsto_eLpNorm_two_zero_of_ae_dominated
            (bound := fun x => (2 : ℝ) * u.grad x i)
          · intro n
            exact (hgradSeqAesm i n).sub (hDuAesm i)
          · exact (u.gradMemL2 i).const_mul 2
          · intro n
            filter_upwards with x
            rw [norm_mul]
            exact (norm_sub_le _ _).trans (by
              rw [mul_comm]
              calc
                ‖gradSeq n x i‖ + ‖Du x i‖ ≤
                    ‖u.grad x i‖ + ‖u.grad x i‖ := add_le_add
                  (hgradSeqBound n i x) (by
                    rw [hDuCoord x i]
                    split_ifs <;> simp)
                _ = ‖u.grad x i‖ * ‖(2 : ℝ)‖ := by norm_num; ring)
          · filter_upwards with x
            exact tendsto_sub_nhds_zero_iff.2 (hgradTendsto i x))
  exact ⟨⟨f, Du, hfMem, hDuMem, hweak⟩, rfl, rfl⟩

end PDE.H1Function
