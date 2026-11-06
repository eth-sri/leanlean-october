module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.GeneralOpenWeakChainRule
public import PDEFoundation.Measure.LpDominatedConvergence
public import PDEFoundation.Sobolev.W1p.Truncation
public import HypoellipticAleksandrov.Parabolic.Dirichlet.GeneralOpenPositivePartApproximation

/-!
# Shifted positive parts on general open sets

The smooth one-sided regularizers are composed using the general-open weak
chain rule.  Their values and gradients then converge in `L²` by dominated
convergence; the nonnegative level ensures that the value regularizers are
dominated by the original representative even when the domain has infinite
measure.
-/

@[expose] public section

namespace PDE.H1Function

open Filter MeasureTheory Set
open scoped ENNReal Topology


/-- The positive part above a nonnegative constant belongs to `H¹` on an
arbitrary open set, with the strict-superlevel representative of its weak
gradient. -/
theorem exists_h1PositivePartSubConst_of_isOpen
    {d : ℕ} {U : Set (PDE.Vec d)}
    (hU : IsOpen U) (u : PDE.H1Function U) (c : ℝ) (hc : 0 ≤ c) :
    ∃ v : PDE.H1Function U,
      v.toFun = (fun x => max (u.toFun x - c) 0) ∧
      v.grad = (fun x => {y | c < u.toFun y}.indicator u.grad x) := by
  let δ : ℕ → ℝ := fun n => 1 / (n + 1)
  have hδPos : ∀ n, 0 < δ n := by
    intro n
    positivity
  have hδTendsto : Tendsto δ atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let f  := fun x => max (u.toFun x - c) 0
  let Du  :=
    fun x => {y | c < u.toFun y}.indicator u.grad x
  let valueSeq  :=
    fun n x => PDE.smoothPositivePartApprox c (δ n) (u.toFun x)
  let gradSeq : ℕ → PDE.Vec d → PDE.Vec d :=
    fun n x i =>
      PDE.smoothPositivePartStep c (δ n) (u.toFun x) * u.grad x i
  have hDuCoord : ∀ x i,
      Du x i = (if c < u.toFun x then (1) else 0) * u.grad x i := by
    intro x i
    by_cases hx : c < u.toFun x <;> simp [Du, hx]
  have hvalueSeqAesm : ∀ n,
      AEStronglyMeasurable (valueSeq n) (PDE.volumeOn U) := by
    intro n
    exact
      (PDE.smoothPositivePartApprox_contDiff_one c _).continuous
        |>.comp_aestronglyMeasurable u.memL2.aestronglyMeasurable
  have hgradSeqAesm : ∀ i n,
      AEStronglyMeasurable (fun x => gradSeq n x i) (PDE.volumeOn U) := by
    intro i n
    exact
      ((PDE.smoothPositivePartStep_continuous c _)
        |>.comp_aestronglyMeasurable u.memL2.aestronglyMeasurable).mul
        (u.gradMemL2 i).aestronglyMeasurable
  have hvalueTendsto : ∀ x,
      Tendsto (fun n => valueSeq n x) atTop (𝓝 (f x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have htwo : Tendsto (fun n => 2 * δ n) atTop (𝓝 0) := by
      simpa only [mul_zero] using hδTendsto.const_mul _
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) htwo
    exact PDE.abs_smoothPositivePartApprox_sub_le
      (hδPos n) _
  have hgradTendsto : ∀ i x,
      Tendsto (fun n => gradSeq n x i) atTop (𝓝 (Du x i)) := by
    intro i x
    have htendsto :=
      (PDE.tendsto_smoothPositivePartStep
        (c := c) hδPos hδTendsto (u.toFun x)).mul_const (u.grad x i)
    simpa only [gradSeq, hDuCoord] using htendsto
  have hfAesm : AEStronglyMeasurable f _ :=
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
    rw [hDuCoord]
    split_ifs
    · simpa only [one_mul] using le_rfl
    · simpa only [zero_mul, norm_zero] using norm_nonneg _
  have hvalueSeqBound : ∀ n x, ‖valueSeq n x‖ ≤ ‖u.toFun x‖ := by
    intro n
    intro x
    rw [Real.norm_eq_abs]
    have hnonneg := PDE.smoothPositivePartApprox_nonneg
      (c := c) (hδPos n) (u.toFun x)
    rw [abs_of_nonneg hnonneg]
    rcases le_or_gt (u.toFun x) c with hx | hx
    · rw [PDE.smoothPositivePartApprox_eq_zero_of_le (hδPos n) hx]
      exact abs_nonneg _
    · calc
        PDE.smoothPositivePartApprox c _ _
            ≤ |u.toFun x - c| :=
          le_trans (le_abs_self _)
            (PDE.abs_smoothPositivePartApprox_le c _ _)
        _ = u.toFun x - c := abs_of_pos (sub_pos.2 hx)
        _ ≤ u.toFun x := sub_le_self _ hc
        _ ≤ |u.toFun x| := le_abs_self _
  have hvalueSeqMem : ∀ n, PDE.MemL2On U (valueSeq n) := by
    intro n
    exact MemLp.of_le u.memL2 (hvalueSeqAesm n)
      (Filter.Eventually.of_forall (hvalueSeqBound n))
  have hgradSeqBound : ∀ n i x, ‖gradSeq n x i‖ ≤ ‖u.grad x i‖ := by
    intro n i x
    rw [norm_mul]
    calc
      |PDE.smoothPositivePartStep c _ _| * ‖u.grad x i‖
          ≤ 1 * ‖u.grad x i‖ :=
        mul_le_mul_of_nonneg_right
          (PDE.abs_smoothPositivePartStep_le_one c _ _)
          (norm_nonneg _)
      _ = ‖u.grad x i‖ := one_mul _
  have hgradSeqMem : ∀ n, PDE.GradMemL2On U (gradSeq n) := by
    intro n i
    exact MemLp.of_le (u.gradMemL2 i) (hgradSeqAesm i n)
      (Filter.Eventually.of_forall (hgradSeqBound n i))
  have hweakSeq : ∀ n,
      PDE.HasWeakGradientOn U (valueSeq n) (gradSeq n) := by
    intro n
    have hzero  :=
      PDE.smoothPositivePartApprox_eq_zero_of_le (hδPos n) hc
    simpa only [valueSeq, gradSeq, PDE.deriv_smoothPositivePartApprox] using
      hasWeakGradient_comp_contDiff_of_deriv_bounded_of_isOpen
        hU u (PDE.smoothPositivePartApprox_contDiff_one c _) hzero
        zero_le_one (PDE.abs_deriv_smoothPositivePartApprox_le c _)
  have hvalueConv : Tendsto
      (fun n => eLpNorm (valueSeq n - f) 2 (PDE.volumeOn U))
      atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_zero_of_ae_dominated
      (bound := fun x => (2) * u.toFun x)
    · intro n
      exact (hvalueSeqAesm n).sub hfAesm
    · exact u.memL2.const_mul 2
    · intro n
      filter_upwards with x
      rw [norm_mul]
      exact (norm_sub_le _ _).trans (by
        rw [mul_comm]
        calc
          ‖valueSeq n x‖ + ‖f x‖ ≤ ‖u.toFun x‖ + ‖u.toFun x‖ := add_le_add
            (hvalueSeqBound n x) (by
              change ‖max _ 0‖ ≤ ‖u.toFun x‖
              rcases le_or_gt (u.toFun x - c) 0 with hx | hx
              · simp [hx]
              · rw [max_eq_left hx.le, Real.norm_eq_abs, abs_of_pos hx]
                exact (sub_le_self _ hc).trans (le_abs_self _))
          _ = ‖u.toFun x‖ * ‖(2 : ℝ)‖ := by norm_num; ring)
    · filter_upwards with x
      exact tendsto_sub_nhds_zero_iff.2 (hvalueTendsto x)
  have hgradConv : ∀ i, Tendsto
      (fun n => eLpNorm (fun x => gradSeq n x i - Du x i)
        2 (PDE.volumeOn U)) atTop (𝓝 0) := by
    intro i
    apply tendsto_eLpNorm_two_zero_of_ae_dominated
      (bound := fun x => (2) * u.grad x i)
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
              rw [hDuCoord]
              split_ifs <;> simp)
          _ = ‖u.grad x i‖ * ‖(2 : ℝ)‖ := by norm_num; ring)
    · filter_upwards with x
      exact tendsto_sub_nhds_zero_iff.2 (hgradTendsto i x)
  have hweak  :=
    PDE.HasWeakGradientOn.of_tendsto_eLpNorm
      hfMem hDuMem hvalueSeqMem hgradSeqMem hweakSeq hvalueConv hgradConv
  exact ⟨⟨f, Du, hfMem, hDuMem, hweak⟩, rfl, rfl⟩

end PDE.H1Function
