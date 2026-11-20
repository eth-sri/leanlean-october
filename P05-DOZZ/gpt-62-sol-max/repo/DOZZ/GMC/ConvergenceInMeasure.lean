/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! Stability of convergence in measure under pointwise operations. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace DOZZ.Proofs

/-- If an error is bounded by the sum of two errors tending to zero in measure, it too
vanishes in measure. No measurability of the random variables is required. -/
theorem tendstoInMeasure_of_norm_sub_le_add {Ω ι E : Type*} [MeasurableSpace Ω]
    [SeminormedAddCommGroup E] {μ : Measure Ω} {l : Filter ι}
    {f g u : ι → Ω → E} {F G U : Ω → E} (hf : TendstoInMeasure μ f l F)
    (hg : TendstoInMeasure μ g l G)
    (h : ∀ᶠ i in l, ∀ᵐ ω ∂μ, ‖u i ω - U ω‖ ≤ ‖f i ω - F ω‖ + ‖g i ω - G ω‖) :
    TendstoInMeasure μ u l U := by
  rw [tendstoInMeasure_iff_norm] at hf hg ⊢
  intro ε hε
  specialize hf (ε / 2) (half_pos hε)
  specialize hg (ε / 2) (half_pos hε)
  have hsum := hf.add hg
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [h] with i hi
  refine (measure_mono_ae (t := {ω | ε / 2 ≤ ‖f i ω - F ω‖} ∪
    {ω | ε / 2 ≤ ‖g i ω - G ω‖}) ?_).trans (measure_union_le _ _)
  filter_upwards [hi] with ω hw hu
  change ε ≤ ‖u i ω - U ω‖ at hu
  by_contra hn
  simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hn
  linarith only [hw, hu, hn.1, hn.2]

section
variable {Ω ι E : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup E] (P : Measure Ω) {l : Filter ι}
  (F G : ι → Ω → E) (Flim Glim : Ω → E) (hF : TendstoInMeasure P F l Flim)
  (hG : TendstoInMeasure P G l Glim)
include Ω ι E hF hG

/-- The sum of two families converging in measure converges to the sum of their limits. -/
theorem tendstoInMeasure_add :
    TendstoInMeasure P (fun i ω => F i ω + G i ω) l (fun ω => Flim ω + Glim ω) := by
  apply tendstoInMeasure_of_norm_sub_le_add hF hG
  exact Eventually.of_forall fun i => ae_of_all _ fun ω => by
    convert norm_add_le (F i ω - Flim ω) (G i ω - Glim ω) using 1 <;> congr 1 <;> abel

/-- Subtraction preserves convergence in measure. -/
theorem tendstoInMeasure_sub :
    TendstoInMeasure P (fun i ω => F i ω - G i ω) l (fun ω => Flim ω - Glim ω) := by
  apply tendstoInMeasure_of_norm_sub_le_add hF hG
  exact Eventually.of_forall fun i => ae_of_all _ fun ω => by
    convert norm_sub_le (F i ω - Flim ω) (G i ω - Glim ω) using 1 <;> congr 1 <;> abel

end

/-- A vanishing difference transfers convergence in measure. -/
theorem tendstoInMeasure_add_of_sub {Ω ι E : Type*} [MeasurableSpace Ω]
    [SeminormedAddCommGroup E] (P : Measure Ω) {l : Filter ι}
    (f g : ι → Ω → E) (y : Ω → E)
    (hfg : TendstoInMeasure P (fun i ω => f i ω - g i ω) l (fun _ => 0))
    (hgy : TendstoInMeasure P g l y) : TendstoInMeasure P f l y := by
  simpa only [sub_add_cancel, zero_add] using tendstoInMeasure_add P _ _ _ _ hfg hgy

/-- Coordinatewise convergence in measure implies joint convergence for finitely many
coordinates. -/
theorem tendstoInMeasure_pi_finite {Ω ι κ E : Type*} [MeasurableSpace Ω] [Fintype ι]
    [SeminormedAddCommGroup E] (μ : Measure Ω) {l : Filter κ}
    (f : κ → Ω → ι → E) (g : Ω → ι → E)
    (hcoord : ∀ i, TendstoInMeasure μ (fun n ω => f n ω i) l (fun ω => g ω i)) :
    TendstoInMeasure μ f l g := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have htail (i : ι) := (tendstoInMeasure_iff_norm.mp (hcoord i)) ε hε
  have hsum : Tendsto (fun n => ∑ i : ι, μ {ω | ε ≤ ‖f n ω i - g ω i‖}) l (𝓝 0) := by
    simpa using (tendsto_finsetSum Finset.univ fun (i : ι) _ => htail i)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le) ?_
  intro n
  refine (measure_mono (t := ⋃ i, {ω | ε ≤ ‖f n ω i - g ω i‖}) ?_).trans
    (measure_iUnion_fintype_le μ _)
  intro ω hw
  change ε ≤ ‖f n ω - g ω‖ at hw
  by_contra hn
  apply (not_lt_of_ge hw) ((pi_norm_lt_iff hε).2 fun i => ?_)
  exact lt_of_not_ge fun hi => hn (mem_iUnion.2 ⟨i, hi⟩)

/-- An AE measurable finite random scalar preserves convergence in measure on a finite
measure space; independence is not required. -/
theorem tendstoInMeasure_mul_random {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {l : Filter ι} {W : Ω → ℝ} (hW : AEMeasurable W μ)
    {f : ι → Ω → ℝ} {g : Ω → ℝ} (hfg : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ (fun i ω => W ω * f i ω) l (fun ω => W ω * g ω) := by
  rw [tendstoInMeasure_iff_norm] at hfg ⊢
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  let T (n : ℕ) := {ω | (n : ℝ) < ‖W ω‖}
  have hT : Antitone T := by
    intro n m hnm ω hw
    exact lt_of_le_of_lt (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast hnm)
      (show (m : ℝ) < ‖W ω‖ from hw)
  have hi : (⋂ n, T n) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨n, hn⟩ := exists_nat_gt ‖W ω‖
    exact ⟨n, not_lt_of_ge hn.le⟩
  have ht := tendsto_measure_iInter_atTop (μ := μ) (s := T)
    (fun _ => nullMeasurableSet_lt aemeasurable_const hW.norm) hT ⟨0, measure_ne_top μ _⟩
  rw [hi, measure_empty] at ht
  have hδ₂ : 0 < δ / 2 := ENNReal.div_pos_iff.mpr ⟨hδ.ne', by simp⟩
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp ht (δ / 2) hδ₂
  let K : ℝ := (N + 1 : ℕ)
  have hK : 0 < K := by positivity
  have hk : μ {ω | K < ‖W ω‖} ≤ δ / 2 := hN _ (Nat.le_succ _)
  filter_upwards [ENNReal.tendsto_nhds_zero.mp (hfg (ε / K) (div_pos hε hK)) _ hδ₂] with i hi
  refine ((measure_mono (t := {ω | K < ‖W ω‖} ∪ {ω | ε / K ≤ ‖f i ω - g ω‖}) ?_).trans
    (measure_union_le _ _)).trans ((add_le_add hk hi).trans_eq (ENNReal.add_halves δ))
  intro ω hw
  change ε ≤ ‖W ω * f i ω - W ω * g ω‖ at hw
  by_contra hn
  simp only [mem_union, mem_ofPred_eq, not_or, not_lt, not_le] at hn
  rw [← mul_sub, norm_mul] at hw
  exact (not_lt_of_ge hw) (calc
    _ ≤ K * ‖f i ω - g ω‖ := mul_le_mul_of_nonneg_right hn.1 (norm_nonneg _)
    _ < K * (ε / K) := mul_lt_mul_of_pos_left hn.2 hK
    _ = ε := mul_div_cancel₀ ε hK.ne')

end DOZZ.Proofs
