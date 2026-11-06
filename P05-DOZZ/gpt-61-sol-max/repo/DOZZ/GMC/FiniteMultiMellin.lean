/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosMellin
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-! Factorization of nonnegative product integrals over finite product measures. -/

public section

open MeasureTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

private theorem lintegral_fin_pi_prod
    {α : Type*} [MeasurableSpace α] {n : ℕ}
    (μ : Fin n → Measure α) (f : Fin n → α → ℝ≥0∞)
    (hμ : ∀ i, SigmaFinite (μ i)) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → α, ∏ i, f i (x i) ∂Measure.pi μ =
      ∏ i, ∫⁻ y, f i y ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [← (measurePreserving_piFinSuccAbove μ 0).symm.lintegral_comp (by fun_prop)]
      simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
        Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      rw [lintegral_prod_mul (g := fun y : Fin n → α => ∏ i, f i.succ (y i))
        (hf 0).aemeasurable
        (Finset.measurable_prod _ (fun i _ => (hf _).comp (measurable_pi_apply i))).aemeasurable,
        ih (fun i => μ i.succ) (fun i => f i.succ) (fun i => hμ i.succ) (fun i => hf i.succ)]

/-- The integral of a product of coordinatewise nonnegative functions over a finite product
measure factors into the product of the coordinate integrals. -/
theorem lintegral_pi_prod
    {α κ : Type*} [MeasurableSpace α] [Fintype κ]
    (μ : κ → Measure α) (f : κ → α → ℝ≥0∞)
    (hμ : ∀ i, SigmaFinite (μ i)) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : κ → α, ∏ i, f i (x i) ∂Measure.pi μ =
      ∏ i, ∫⁻ y, f i y ∂μ i := by
  classical
  let e := (Fintype.equivFin κ).symm
  rw [← (measurePreserving_piCongrLeft μ e).lintegral_comp (by fun_prop)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_pi_prod _ _ (fun i => hμ (e i)) (fun i => hf (e i))


/-- Coordinates of the product of positive-half-line measures are positive almost everywhere. -/
theorem ae_pi_Ioi_pos {κ : Type*} [Fintype κ] :
    ∀ᵐ t ∂Measure.pi (fun _ : κ => volume.restrict (Ioi (0 : ℝ))), ∀ k, 0 < t k := by
  apply ae_all_iff.2
  intro k
  rw [ae_iff]
  have hn : (volume.restrict (Ioi (0 : ℝ))) (Iic (0 : ℝ)) = 0 := by
    rw [Measure.restrict_apply measurableSet_Iic, Set.inter_comm, Ioi_inter_Iic]
    simp
  simpa [Function.eval, Set.preimage, Set.mem_Iic] using
    (Measure.pi_eval_preimage_null (fun _ : κ => volume.restrict (Ioi (0 : ℝ))) hn)

/-- The multivariate Mellin formula, with zeros allowed in every mass coordinate. -/
theorem multi_rpow_neg_lintegral_eq_weighted_laplace
    {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (P : Measure Ω) [SFinite P] (m : Ω → κ → ℝ)
    (hm : ∀ ω k, 0 ≤ m ω k) (hmA : ∀ k, Measurable (fun ω => m ω k))
    (q : κ → ℝ) (hq : ∀ k, 0 < q k) :
    ∫⁻ ω, ∏ k, (ENNReal.ofReal (m ω k)) ^ (-q k) ∂P =
      (∏ k, ENNReal.ofReal (1 / Real.Gamma (q k))) *
        ∫⁻ t, ENNReal.ofReal (∏ k, t k ^ (q k - 1)) *
            (∫⁻ ω, ENNReal.ofReal (Real.exp (-∑ k, t k * m ω k)) ∂P)
          ∂Measure.pi (fun _ : κ => volume.restrict (Ioi (0 : ℝ))) := by
  classical
  let T := Measure.pi (fun _ : κ => volume.restrict (Ioi (0 : ℝ)))
  let C := ∏ k, ENNReal.ofReal (1 / Real.Gamma (q k))
  let f : Ω → (κ → ℝ) → ℝ≥0∞ := fun ω t =>
    ∏ k, ENNReal.ofReal (t k ^ (q k - 1) * Real.exp (-(m ω k * t k)))
  have hpoint (ω : Ω) : (∏ k, (ENNReal.ofReal (m ω k)) ^ (-q k)) =
      C * ∫⁻ t, f ω t ∂T := by
    simp_rw [nonneg_rpow_neg_eq_mellin_lintegral (hm ω _) (hq _)]
    rw [Finset.prod_mul_distrib]
    congr 1
    exact (lintegral_pi_prod _ _ (fun _ => by infer_instance) (fun _ => by fun_prop)).symm
  have hf : AEMeasurable (Function.uncurry f) (P.prod T) := by
    have hmk (k : κ) : Measurable (fun z : Ω × (κ → ℝ) => m z.1 k) :=
      (hmA k).comp measurable_fst
    fun_prop
  calc
    _ = C * ∫⁻ t, ∫⁻ ω, f ω t ∂P ∂T := by
      simp_rw [hpoint]
      rw [lintegral_const_mul' _ _ (ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)),
        lintegral_lintegral_swap hf]
    _ = _ := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_pi_Ioi_pos (κ := κ)] with t ht
      have hkernel (ω : Ω) : f ω t = ENNReal.ofReal (∏ k, t k ^ (q k - 1)) *
          ENNReal.ofReal (Real.exp (-∑ k, t k * m ω k)) := by
        dsimp [f]
        simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg (ht _).le _)]
        rw [Finset.prod_mul_distrib, ← ENNReal.ofReal_prod_of_nonneg
          (fun k _ => Real.rpow_nonneg (ht k).le _),
          ← ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.exp_nonneg _), ← Real.exp_sum]
        congr 3
        simp [Finset.sum_neg_distrib, mul_comm]
      simp_rw [hkernel]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top


end DOZZ.Proofs
