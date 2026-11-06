/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosNegativePower
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Prod

/-! Mellin representation of negative moments for measurable nonnegative masses, including
possible zero values. -/

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace DOZZ.Proofs

/-- Mellin's Laplace representation remains valid for a measurable nonnegative random variable
that may vanish. Positive shifts and monotone convergence handle the infinite value at zero. -/
theorem nonneg_rpow_neg_lintegral_eq_weighted_laplace
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (m : Ω → ℝ)
    (hm : ∀ ω, 0 ≤ m ω) (hmA : AEMeasurable m P) q (hq : 0 < q) :
    ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (m ω)) (-q) ∂P =
      ENNReal.ofReal (1 / Real.Gamma q) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1)) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-(m ω * t))) ∂P) ∂volume := by
  classical
  let ε : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ n
  have hεpos n : 0 < ε n := by
    dsimp [ε]
    positivity
  have hεmono : Antitone ε := by
    intro i j hij
    dsimp [ε]
    exact pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hij
  have hεtend : Tendsto ε atTop (𝓝 0) := by
    dsimp [ε]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  let mε : ℕ → Ω → ℝ := fun n ω => m ω + ε n
  have hmεpos n ω : 0 < mε n ω :=
    lt_of_lt_of_le (hεpos n) (by dsimp [mε]; linarith [hm ω])
  have hmεA (n : ℕ) := hmA.add_const (ε n)
  let ψ : ℝ → ℝ≥0∞ := fun x => ENNReal.rpow (ENNReal.ofReal x) (-q)
  have hψcont : Continuous ψ := ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal
  let L : ℕ → Ω → ℝ≥0∞ := fun n ω => ψ (mε n ω)
  let Llim : Ω → ℝ≥0∞ := fun ω => ψ (m ω)
  have hLmono : ∀ ω, Monotone (fun n => L n ω) := by
    intro ω i j hij
    change ψ (mε i ω) ≤ ψ (mε j ω)
    dsimp [ψ]
    rw [ENNReal.ofReal_rpow_of_pos (hmεpos i ω),
      ENNReal.ofReal_rpow_of_pos (hmεpos j ω)]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (hmεpos j ω) (by dsimp [mε]; simpa [add_comm] using add_le_add_left (hεmono hij) (m ω)) (neg_nonpos.mpr hq.le))
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let c := ENNReal.ofReal (1 / Real.Gamma q)
  let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (q - 1))
  let F : ℕ → Ω × ℝ → ℝ≥0∞ := fun n z =>
    ENNReal.ofReal (z.2 ^ (q - 1) * Real.exp (-(mε n z.1 * z.2)))
  let Flim : Ω × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (z.2 ^ (q - 1) * Real.exp (-(m z.1 * z.2)))
  have hFmeas : ∀ n, AEMeasurable (F n) (P.prod ν) := by
    intro n
    exact ((show Measurable (fun z : Ω × ℝ => z.2 ^ (q - 1)) by fun_prop).aemeasurable.mul (Real.measurable_exp.comp_aemeasurable ((((hmεA n).comp_fst).mul measurable_snd.aemeasurable).neg))).ennreal_ofReal
  have hprod_t : ∀ᵐ z ∂(P.prod ν), 0 < z.2 := by
    let s : Set (Ω × ℝ) := {z | z.2 ∈ Ioi (0 : ℝ)}
    have hright : ∀ᵐ x ∂P, ∀ᵐ y ∂ν, (x, y) ∈ s := by
      filter_upwards [] with x
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact hy
    simpa [s, Set.mem_Ioi] using ((Measure.ae_prod_mem_iff_ae_ae_mem (by dsimp [s]; exact measurableSet_preimage measurable_snd measurableSet_Ioi)).2 hright)
  have hFmono : ∀ᵐ z ∂(P.prod ν), Monotone (fun n => F n z) := by
    filter_upwards [hprod_t] with z ht
    intro i j hij
    change ENNReal.ofReal (z.2 ^ (q - 1) * Real.exp (-(mε i z.1 * z.2))) ≤
      ENNReal.ofReal (z.2 ^ (q - 1) * Real.exp (-(mε j z.1 * z.2)))
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (by dsimp [mε]; simpa [add_comm] using add_le_add_left (hεmono hij) (m z.1)) ht.le))) (Real.rpow_nonneg (le_of_lt ht) _))
  have hFlim : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 (Flim z)) := by
    intro z
    let g : ℝ → ℝ≥0∞ := fun x =>
      ENNReal.ofReal (z.2 ^ (q - 1) * Real.exp (-(x * z.2)))
    convert ((show Continuous g by change Continuous (fun x => ENNReal.ofReal (z.2 ^ (q - 1) * Real.exp (-(x * z.2)))); exact ENNReal.continuous_ofReal.comp (continuous_const.mul (Real.continuous_exp.comp ((continuous_id.mul continuous_const).neg)))).continuousAt.tendsto.comp (show Tendsto (fun n => mε n z.1) atTop (𝓝 (m z.1)) by simpa [mε] using (tendsto_const_nhds.add hεtend))) using 1
    funext n
    simp [F, g, mε]
  let R : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ t in Ioi (0 : ℝ), w t *
      (∫⁻ ω, ENNReal.ofReal (Real.exp (-(mε n ω * t))) ∂P) ∂volume
  let Rlim := ∫⁻ t in Ioi (0 : ℝ), w t *
      (∫⁻ ω, ENNReal.ofReal (Real.exp (-(m ω * t))) ∂P) ∂volume
  have hprodR n : ∫⁻ z, F n z ∂(P.prod ν) = R n := by
    have hf : AEMeasurable (Function.uncurry (fun ω t => F n (ω, t))) (P.prod ν) := by
      have hEq : Function.uncurry (fun ω t => F n (ω, t)) = F n := by
        funext z
        cases z
        rfl
      rw [hEq]
      exact hFmeas n
    have hfactor : ∀ᵐ t ∂ν,
        (∫⁻ ω, F n (ω, t) ∂P) = w t *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-(mε n ω * t))) ∂P) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [show (fun ω => F n (ω, t)) = fun ω => w t *
          ENNReal.ofReal (Real.exp (-(mε n ω * t))) by
        funext ω
        change ENNReal.ofReal (t ^ (q - 1) * Real.exp (-(mε n ω * t))) = _
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)] ]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    calc
      ∫⁻ z, F n z ∂(P.prod ν) = ∫⁻ ω, ∫⁻ t, F n (ω, t) ∂ν ∂P :=
        lintegral_prod _ hf
      _ = ∫⁻ t, ∫⁻ ω, F n (ω, t) ∂P ∂ν := by
        exact MeasureTheory.lintegral_lintegral_swap
          (f := fun ω t => F n (ω, t)) hf
      _ = R n := by
        simpa [R, ν] using (lintegral_congr_ae hfactor)
  have hprodRlim : ∫⁻ z, Flim z ∂(P.prod ν) = Rlim := by
    have hf : AEMeasurable (Function.uncurry (fun ω t => Flim (ω, t))) (P.prod ν) := by
      have hEq : Function.uncurry (fun ω t => Flim (ω, t)) = Flim := by
        funext z
        cases z
        rfl
      rw [hEq]
      exact (by exact ((show Measurable (fun z : Ω × ℝ => z.2 ^ (q - 1)) by fun_prop).aemeasurable.mul (Real.measurable_exp.comp_aemeasurable ((hmA.comp_fst.mul measurable_snd.aemeasurable).neg))).ennreal_ofReal)
    have hfactor : ∀ᵐ t ∂ν,
        (∫⁻ ω, Flim (ω, t) ∂P) = w t *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-(m ω * t))) ∂P) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [show (fun ω => Flim (ω, t)) = fun ω => w t *
          ENNReal.ofReal (Real.exp (-(m ω * t))) by
        funext ω
        change ENNReal.ofReal (t ^ (q - 1) * Real.exp (-(m ω * t))) = _
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)] ]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    calc
      ∫⁻ z, Flim z ∂(P.prod ν) = ∫⁻ ω, ∫⁻ t, Flim (ω, t) ∂ν ∂P :=
        lintegral_prod _ hf
      _ = ∫⁻ t, ∫⁻ ω, Flim (ω, t) ∂P ∂ν := by
        exact MeasureTheory.lintegral_lintegral_swap
          (f := fun ω t => Flim (ω, t)) hf
      _ = Rlim := by
        simpa [Rlim, ν] using (lintegral_congr_ae hfactor)
  have hformula n :
      ∫⁻ ω, L n ω ∂P = c * R n := by
    simpa [L, ψ, mε, c, R, w] using (finite_rpow_neg_lintegral_eq_weighted_laplace P (mε n) (fun ω => hmεpos n ω) (hmεA n) q hq)
  have hleftEq : ∫⁻ ω, Llim ω ∂P = c * ∫⁻ z, Flim z ∂(P.prod ν) :=
    tendsto_nhds_unique (lintegral_tendsto_of_tendsto_of_monotone (by intro n; exact hψcont.measurable.comp_aemeasurable (hmεA n)) (ae_of_all P fun ω => hLmono ω) (ae_of_all P (by intro ω; exact hψcont.continuousAt.tendsto.comp (by simpa [mε] using (tendsto_const_nhds.add hεtend))))) (by apply (show Tendsto (fun n => c * ∫⁻ z, F n z ∂(P.prod ν)) atTop (𝓝 (c * ∫⁻ z, Flim z ∂(P.prod ν))) by exact ENNReal.Tendsto.const_mul (lintegral_tendsto_of_tendsto_of_monotone hFmeas hFmono (ae_of_all (P.prod ν) hFlim)) (Or.inr ENNReal.ofReal_ne_top)).congr'; filter_upwards [] with n; rw [hformula n, hprodR n])
  rw [hprodRlim] at hleftEq
  simpa [Llim, ψ, c, Rlim, w, ν] using hleftEq


end DOZZ.Proofs
