/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Statements.GMC.IsCenteredJointlyGaussian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Exponential integrability for finite linear forms of a Gaussian vector. -/


open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal

namespace DOZZ.Proofs

/-- Every real exponential of a finite linear form of a centered jointly Gaussian family is
integrable. -/
theorem centeredJointlyGaussian_linear_exp_integrable
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : IsCenteredJointlyGaussian P Z) (a : ι → ℝ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * ∑ i, a i * Z ω i)) P := by
  obtain ⟨hLmem, ⟨v, hLmap⟩⟩ := hZ.2.2 a
  let L : Ω → ℝ := fun ω => ∑ i, a i * Z ω i
  have hLmap' : P.map L = gaussianReal 0 v := by
    simpa [L] using hLmap
  have hLmeas : AEMeasurable L P := by
    simpa [L] using hLmem.aemeasurable
  have hExpMap : Integrable (fun x : ℝ => Real.exp (t * x)) (P.map L) := by
    rw [hLmap']
    exact integrable_exp_mul_gaussianReal t
  have hExp : Integrable (fun ω => Real.exp (t * L ω)) P := by
    simpa [Function.comp_def] using
      (integrable_map_measure hExpMap.aestronglyMeasurable hLmeas).mp hExpMap
  simpa [L] using hExp

/-- The exponential of a weighted sum of absolute Gaussian coordinates is integrable.
The proof dominates it by the finite sum over all sign choices of Gaussian linear exponentials. -/
theorem centeredJointlyGaussian_abs_linear_exp_integrable
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : IsCenteredJointlyGaussian P Z) (c : ι → ℝ) :
    Integrable (fun ω => Real.exp (∑ i, c i * |Z ω i|)) P := by
  classical
  let G : (ι → Bool) → Ω → ℝ := fun s ω =>
    Real.exp (∑ i, (if s i then c i else -c i) * Z ω i)
  have hG (s : ι → Bool) : Integrable (G s) P := by
    simpa [G] using centeredJointlyGaussian_linear_exp_integrable P Z hZ
      (fun i => if s i then c i else -c i) 1
  have hsum : Integrable (fun ω => ∑ s : ι → Bool, G s ω) P := integrable_finsetSum Finset.univ (fun s hs => hG s)
  have hpoint (ω : Ω) : Real.exp (∑ i, c i * |Z ω i|) ≤ ∑ s : ι → Bool, G s ω := by
    let sω : ι → Bool := fun i => decide (0 ≤ Z ω i)
    have hlinear : (∑ i, c i * |Z ω i|) =
        ∑ i, (if sω i then c i else -c i) * Z ω i := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : 0 ≤ Z ω i
      · simp [sω, h, abs_of_nonneg h]
      · have hneg : Z ω i < 0 := lt_of_not_ge h
        simp [sω, h, abs_of_neg hneg]
    calc
      Real.exp (∑ i, c i * |Z ω i|) =
          Real.exp (∑ i, (if sω i then c i else -c i) * Z ω i) := by rw [hlinear]
      _ = G sω ω := by simp [G]
      _ ≤ ∑ s : ι → Bool, G s ω := by
        exact Finset.single_le_sum
          (f := fun s : ι → Bool => G s ω) (s := Finset.univ)
          (fun s hs => Real.exp_nonneg _) (Finset.mem_univ sω)
  have hterm (i : ι) : AEStronglyMeasurable
      (fun ω => c i * |Z ω i|) P := by
    exact (continuous_abs.comp_aestronglyMeasurable
      (hZ.2.1 i).aestronglyMeasurable).const_mul (c i)
  have harg : AEStronglyMeasurable
      (fun ω => ∑ i, c i * |Z ω i|) P := by
    simpa [Finset.sum_apply] using
      (Finset.univ.aestronglyMeasurable_fun_sum (fun i hi => hterm i))
  have hf : AEStronglyMeasurable
      (fun ω => Real.exp (∑ i, c i * |Z ω i|)) P := by
    exact Real.continuous_exp.comp_aestronglyMeasurable harg
  have hpointNorm (ω : Ω) :
      ‖Real.exp (∑ i, c i * |Z ω i|)‖ ≤ ∑ s : ι → Bool, G s ω := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact hpoint ω
  exact hsum.mono' hf (ae_of_all P hpointNorm)

/-- A Gaussian coordinate times an exponential of a weighted absolute-coordinate sum is
integrable. This is the uniform derivative envelope for smooth interpolation tests. -/
theorem centeredJointlyGaussian_coordinate_mul_abs_linear_exp_integrable
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : IsCenteredJointlyGaussian P Z) (c : ι → ℝ) (i : ι) :
    Integrable (fun ω => Z ω i * Real.exp (∑ j, c j * |Z ω j|)) P := by
  have hArg : AEStronglyMeasurable
      (fun ω => ∑ j, c j * |Z ω j|) P := by
    have hterm (j : ι) : AEStronglyMeasurable
        (fun ω => c j * |Z ω j|) P := by
      exact (continuous_abs.comp_aestronglyMeasurable
        (hZ.2.1 j).aestronglyMeasurable).const_mul (c j)
    simpa [Finset.sum_apply] using
      (Finset.univ.aestronglyMeasurable_fun_sum (fun j hj => hterm j))
  have hExpMeas : AEStronglyMeasurable
      (fun ω => Real.exp (∑ j, c j * |Z ω j|)) P :=
    Real.continuous_exp.comp_aestronglyMeasurable hArg
  have hExpSq : Integrable
      (fun ω => Real.exp (2 * ∑ j, c j * |Z ω j|)) P := by
    have hdouble := centeredJointlyGaussian_abs_linear_exp_integrable P Z hZ
      (fun j => 2 * c j)
    have hsum (ω : Ω) :
        (∑ j, 2 * c j * |Z ω j|) = 2 * ∑ j, c j * |Z ω j| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    exact hdouble.congr (ae_of_all P fun ω => congrArg Real.exp (hsum ω))
  have hExpMem : MemLp (fun ω => Real.exp (∑ j, c j * |Z ω j|)) 2 P := by
    apply (memLp_two_iff_integrable_sq hExpMeas).2
    have hsq (ω : Ω) :
        Real.exp (∑ j, c j * |Z ω j|) ^ 2 =
          Real.exp (2 * ∑ j, c j * |Z ω j|) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    exact hExpSq.congr (ae_of_all P fun ω => (hsq ω).symm)
  have hZiMem : MemLp (fun ω => Z ω i) 2 P := by
    obtain ⟨hmem, _⟩ := hZ.2.2 (fun j => if j = i then 1 else 0)
    have hEq : (fun ω => ∑ j, (if j = i then 1 else 0) * Z ω j) =
        fun ω => Z ω i := by
      funext ω
      simp
    rwa [← hEq]
  have hHolder : ENNReal.HolderTriple 2 2 1 := ⟨by
    simpa using ENNReal.inv_two_add_inv_two⟩
  have hprod := hZiMem.mul hExpMem (hpqr := hHolder)
  exact memLp_one_iff_integrable.mp (by convert hprod using 1)

end DOZZ.Proofs
