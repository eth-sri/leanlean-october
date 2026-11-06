/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsCenteredJointlyGaussian
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Exponential integrability for finite linear forms of a Gaussian vector. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal

namespace DOZZ.Proofs


/-- The exponential of a weighted sum of absolute Gaussian coordinates is integrable.
The proof dominates it by the finite sum over all sign choices of Gaussian linear exponentials. -/
theorem centeredJointlyGaussian_abs_linear_exp_integrable
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) Z
    (hZ : DOZZ.IsCenteredJointlyGaussian P Z) (c : ι → ℝ) :
    Integrable (fun ω => Real.exp (∑ i, c i * |Z ω i|)) P := by
  classical
  have centeredJointlyGaussian_linear_exp_integrable (a : ι → ℝ) t : Integrable (fun ω => Real.exp (t * ∑ i, a i * Z ω i)) P := by
    obtain ⟨hLmem, ⟨v, hLmap⟩⟩ := hZ.2.2 a
    let L : Ω → ℝ := fun ω => ∑ i, a i * Z ω i
    have hExpMap : Integrable (fun x => Real.exp (t * x)) (P.map L) := by
      rw [(show P.map L = gaussianReal 0 v by simpa [L] using hLmap)]
      exact integrable_exp_mul_gaussianReal t
    simpa [L] using (by simpa only [Function.comp_def] using (integrable_map_measure hExpMap.aestronglyMeasurable (by simpa [L] using hLmem.aemeasurable)).mp hExpMap)
  let G : (ι → Bool) → Ω → ℝ := fun s ω =>
    Real.exp (∑ i, (if s i then c i else -c i) * Z ω i)
  have hG s : Integrable (G s) P := by
    simpa [G] using centeredJointlyGaussian_linear_exp_integrable
      (fun i => if s i then c i else -c i) 1
  have hpoint ω : Real.exp (∑ i, c i * |Z ω i|) ≤ ∑ s : ι → Bool, G s ω := by
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
  exact (integrable_finsetSum Finset.univ (fun s hs => hG s)).mono' (Real.continuous_exp.comp_aestronglyMeasurable (by simpa only [Finset.sum_apply] using (Finset.univ.aestronglyMeasurable_fun_sum (fun i hi => (fun i => (continuous_abs.comp_aestronglyMeasurable (hZ.2.1 i).aestronglyMeasurable).const_mul (c i)) i)))) (ae_of_all P (fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]; exact hpoint ω))

/-- A Gaussian coordinate times an exponential of a weighted absolute-coordinate sum is
integrable. This is the uniform derivative envelope for smooth interpolation tests. -/
theorem centeredJointlyGaussian_coordinate_mul_abs_linear_exp_integrable
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) Z
    (hZ : DOZZ.IsCenteredJointlyGaussian P Z) (c : ι → ℝ) i :
    Integrable (fun ω => Z ω i * Real.exp (∑ j, c j * |Z ω j|)) P := by
  have hExpMem : MemLp (fun ω => Real.exp (∑ j, c j * |Z ω j|)) 2 P := by
    apply (memLp_two_iff_integrable_sq (Real.continuous_exp.comp_aestronglyMeasurable (by simpa only [Finset.sum_apply] using (Finset.univ.aestronglyMeasurable_fun_sum (fun j hj => (fun j => (continuous_abs.comp_aestronglyMeasurable (hZ.2.1 j).aestronglyMeasurable).const_mul (c j)) j))))).2
    have hsq ω :
        Real.exp (∑ j, c j * |Z ω j|) ^ 2 =
          Real.exp (2 * ∑ j, c j * |Z ω j|) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    exact (show Integrable (fun ω => Real.exp (2 * ∑ j, c j * |Z ω j|)) P by exact (centeredJointlyGaussian_abs_linear_exp_integrable P Z hZ (fun j => 2 * c j)).congr (ae_of_all P fun ω => congrArg Real.exp ((fun (ω : Ω) => by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; ring) ω))).congr (ae_of_all P fun ω => (hsq ω).symm)
  have hZiMem : MemLp (fun ω => Z ω i) 2 P := by
    obtain ⟨hmem, _⟩ := hZ.2.2 (fun j => if j = i then 1 else 0)
    rw [← (show (fun ω => ∑ j, (if j = i then 1 else 0) * Z ω j) = fun ω => Z ω i by funext ω; simp)]
    exact hmem
  have hHolder : ENNReal.HolderTriple 2 2 1 := ⟨by
    simpa using ENNReal.inv_two_add_inv_two⟩
  exact memLp_one_iff_integrable.mp (by convert (hZiMem.mul hExpMem (hpqr := hHolder)) using 1)

end DOZZ.Proofs
