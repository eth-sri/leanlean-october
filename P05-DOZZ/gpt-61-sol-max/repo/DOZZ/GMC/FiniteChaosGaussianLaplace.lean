/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.KahaneConvexOrderClosure
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Finite Gaussian Laplace comparison as a direct corollary of convex order. -/

public section

open MeasureTheory ProbabilityTheory
open scoped Distributions Topology

namespace DOZZ.Proofs

/-- The Laplace test is convex. An affine shift of the masses permits the convex-order
criterion to cover zero weights and empty families without a separate argument. -/
theorem kahane_finite_laplace_lintegral
    {ΩX ΩY : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] {ι : Type*} [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X)
    (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ s : ℝ) (hs : 0 ≤ s)
    (hcov : ∀ i j, DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-s * DOZZ.finiteChaosMass PX X a γ ω)) ∂PX ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-s * DOZZ.finiteChaosMass PY Y a γ ω)) ∂PY := by
  classical
  let := hX.1
  let := hY.1
  have hn (P : Measure ΩX) (Z : ΩX → ι → ℝ) (ω : ΩX) :
      0 ≤ DOZZ.finiteChaosMass P Z a γ ω :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (Real.exp_nonneg _))
  have hnY (ω : ΩY) : 0 ≤ DOZZ.finiteChaosMass PY Y a γ ω :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (Real.exp_nonneg _))
  obtain ⟨hMX, hmeanX⟩ := finiteChaosMass_integral PX X hX a γ
  obtain ⟨hMY, hmeanY⟩ := finiteChaosMass_integral PY Y hY a γ
  let MX := fun ω => DOZZ.finiteChaosMass PX X a γ ω + 1
  let MY := fun ω => DOZZ.finiteChaosMass PY Y a γ ω + 1
  let F := fun x : ℝ => Real.exp (-s * (x - 1))
  have hF : Measurable F := by fun_prop
  have hconv : ConvexOn ℝ (Set.Ici 0) F := by
    have h := convexOn_exp.comp_affineMap
      (ContinuousAffineMap.toAffineMap ((-s) • ContinuousAffineMap.id ℝ ℝ +
        ContinuousAffineMap.const ℝ ℝ s))
    simpa [F, Function.comp_def, mul_sub] using h.subset (Set.subset_univ _) (convex_Ici 0)
  have hIY : Integrable (fun ω => F (MY ω)) PY := by
    apply Integrable.of_bound (hF.comp_aemeasurable (hMY.add (integrable_const 1)).aemeasurable).aestronglyMeasurable 1
    exact ae_of_all _ fun ω => by
      simp only [Function.comp_def, F, Pi.add_apply, add_sub_cancel_right, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (hnY ω))
  have horder (n : ℕ) (c d : Fin (n + 1) → ℝ) :
      (∫ ω, affineMax c d (MX ω) ∂PX) ≤ ∫ ω, affineMax c d (MY ω) ∂PY := by
    have heq (x : ℝ) : affineMax c d (x + 1) = affineMax c (fun i => c i + d i) x := by
      unfold affineMax
      congr 1
      funext i
      ring
    simpa only [MX, MY, heq] using kahane_finite_affine_max PX PY X Y hX hY a ha γ
      c (fun i => c i + d i) hcov
  obtain ⟨hIX, hle⟩ := convex_comparison_of_affine_max_order PX PY MX MY
    (hMX.add (integrable_const 1)) (hMY.add (integrable_const 1))
    (ae_of_all _ fun ω => by dsimp [MX]; linarith only [hn PX X ω])
    (ae_of_all _ fun ω => by dsimp [MY]; linarith only [hnY ω])
    (by simp [MX, MY, integral_add hMX (integrable_const 1),
      integral_add hMY (integrable_const 1), hmeanX, hmeanY])
    horder F hF hconv hIY
  simpa only [F, MX, MY, add_sub_cancel_right] using
    (show (∫⁻ ω, ENNReal.ofReal (F (MX ω)) ∂PX) ≤
        ∫⁻ ω, ENNReal.ofReal (F (MY ω)) ∂PY from by
      rw [← ofReal_integral_eq_lintegral_ofReal hIX (ae_of_all _ fun _ => Real.exp_nonneg _),
        ← ofReal_integral_eq_lintegral_ofReal hIY (ae_of_all _ fun _ => Real.exp_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hle)

end DOZZ.Proofs
