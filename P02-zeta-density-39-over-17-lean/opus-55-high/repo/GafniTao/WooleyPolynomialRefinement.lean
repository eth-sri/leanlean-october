module
public import GafniTao.WooleyPolynomialBasic
public import GafniTao.WooleyResidueRefinement
import WeylPort.Analytic.RealLaplace

public section

/-!
# Residue refinement for polynomial systems

The residue-class argument in Wooley Lemma 6.2 is independent of the
particular polynomial phase.  This file proves it for the `p^c`-spaced
systems used by the induction in Section 7.
-/

open Finset

namespace GafniTao


section
variable {Q p a b qB k : ℕ} [NeZero p] [NeZero qB] (phi : WooleyPolynomialSystem k) (hab : a ≤ b) (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod qB) (xi : ZMod (p ^ a))
include Q p a b qB k phi hab gamma alpha xi
theorem wooleyPolynomial_sum_refined_residue_grid :
    ∑ z ∈ wooleyResidueRefinementFiber p a b hab xi,
        wooleyPolynomialWeightedResidueGridSum phi qB gamma alpha z =
      wooleyPolynomialWeightedResidueGridSum phi qB gamma alpha xi := by
  unfold wooleyPolynomialWeightedResidueGridSum wooleyResidueClass
    wooleyResidueRefinementFiber
  simp_rw [Finset.sum_filter]
  have hdistribute (z : ZMod (p ^ b)) :
      (if ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = xi then
          ∑ n : Fin Q,
            if ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ b))) = z then
              gamma n * wooleyPolynomialGridPhase phi qB Q alpha n else 0
        else 0) =
        ∑ n : Fin Q,
          if ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = xi then
            (if ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ b))) = z then
              gamma n * wooleyPolynomialGridPhase phi qB Q alpha n else 0)
          else 0 := by
    simp_all
  pm_2845
  grind

theorem wooleyPolynomial_refined_normalized_residue_decomposition :
    (Real.sqrt (wooleyWeightedResidueMassSq gamma xi) : ℂ) *
        wooleyPolynomialNormalizedResidueGridSum phi qB gamma alpha xi =
      ∑ z ∈ wooleyResidueRefinementFiber p a b hab xi,
        (Real.sqrt (wooleyWeightedResidueMassSq gamma z) : ℂ) *
          wooleyPolynomialNormalizedResidueGridSum phi qB gamma alpha z := by
  rw [wooleyPolynomial_sqrt_mass_mul_normalizedResidueGridSum
    phi gamma alpha]
  simp_rw [wooleyPolynomial_sqrt_mass_mul_normalizedResidueGridSum
    phi gamma alpha]
  exact (wooleyPolynomial_sum_refined_residue_grid
    phi hab gamma alpha xi).symm
end

/-- Polynomial-system form of Wooley Lemma 6.2. -/
theorem wooleyPolynomial_lemma_6_2
    {Q p a b qB k w : ℕ} [NeZero p] [NeZero qB]
    (phi : WooleyPolynomialSystem k) (hab : a ≤ b) (hw : 1 ≤ w)
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod qB)
    (xi : ZMod (p ^ a)) :
    wooleyWeightedResidueMassSq gamma xi *
        ‖wooleyPolynomialNormalizedResidueGridSum
            phi qB gamma alpha xi‖ ^ (2 * w) ≤
      (p ^ (b - a) : ℝ) ^ w *
        ∑ z ∈ wooleyResidueRefinementFiber p a b hab xi,
          wooleyWeightedResidueMassSq gamma z *
            ‖wooleyPolynomialNormalizedResidueGridSum
                phi qB gamma alpha z‖ ^ (2 * w) := by
  let M := wooleyWeightedResidueMassSq gamma xi
  let R : ℝ :=
    ∑ z ∈ wooleyResidueRefinementFiber p a b hab xi,
      wooleyWeightedResidueMassSq gamma z *
        ‖wooleyPolynomialNormalizedResidueGridSum
            phi qB gamma alpha z‖ ^ (2 * w)
  by_cases hMzero : M = 0
  · have hR : 0 ≤ R := by
      dsimp [R]
      exact Finset.sum_nonneg fun z hz => mul_nonneg
        (wooleyWeightedResidueMassSq_nonneg gamma z) (by positivity)
    pm_6041
  · have hMpos : 0 < M := lt_of_le_of_ne
      (wooleyWeightedResidueMassSq_nonneg gamma xi) (Ne.symm hMzero)
    have hholder := wooley_weighted_complex_sum_pow_le
      (wooleyResidueRefinementFiber p a b hab xi)
      (fun z => wooleyWeightedResidueMassSq gamma z)
      (fun z => wooleyPolynomialNormalizedResidueGridSum
        phi qB gamma alpha z) hw
      (fun z => wooleyWeightedResidueMassSq_nonneg gamma z)
    have hdecomp :=
      wooleyPolynomial_refined_normalized_residue_decomposition
        phi hab gamma alpha xi
    have hsource :
        M ^ w *
            ‖wooleyPolynomialNormalizedResidueGridSum
                phi qB gamma alpha xi‖ ^ (2 * w) ≤
          (p ^ (b - a) : ℝ) ^ w * M ^ (w - 1) * R := by
      pm_2855 wooley_sum_refined_residue_mass
    pm_2854
    have hfactored :
        M ^ (w - 1) *
            (M * ‖wooleyPolynomialNormalizedResidueGridSum
              phi qB gamma alpha xi‖ ^ (2 * w)) ≤
          M ^ (w - 1) * ((p ^ (b - a) : ℝ) ^ w * R) := by
      rw [← mul_assoc, ← hpow]
      calc
        M ^ w *
            ‖wooleyPolynomialNormalizedResidueGridSum
                phi qB gamma alpha xi‖ ^ (2 * w) ≤
            (p ^ (b - a) : ℝ) ^ w * M ^ (w - 1) * R := hsource
        _ = M ^ (w - 1) * ((p ^ (b - a) : ℝ) ^ w * R) := by ring
    exact le_of_mul_le_mul_left hfactored hfactorPos



end GafniTao
