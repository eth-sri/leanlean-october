/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import CCDN.AuxiliaryPolynomial.HypersurfaceRankProfile
import CCDN.ForMathlib.Log
public import CCDN.AuxiliaryPolynomial.HypersurfaceRankRoots
public import CCDN.Determinant.HypersurfaceDeterminantRank
public import CCDN.Plane.IntegerPlaneLogHeight
import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeCoordinates
import CCDN.Determinant.HomogeneousDeterminantComparison

/-! Compare the archimedean minor bound with local divisibility, keeping the exact
Hilbert rank and the bad-prime charge. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The dimension-dependent error term in the normalized no-auxiliary comparison that retains
the bad-prime charge, for forms in `n + 3` variables: the determinant error plus the
archimedean error normalized by $(n + 2) / ((n + 1)!)^{1/(n + 1)}$. -/
def hypersurfaceBadPrimeNormalizedError (n : ℕ) : ℝ :=
  hypersurfaceDeterminantError n +
    (n + 2 : ℝ) * (n + 1 : ℝ) /
      ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ))

/-- The bound on the bad-prime charge in terms of coefficient height. -/
abbrev hypersurfaceHeightChargeBound (n d : ℕ) (H : ℝ) : ℝ :=
  Real.log (hypersurfaceHeightConstant (n + 3) * (1 + Real.log H / (d : ℝ) ^ 2)) +
    2 * mertensError + 1

/-- Error in the normalized comparison after bounding the charge by height. -/
def hypersurfaceNormalizedError (n : ℕ) : ℝ :=
  hypersurfaceBadPrimeNormalizedError n +
    (n + 1 : ℝ) * (Real.log (hypersurfaceHeightConstant (n + 3)) + 2 * mertensError + 1)

/-- Divide the determinant bounds by the rank after absorbing the factorial. -/
private theorem hypersurface_rank_comparison_normalized {r d M : ℕ}
    (hr : 0 < r) (hd : 0 < d) (hdM : d ≤ M) (B L c E : ℝ) :
    let s := hypersurfaceRank (r + 1) d M
    (hcomparison : (r.factorial : ℝ) ^ (1 / (r : ℝ)) / (r + 1 : ℝ) *
        (s : ℝ) ^ (1 + 1 / (r : ℝ)) *
          (Real.log s - r * (4 * Real.log d + c) - E) ≤
      Real.log (s.factorial : ℝ) + s * M * Real.log B -
        ((r + 1 + (M - d)).choose (M - d) : ℝ) * Real.log L) →
    NormalizedRankComparison r d M (Real.log B) (Real.log L) c
      (E + (r + 1 : ℝ) * r / (r.factorial : ℝ) ^ (1 / (r : ℝ))) := by
  intro s hcomparison
  have hs : 0 < s := hypersurface_rank_pos hdM hd
  have hs0 : (0 : ℝ) < s := by positivity
  have hr0 : (0 : ℝ) < r := by positivity
  let F := (r.factorial : ℝ) ^ (1 / (r : ℝ))
  let S := (s : ℝ) ^ (1 / (r : ℝ))
  let T := Real.log s - r * (4 * Real.log d + c) - E
  have hF : F ≠ 0 := by positivity
  
  have hf := Real.log_factorial_le_mul_rpow s (one_div_pos.mpr hr0)
  rw [div_div_eq_mul_div, div_one] at hf
  rw [Real.rpow_add hs0, Real.rpow_one] at hcomparison
  change F / (r + 1) * (s * S) * T ≤ _ at hcomparison
  delta NormalizedRankComparison
  dsimp only
  rw [← sub_sub]
  change F * S * (T - (r + 1) * r / F) ≤ (r + 1 : ℝ) *
    (M * Real.log B - ((r + 1 + (M - d)).choose (M - d) : ℝ) / s * Real.log L)
  apply le_of_mul_le_mul_right _ (show 0 < (s : ℝ) / (r + 1) by positivity)
  convert (show F / (r + 1) * (s * S) * T - s * (S * r) ≤
    s * M * Real.log B - ((r + 1 + (M - d)).choose (M - d) : ℝ) * Real.log L by
      linarith only [hcomparison, hf]) using 1 <;> field_simp

/-- The normalized no-auxiliary comparison with the charge of a finite prime set `bad`:
for every radius `B ≥ 1` bounding the points `z` and every degree `M ≥ d` in which each
form vanishing on `z` is a multiple of `f`, the rank `s` of the evaluation matrix
satisfies the normalized comparison retaining `log b = ∑ p ∈ bad, log p / p`. -/
def AuxiliaryRankComparison {n t : ℕ} (order : MonomialOrder (Fin (n + 3)))
    (f : MvPolynomial (Fin (n + 3)) ℤ) (d : ℕ) (z : Fin t → IntPoint (n + 3))
    (bad : Finset ℕ) : Prop :=
  ∀ ⦃B : ℝ⦄, 1 ≤ B → (∀ i, InBox (z i) B) → ∀ ⦃M : ℕ⦄, d ≤ M →
    (∀ g : MvPolynomial (Fin (n + 3)) ℤ, g.IsHomogeneous M → (∀ i, eval (z i) g = 0) → f ∣ g) →
    NormalizedRankComparison (n + 1) d M (Real.log B)
        (Real.log |((order.leadingCoeff f : ℤ) : ℝ)|) (∑ p ∈ bad, Real.log p / p)
        (hypersurfaceBadPrimeNormalizedError n)

/-- The comparison retaining `log b(f)` for the exact geometric bad-prime set, rather
than bounding it in terms of height. -/
theorem hypersurface_auxiliaryRankComparison {n d t : ℕ}
    (order : MonomialOrder (Fin (n + 3))) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d)
    (z : Fin t → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0) (bad : Finset ℕ)
    (hbad : ∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction f p) :
    AuxiliaryRankComparison order f d z bad := by
  intro B hB hbox M hdM hrel
  obtain ⟨a, hi, hupper⟩ :=
    homogeneous_no_auxiliary_box_comparison order f hf hf0 hdM z hz hB hbox hrel
  have hs := hypersurface_rank_pos (r := n + 1) hdM hd
  let F := fun j => (monomial (homogeneousMonomials (n + 2) M j) 1 : MvPolynomial (Fin (n + 3)) ℤ)
  have hF : ∀ j, (F j).IsHomogeneous M := fun j =>
    isHomogeneous_monomial _ (homogeneousMonomials_degree (n + 2) M j)
  have he : (Matrix.of fun i j => eval ((z ∘ a) i) (F j)) =
      evaluationMatrix (homogeneousMonomials (n + 2) M) (z ∘ a) :=
    evaluationMatrix_eq_eval _ _
  have hlower := hypersurface_determinant_log_lower_at_rank (z := z ∘ a) hs f hf hd
    ⟨hF, fun i => hprim (a i), fun i => hz (a i), by rwa [he]⟩ bad hbad
    ∅ (by simp) 0 (by simp)
  simp only [he, Finset.union_empty, CharP.cast_eq_zero, zero_mul, add_zero, Finset.sum_empty] at hlower
  have hc := hlower.trans hupper
  have hnN : n + 1 + 1 = n + 2 := by omega
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  have hh := hypersurface_rank_comparison_normalized (r := n + 1) (by omega) hd hdM
    B |((order.leadingCoeff f : ℤ) : ℝ)| (∑ p ∈ bad, Real.log p / p)
    (hypersurfaceDeterminantError n)
    (by simpa only [hypersurfaceRankLowerBound, hnN, Nat.cast_add, Nat.cast_one, hnR,
      Real.log_exp] using hc)
  simpa only [hypersurfaceBadPrimeNormalizedError, Nat.cast_add, Nat.cast_one, hnR] using hh

end
end CCDN
