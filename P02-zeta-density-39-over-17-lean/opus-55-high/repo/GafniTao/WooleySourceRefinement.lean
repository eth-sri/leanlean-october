module
public import GafniTao.WooleySection7Reverse
public import GafniTao.WooleySection7HardArithmetic
public import GafniTao.WooleyWeightedComplexHolder
public import GafniTao.WooleyResidueRefinement
import WeylPort.Analytic.RealLaplace

public section

/-!
# Source-sequence residue refinement

This is Wooley Lemma 6.2 on the actual finitely supported integer sequence.
It avoids an implicit change from integer-indexed source coefficients to the
older positive finite box: the residue partition and its normalization are
proved directly on `gamma.support`.
-/

open Finset

namespace GafniTao


theorem wooleySource_sum_refined_residue_mass
    {p a b : ℕ} [NeZero p] (hab : a ≤ b)
    (gamma : WooleySourceSequence) (xi : ZMod (p ^ a)) :
    ∑ z ∈ wooleyResidueRefinementFiber p a b hab xi,
        wooleySourceResidueMassSq gamma (p ^ b) z =
      wooleySourceResidueMassSq gamma (p ^ a) xi := by
  unfold wooleySourceResidueMassSq wooleyResidueRefinementFiber
  simp_rw [Finset.sum_filter]
  have hdistribute (z : ZMod (p ^ b)) :
      (if ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = xi then
          ∑ n ∈ gamma.support,
            if (n : ZMod (p ^ b)) = z then ‖gamma n‖ ^ 2 else 0
        else 0) =
        ∑ n ∈ gamma.support,
          if ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = xi then
            (if (n : ZMod (p ^ b)) = z then ‖gamma n‖ ^ 2 else 0)
          else 0 := by
    pm_2808
  pm_224 hdistribute Finset.sum_comm n hn
  pm_7204
  simp_all
  grind

theorem wooleySource_sum_refined_polynomialResidueSum
    {k p a b qB : ℕ} [NeZero p] [NeZero qB]
    (phi : WooleyPolynomialSystem k) (hab : a ≤ b)
    (gamma : WooleySourceSequence) (alpha : Fin k → ZMod qB)
    (xi : ZMod (p ^ a)) :
    ∑ z ∈ wooleyResidueRefinementFiber p a b hab xi,
        wooleySourcePolynomialResidueSum phi gamma alpha z =
      wooleySourcePolynomialResidueSum phi gamma alpha xi := by
  unfold wooleySourcePolynomialResidueSum wooleyResidueRefinementFiber
  simp_rw [Finset.sum_filter]
  have hdistribute (z : ZMod (p ^ b)) :
      (if ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = xi then
          ∑ n ∈ gamma.support,
            if (n : ZMod (p ^ b)) = z then
              gamma n * wooleySourcePolynomialPhase phi alpha n else 0
        else 0) =
        ∑ n ∈ gamma.support,
          if ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = xi then
            (if (n : ZMod (p ^ b)) = z then
              gamma n * wooleySourcePolynomialPhase phi alpha n else 0)
          else 0 := by
    pm_2808
  pm_224 hdistribute Finset.sum_comm n hn
  pm_7204
  · have hcast :
        ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a))
            (n : ZMod (p ^ b)) = (n : ZMod (p ^ a)) :=
      ZMod.cast_intCast (pow_dvd_pow p hab) n
    rw [hcast]
    by_cases hxi : (n : ZMod (p ^ a)) = xi <;> simp [hxi]
  grind

section
variable {k qH qB : ℕ} [NeZero qB] (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence) (alpha : Fin k → ZMod qB) (xi : ZMod qH)
include k qH qB phi gamma alpha xi
theorem wooleySourcePolynomialResidueSum_eq_zero_of_massSq_eq_zero
    (hmass : wooleySourceResidueMassSq gamma qH xi = 0) :
    wooleySourcePolynomialResidueSum phi gamma alpha xi = 0 := by
  have hterm : ∀ n ∈ gamma.support.filter
      (fun n : ℤ => (n : ZMod qH) = xi), ‖gamma n‖ ^ 2 = 0 := by
    pm_7483
    simpa [wooleySourceResidueMassSq] using hmass
  unfold wooleySourcePolynomialResidueSum
  pm_2835
  simp [hnzero]

theorem wooleySource_sqrt_mass_mul_normalizedResidueSum :
    (Real.sqrt (wooleySourceResidueMassSq gamma qH xi) : ℂ) *
        wooleySourceNormalizedPolynomialResidueSum phi gamma alpha xi =
      wooleySourcePolynomialResidueSum phi gamma alpha xi := by
  by_cases hmass : wooleySourceResidueMassSq gamma qH xi = 0
  · simp [wooleySourceNormalizedPolynomialResidueSum, hmass,
      wooleySourcePolynomialResidueSum_eq_zero_of_massSq_eq_zero
        phi gamma alpha xi hmass]
  · have hmassPos : 0 < wooleySourceResidueMassSq gamma qH xi :=
      lt_of_le_of_ne (wooleySourceResidueMassSq_nonneg gamma qH xi)
        (Ne.symm hmass)
    simp [wooleySourceNormalizedPolynomialResidueSum, hmass,
      Real.sqrt_ne_zero'.mpr hmassPos]
end

theorem wooleySource_refined_normalized_residue_decomposition
    {k p a b qB : ℕ} [NeZero p] [NeZero qB]
    (phi : WooleyPolynomialSystem k) (hab : a ≤ b)
    (gamma : WooleySourceSequence) (alpha : Fin k → ZMod qB)
    (xi : ZMod (p ^ a)) :
    (Real.sqrt (wooleySourceResidueMassSq gamma (p ^ a) xi) : ℂ) *
        wooleySourceNormalizedPolynomialResidueSum phi gamma alpha xi =
      ∑ z ∈ wooleyResidueRefinementFiber p a b hab xi,
        (Real.sqrt (wooleySourceResidueMassSq gamma (p ^ b) z) : ℂ) *
          wooleySourceNormalizedPolynomialResidueSum phi gamma alpha z := by
  rw [wooleySource_sqrt_mass_mul_normalizedResidueSum phi gamma alpha]
  simp_rw [wooleySource_sqrt_mass_mul_normalizedResidueSum phi gamma alpha]
  exact (wooleySource_sum_refined_polynomialResidueSum
    phi hab gamma alpha xi).symm

/-- Wooley Lemma 6.2 on the literal source sequence. -/
theorem wooleySourcePolynomial_lemma_6_2
    {k p a b qB w : ℕ} [NeZero p] [NeZero qB]
    (phi : WooleyPolynomialSystem k) (hab : a ≤ b) (hw : 1 ≤ w)
    (gamma : WooleySourceSequence) (alpha : Fin k → ZMod qB)
    (xi : ZMod (p ^ a)) :
    wooleySourceResidueMassSq gamma (p ^ a) xi *
        ‖wooleySourceNormalizedPolynomialResidueSum
            phi gamma alpha xi‖ ^ (2 * w) ≤
      (p ^ (b - a) : ℝ) ^ w *
        ∑ z ∈ wooleyResidueRefinementFiber p a b hab xi,
          wooleySourceResidueMassSq gamma (p ^ b) z *
            ‖wooleySourceNormalizedPolynomialResidueSum
                phi gamma alpha z‖ ^ (2 * w) := by
  let M := wooleySourceResidueMassSq gamma (p ^ a) xi
  let R : ℝ :=
    ∑ z ∈ wooleyResidueRefinementFiber p a b hab xi,
      wooleySourceResidueMassSq gamma (p ^ b) z *
        ‖wooleySourceNormalizedPolynomialResidueSum
          phi gamma alpha z‖ ^ (2 * w)
  by_cases hMzero : M = 0
  · have hR : 0 ≤ R := by
      dsimp [R]
      exact Finset.sum_nonneg fun z hz => mul_nonneg
        (wooleySourceResidueMassSq_nonneg gamma (p ^ b) z) (by positivity)
    pm_6041
  · have hMpos : 0 < M := lt_of_le_of_ne
      (wooleySourceResidueMassSq_nonneg gamma (p ^ a) xi)
      (Ne.symm hMzero)
    have hholder := wooley_weighted_complex_sum_pow_le
      (wooleyResidueRefinementFiber p a b hab xi)
      (fun z => wooleySourceResidueMassSq gamma (p ^ b) z)
      (fun z => wooleySourceNormalizedPolynomialResidueSum
        phi gamma alpha z) hw
      (fun z => wooleySourceResidueMassSq_nonneg gamma (p ^ b) z)
    have hdecomp := wooleySource_refined_normalized_residue_decomposition
      phi hab gamma alpha xi
    have hsource :
        M ^ w *
            ‖wooleySourceNormalizedPolynomialResidueSum
                phi gamma alpha xi‖ ^ (2 * w) ≤
          (p ^ (b - a) : ℝ) ^ w * M ^ (w - 1) * R := by
      pm_2855 wooleySource_sum_refined_residue_mass
    pm_2854
    have hfactored :
        M ^ (w - 1) *
            (M * ‖wooleySourceNormalizedPolynomialResidueSum
              phi gamma alpha xi‖ ^ (2 * w)) ≤
          M ^ (w - 1) * ((p ^ (b - a) : ℝ) ^ w * R) := by
      rw [← mul_assoc, ← hpow]
      calc
        M ^ w *
            ‖wooleySourceNormalizedPolynomialResidueSum
                phi gamma alpha xi‖ ^ (2 * w) ≤
            (p ^ (b - a) : ℝ) ^ w * M ^ (w - 1) * R := hsource
        _ = M ^ (w - 1) * ((p ^ (b - a) : ℝ) ^ w * R) := by ring
    exact le_of_mul_le_mul_left hfactored hfactorPos

/-- Equation (7.22), with `H'` and `b'` the literal Section 7 depths. -/
theorem wooley_equation_7_22_native
    {k p r a b nu gammaVal B : ℕ} [NeZero p] [NeZero (p ^ B)]
    (hr : 1 ≤ r)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gammaVal)
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (alpha : Fin k → ZMod (p ^ B))
    (kappa : ZMod (p ^ (a + wooleySection7HPrime k r a b gammaVal))) :
    wooleySourceResidueMassSq gamma
          (p ^ (a + wooleySection7HPrime k r a b gammaVal)) kappa *
        ‖wooleySourceNormalizedPolynomialResidueSum
            phi gamma alpha kappa‖ ^ (2 * wooleyTriangular r) ≤
      (p ^ (wooleySection7NextB k r b -
          (a + wooleySection7HPrime k r a b gammaVal)) : ℝ) ^
          wooleyTriangular r *
        ∑ xiPrime ∈ wooleyResidueRefinementFiber p
            (a + wooleySection7HPrime k r a b gammaVal)
            (wooleySection7NextB k r b)
            (wooley_section7_a_add_HPrime_le_nextB hr hBPrime) kappa,
          wooleySourceResidueMassSq gamma
              (p ^ wooleySection7NextB k r b) xiPrime *
            ‖wooleySourceNormalizedPolynomialResidueSum
                phi gamma alpha xiPrime‖ ^ (2 * wooleyTriangular r) := by
  exact wooleySourcePolynomial_lemma_6_2 phi
    (wooley_section7_a_add_HPrime_le_nextB hr hBPrime)
    (by
      unfold wooleyTriangular
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
      nlinarith) gamma alpha kappa



end GafniTao
