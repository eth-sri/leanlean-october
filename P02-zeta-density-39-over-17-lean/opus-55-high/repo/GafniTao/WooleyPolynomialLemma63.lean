module
public import GafniTao.WooleyPolynomialInitial
import WeylPort.Analytic.RealLaplace

public section

/-!
# Polynomial-system form of Wooley Lemma 6.3

Both residue factors are refined by the polynomial version of Lemma 6.2.
The proof is phase-independent, but its conclusion is stated in the literal
mixed means used by the Section 7 induction.
-/

open Finset

namespace GafniTao


theorem wooleyPolynomial_mixed_one_point_refinement
    {Q p nu theta qB k s : ℕ} [NeZero p] [NeZero qB]
    (phi : WooleyPolynomialSystem k) (hnu : nu ≤ theta) (hs : 2 ≤ s)
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod qB)
    (xi eta : ZMod (p ^ nu)) :
    wooleyWeightedResidueMassSq gamma xi *
        wooleyWeightedResidueMassSq gamma eta *
        (‖wooleyPolynomialNormalizedResidueGridSum
            phi qB gamma alpha xi‖ ^ 2 *
          ‖wooleyPolynomialNormalizedResidueGridSum
            phi qB gamma alpha eta‖ ^ (2 * (s - 1))) ≤
      (p ^ (theta - nu) : ℝ) ^ s *
        ∑ xi' ∈ wooleyResidueRefinementFiber p nu theta hnu xi,
          ∑ eta' ∈ wooleyResidueRefinementFiber p nu theta hnu eta,
            wooleyWeightedResidueMassSq gamma xi' *
              wooleyWeightedResidueMassSq gamma eta' *
              (‖wooleyPolynomialNormalizedResidueGridSum
                  phi qB gamma alpha xi'‖ ^ 2 *
                ‖wooleyPolynomialNormalizedResidueGridSum
                  phi qB gamma alpha eta'‖ ^ (2 * (s - 1))) := by
  let A : ℝ := wooleyWeightedResidueMassSq gamma xi *
    ‖wooleyPolynomialNormalizedResidueGridSum
      phi qB gamma alpha xi‖ ^ 2
  let D : ℝ := wooleyWeightedResidueMassSq gamma eta *
    ‖wooleyPolynomialNormalizedResidueGridSum
      phi qB gamma alpha eta‖ ^ (2 * (s - 1))
  let AR : ℝ := ∑ xi' ∈ wooleyResidueRefinementFiber p nu theta hnu xi,
    wooleyWeightedResidueMassSq gamma xi' *
      ‖wooleyPolynomialNormalizedResidueGridSum
        phi qB gamma alpha xi'‖ ^ 2
  let DR : ℝ := ∑ eta' ∈ wooleyResidueRefinementFiber p nu theta hnu eta,
    wooleyWeightedResidueMassSq gamma eta' *
      ‖wooleyPolynomialNormalizedResidueGridSum
        phi qB gamma alpha eta'‖ ^ (2 * (s - 1))
  have hs1 : 1 ≤ s - 1 := by omega
  have hA : A ≤ (p ^ (theta - nu) : ℝ) * AR := by
    simpa only [A, AR, one_mul, pow_one, Nat.mul_one] using
      (wooleyPolynomial_lemma_6_2 (w := 1) phi hnu (by omega)
        gamma alpha xi)
  have hD : D ≤ (p ^ (theta - nu) : ℝ) ^ (s - 1) * DR := by
    simpa only [D, DR] using
      (wooleyPolynomial_lemma_6_2 (w := s - 1) phi hnu hs1 gamma alpha eta)
  have hAnonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (wooleyWeightedResidueMassSq_nonneg gamma xi)
      (sq_nonneg _)
  have hDnonneg : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (wooleyWeightedResidueMassSq_nonneg gamma eta)
      (pow_nonneg (norm_nonneg _) _)
  have hARnonneg : 0 ≤ AR := by
    dsimp [AR]
    exact Finset.sum_nonneg fun xi' hxi' =>
      mul_nonneg (wooleyWeightedResidueMassSq_nonneg gamma xi')
        (sq_nonneg _)
  have hDRnonneg : 0 ≤ DR := by
    dsimp [DR]
    exact Finset.sum_nonneg fun eta' heta' =>
      mul_nonneg (wooleyWeightedResidueMassSq_nonneg gamma eta')
        (pow_nonneg (norm_nonneg _) _)
  have hmul : A * D ≤
      ((p ^ (theta - nu) : ℝ) * AR) *
        ((p ^ (theta - nu) : ℝ) ^ (s - 1) * DR) :=
    mul_le_mul hA hD hDnonneg (mul_nonneg (by positivity) hARnonneg)
  dsimp [A, D, AR, DR] at hmul
  have hpow :
      (p ^ (theta - nu) : ℝ) *
          (p ^ (theta - nu) : ℝ) ^ (s - 1) =
        (p ^ (theta - nu) : ℝ) ^ s := by
    rw [← pow_succ']
    congr
    omega
  calc
    wooleyWeightedResidueMassSq gamma xi *
          wooleyWeightedResidueMassSq gamma eta *
          (‖wooleyPolynomialNormalizedResidueGridSum
              phi qB gamma alpha xi‖ ^ 2 *
            ‖wooleyPolynomialNormalizedResidueGridSum
              phi qB gamma alpha eta‖ ^ (2 * (s - 1))) =
        (wooleyWeightedResidueMassSq gamma xi *
            ‖wooleyPolynomialNormalizedResidueGridSum
              phi qB gamma alpha xi‖ ^ 2) *
          (wooleyWeightedResidueMassSq gamma eta *
            ‖wooleyPolynomialNormalizedResidueGridSum
              phi qB gamma alpha eta‖ ^ (2 * (s - 1))) := by ring
    _ ≤ ((p ^ (theta - nu) : ℝ) *
          ∑ xi' ∈ wooleyResidueRefinementFiber p nu theta hnu xi,
            wooleyWeightedResidueMassSq gamma xi' *
              ‖wooleyPolynomialNormalizedResidueGridSum
                phi qB gamma alpha xi'‖ ^ 2) *
        ((p ^ (theta - nu) : ℝ) ^ (s - 1) *
          ∑ eta' ∈ wooleyResidueRefinementFiber p nu theta hnu eta,
            wooleyWeightedResidueMassSq gamma eta' *
              ‖wooleyPolynomialNormalizedResidueGridSum
                phi qB gamma alpha eta'‖ ^ (2 * (s - 1))) := hmul
    _ = _ := by
      rw [← hpow]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      pm_90 Finset.sum_congr xi' hxi' eta' heta'
      ring

section
variable {Q p nu theta B k s : ℕ} [NeZero p] [NeZero (p ^ B)]
include Q p nu theta B k s
theorem wooleyPolynomial_mixed_one_refinement
    (phi : WooleyPolynomialSystem k) (hnu : nu ≤ theta) (hs : 2 ≤ s)
    (gamma : Fin Q → ℂ) :
    wooleyPolynomialMixedGridMean phi s 1 p B nu nu nu gamma ≤
      (p ^ (theta - nu) : ℝ) ^ s *
        wooleyPolynomialMixedGridMean
          phi s 1 p B theta theta nu gamma := by
  let V (d : ℕ) (xi eta : ZMod (p ^ d))
      (alpha : Fin k → ZMod (p ^ B)) : ℝ :=
    wooleyWeightedResidueMassSq gamma xi *
      wooleyWeightedResidueMassSq gamma eta *
      (‖wooleyPolynomialNormalizedResidueGridSum
          phi (p ^ B) gamma alpha xi‖ ^ 2 *
        ‖wooleyPolynomialNormalizedResidueGridSum
          phi (p ^ B) gamma alpha eta‖ ^ (2 * (s - 1)))
  let P (d : ℕ) : ℝ :=
    ∑ alpha : Fin k → ZMod (p ^ B),
      ∑ xi : ZMod (p ^ d),
        ∑ eta : ZMod (p ^ d) with wooleyResiduesSeparated nu xi eta,
          V d xi eta alpha
  pm_2840 gridScale
  have haggregate (d : ℕ) :
      ∑ xi : ZMod (p ^ d),
        ∑ eta : ZMod (p ^ d) with wooleyResiduesSeparated nu xi eta,
          wooleyWeightedResidueMassSq gamma xi *
            wooleyWeightedResidueMassSq gamma eta *
              wooleyPolynomialMixedResidueGridMoment
                phi s 1 p B d d gamma xi eta =
        gridScale * P d := by
    dsimp [gridScale, P, V]
    simp only [wooleyPolynomialMixedResidueGridMoment,
      wooleyTriangular_one, Nat.mul_one]
    have hlocal (xi eta : ZMod (p ^ d)) :
        wooleyWeightedResidueMassSq gamma xi *
            wooleyWeightedResidueMassSq gamma eta *
              (((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
                ∑ alpha : Fin k → ZMod (p ^ B),
                  ‖wooleyPolynomialNormalizedResidueGridSum
                    phi (p ^ B) gamma alpha xi‖ ^ 2 *
                  ‖wooleyPolynomialNormalizedResidueGridSum
                    phi (p ^ B) gamma alpha eta‖ ^ (2 * (s - 1))) =
          ∑ alpha : Fin k → ZMod (p ^ B),
            ((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
              (wooleyWeightedResidueMassSq gamma xi *
                wooleyWeightedResidueMassSq gamma eta *
                (‖wooleyPolynomialNormalizedResidueGridSum
                    phi (p ^ B) gamma alpha xi‖ ^ 2 *
                  ‖wooleyPolynomialNormalizedResidueGridSum
                    phi (p ^ B) gamma alpha eta‖ ^ (2 * (s - 1)))) := by
      pm_5620
    simp_rw [hlocal]
    rw [show
      (∑ xi : ZMod (p ^ d),
        ∑ eta : ZMod (p ^ d) with wooleyResiduesSeparated nu xi eta,
          ∑ alpha : Fin k → ZMod (p ^ B),
            ((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ * V d xi eta alpha) =
      ∑ xi : ZMod (p ^ d),
        ∑ alpha : Fin k → ZMod (p ^ B),
          ∑ eta : ZMod (p ^ d) with wooleyResiduesSeparated nu xi eta,
            ((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ * V d xi eta alpha by
      apply Finset.sum_congr rfl
      intro xi hxi
      rw [Finset.sum_comm]]
    rw [Finset.sum_comm]
    pm_2846 Finset.mul_sum Finset.sum_congr alpha halpha
    apply Finset.sum_congr rfl
    intro xi hxi
    rw [Finset.mul_sum]
  have hpoint (alpha : Fin k → ZMod (p ^ B)) :
      (∑ xi : ZMod (p ^ nu),
        ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
          V nu xi eta alpha) ≤
        (p ^ (theta - nu) : ℝ) ^ s *
          ∑ xi : ZMod (p ^ theta),
            ∑ eta : ZMod (p ^ theta) with
              wooleyResiduesSeparated nu xi eta,
                V theta xi eta alpha := by
    calc
      (∑ xi : ZMod (p ^ nu),
          ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
            V nu xi eta alpha) ≤
          ∑ xi : ZMod (p ^ nu),
            ∑ eta : ZMod (p ^ nu) with
              wooleyResiduesSeparated nu xi eta,
                (p ^ (theta - nu) : ℝ) ^ s *
                  ∑ xi' ∈
                    wooleyResidueRefinementFiber p nu theta hnu xi,
                    ∑ eta' ∈
                      wooleyResidueRefinementFiber p nu theta hnu eta,
                      V theta xi' eta' alpha := by
        apply Finset.sum_le_sum
        intro xi hxi
        apply Finset.sum_le_sum
        intro eta heta
        simpa only [V] using
          (wooleyPolynomial_mixed_one_point_refinement
            phi hnu hs gamma alpha xi eta)
      _ = (p ^ (theta - nu) : ℝ) ^ s *
          ∑ xi : ZMod (p ^ theta),
            ∑ eta : ZMod (p ^ theta) with
              wooleyResiduesSeparated nu xi eta,
                V theta xi eta alpha := by
        rw [← wooley_sum_refinement_pairs hnu
          (fun xi eta => V theta xi eta alpha)]
        pm_2846 Finset.mul_sum Finset.sum_congr xi hxi
  have hP : P nu ≤ (p ^ (theta - nu) : ℝ) ^ s * P theta := by
    dsimp [P]
    calc
      (∑ alpha : Fin k → ZMod (p ^ B),
          ∑ xi : ZMod (p ^ nu),
            ∑ eta : ZMod (p ^ nu) with
              wooleyResiduesSeparated nu xi eta,
                V nu xi eta alpha) ≤
          ∑ alpha : Fin k → ZMod (p ^ B),
            (p ^ (theta - nu) : ℝ) ^ s *
              ∑ xi : ZMod (p ^ theta),
                ∑ eta : ZMod (p ^ theta) with
                  wooleyResiduesSeparated nu xi eta,
                    V theta xi eta alpha :=
        Finset.sum_le_sum fun alpha _ => hpoint alpha
      _ = (p ^ (theta - nu) : ℝ) ^ s *
          ∑ alpha : Fin k → ZMod (p ^ B),
            ∑ xi : ZMod (p ^ theta),
              ∑ eta : ZMod (p ^ theta) with
                wooleyResiduesSeparated nu xi eta,
                  V theta xi eta alpha := by rw [Finset.mul_sum]
  unfold wooleyPolynomialMixedGridMean
  split_ifs with hmass
  · simp
  · rw [haggregate nu, haggregate theta]
    pm_165 hscale gridScale
    pm_1474 wooleyWeightedMassSq
    calc
      (wooleyWeightedMassSq gamma)⁻¹ ^ 2 * (gridScale * P nu) ≤
          (wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
            (gridScale * ((p ^ (theta - nu) : ℝ) ^ s * P theta)) := by
        gcongr
      _ = (p ^ (theta - nu) : ℝ) ^ s *
          ((wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
            (gridScale * P theta)) := by ring

/-- Polynomial-system Lemma 6.3 as a consumer of its initial-condition bound. -/
theorem wooleyPolynomial_lemma_6_3_of_initial_conditioning
    {C : ℝ} (phi : WooleyPolynomialSystem k) (hC : 0 ≤ C)
    (hnu : nu ≤ theta) (hs : 2 ≤ s) (gamma : Fin Q → ℂ)
    (hinitial :
      wooleyPolynomialWeightedGridMean phi s (p ^ B) gamma ≤
        C * (p ^ nu : ℝ) ^ s *
          wooleyPolynomialMixedGridMean
            phi s 1 p B nu nu nu gamma) :
    wooleyPolynomialWeightedGridMean phi s (p ^ B) gamma ≤
      C * (p ^ theta : ℝ) ^ s *
        wooleyPolynomialMixedGridMean
          phi s 1 p B theta theta nu gamma := by
  have hrefine := wooleyPolynomial_mixed_one_refinement
    (Q := Q) (p := p) (nu := nu) (theta := theta)
      (B := B) (k := k) (s := s) phi hnu hs gamma
  have hpolyNonneg : 0 ≤ wooleyPolynomialMixedGridMean
      phi s 1 p B theta theta nu gamma := by
    unfold wooleyPolynomialMixedGridMean
    split_ifs
    · simp
    · apply mul_nonneg (sq_nonneg _)
      apply Finset.sum_nonneg
      intro xi hxi
      apply Finset.sum_nonneg
      intro eta heta
      apply mul_nonneg
      · exact mul_nonneg
          (wooleyWeightedResidueMassSq_nonneg gamma xi)
          (wooleyWeightedResidueMassSq_nonneg gamma eta)
      · unfold wooleyPolynomialMixedResidueGridMoment
        apply mul_nonneg (by positivity)
        exact Finset.sum_nonneg fun alpha halpha =>
          mul_nonneg (by positivity) (by positivity)
  calc
    wooleyPolynomialWeightedGridMean phi s (p ^ B) gamma ≤
        C * (p ^ nu : ℝ) ^ s *
          wooleyPolynomialMixedGridMean
            phi s 1 p B nu nu nu gamma := hinitial
    _ ≤ C * (p ^ nu : ℝ) ^ s *
        ((p ^ (theta - nu) : ℝ) ^ s *
          wooleyPolynomialMixedGridMean
            phi s 1 p B theta theta nu gamma) := by gcongr
    _ = C * (p ^ theta : ℝ) ^ s *
          wooleyPolynomialMixedGridMean
            phi s 1 p B theta theta nu gamma := by
      have hpowers : (p : ℝ) ^ nu * (p : ℝ) ^ (theta - nu) =
          (p : ℝ) ^ theta := by rw [← pow_add, Nat.add_sub_of_le hnu]
      calc
        C * ((p : ℝ) ^ nu) ^ s *
            (((p : ℝ) ^ (theta - nu)) ^ s *
              wooleyPolynomialMixedGridMean
                phi s 1 p B theta theta nu gamma) =
          C * (((p : ℝ) ^ nu) *
            ((p : ℝ) ^ (theta - nu))) ^ s *
              wooleyPolynomialMixedGridMean
                phi s 1 p B theta theta nu gamma := by rw [mul_pow]; ring
        _ = _ := by rw [hpowers]
end


end GafniTao
