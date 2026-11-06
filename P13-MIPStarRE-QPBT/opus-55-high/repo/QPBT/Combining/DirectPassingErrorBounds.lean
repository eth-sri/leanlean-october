module

public import QPBT.Combining.ErrorBounds
public import QPBT.Combining.PassingError
public import QPBT.Combining.DirectLowDegree.Transport.Error

/-!
# Absorbing both errors of the directly indexed game

The conversion from combined measurements to a low-degree strategy has passing
error `3 * (sqrt (deltaQ + deltaL) + m * d / q)`. This module bounds its cap by
one while retaining the point error and the dimension factor in the line error.
It then absorbs low-degree soundness at that capped error into `deltaQld`.
These scalar estimates do not construct either measurement witness.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288,1402`
* Blueprint `lem:qld-4-7`
-/

@[expose] public section

namespace MIPStarRE.QPBT

variable (pointError : ℝ → ℝ)

/-- The capped passing error of the directly indexed game is bounded by the
dimension times a polynomial error. Both the point error `pointError error`
and the line error `C * dimension * lineError error ratio` are retained.
This is a scalar auxiliary for paper `lem:qld-4-7`, not an existence assertion
for the measurements used to construct that game. -/
theorem exists_direct_passing_polynomial_bound (hpoint : IsPolyErr pointError) (lineError : ℝ → ℝ → ℝ)
    (hline : IsPolyErr₂ lineError) (C : ℝ) (hC : 0 ≤ C) :
    ∃ passingError : ℝ → ℝ → ℝ, IsPolyErr₂ passingError ∧
      ∀ error ratio dimension : ℝ, 0 ≤ error → 0 ≤ ratio → 1 ≤ dimension →
        min 1 (directPassingErrorEnvelope
          (pointError error + C * dimension * lineError error ratio) ratio) ≤
            dimension * passingError error ratio := by
  obtain ⟨A, p, hA, hp, hpoint⟩ := hpoint
  obtain ⟨B, r, s, hB, hr, hs, hline⟩ := hline
  let t := min p r
  let u := min s 2
  let K := A + C * B
  let D := 3 * (Real.sqrt K + 1) + 1
  have ht := lt_min hp hr
  have hu : 0 < u := lt_min hs (by norm_num)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : 1 ≤ D := by dsimp [D]; nlinarith [Real.sqrt_nonneg K]
  refine ⟨fun error ratio => D * (error ^ (t / 2) + ratio ^ (u / 2)),
    ⟨D, t / 2, u / 2, hD, by positivity, by positivity, ?_⟩, ?_⟩
  · intro error ratio herror hratio
    exact ⟨by positivity, le_rfl⟩
  intro error ratio dimension herror hratio hdimension
  have hdim : 0 ≤ dimension := by linarith
  have he : 0 ≤ error ^ (t / 2) := Real.rpow_nonneg herror _
  have hy : 0 ≤ ratio ^ (u / 2) := Real.rpow_nonneg hratio _
  have hlarge (h : 1 ≤ error ^ (t / 2) + ratio ^ (u / 2)) :
      min 1 (directPassingErrorEnvelope
        (pointError error + C * dimension * lineError error ratio) ratio) ≤
          dimension * (D * (error ^ (t / 2) + ratio ^ (u / 2))) := by
    refine (min_le_left _ _).trans ?_
    exact one_le_mul_of_one_le_of_one_le hdimension
      (one_le_mul_of_one_le_of_one_le hD h)
  by_cases herrorOne : error ≤ 1
  · by_cases hratioOne : ratio ≤ 1
    · have hpointBound :=
        (hpoint error herror).2.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge' herror herrorOne ht.le
            (min_le_left _ _)) (by linarith))
      have hlineBound :=
        (hline error ratio herror hratio).2.trans (mul_le_mul_of_nonneg_left
          (add_le_add
            (Real.rpow_le_rpow_of_exponent_ge' herror herrorOne ht.le
              (min_le_right _ _))
            (Real.rpow_le_rpow_of_exponent_ge' hratio hratioOne hu.le
              (min_le_left _ _))) (by linarith))
      have heFull : 0 ≤ error ^ t := Real.rpow_nonneg herror _
      have hyFull : 0 ≤ ratio ^ u := Real.rpow_nonneg hratio _
      have hsum : pointError error + C * dimension * lineError error ratio ≤
          dimension * K * (error ^ t + ratio ^ u) := by
        have hpDim : A * error ^ t ≤ dimension * (A * error ^ t) :=
          le_mul_of_one_le_left (by positivity) hdimension
        have hlDim := mul_le_mul_of_nonneg_left hlineBound
          (mul_nonneg hC hdim)
        dsimp [K]
        nlinarith [mul_nonneg (mul_nonneg hdim (by linarith : 0 ≤ A)) hyFull]
      have heSq : (error ^ (t / 2)) ^ (2 : ℕ) = error ^ t := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul herror]
        congr 1
        ring
      have hySq : (ratio ^ (u / 2)) ^ (2 : ℕ) = ratio ^ u := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hratio]
        congr 1
        ring
      have hrootSum : Real.sqrt (error ^ t + ratio ^ u) ≤
          error ^ (t / 2) + ratio ^ (u / 2) := by
        apply (Real.sqrt_le_left (add_nonneg he hy)).mpr
        nlinarith
      have hrootDim : Real.sqrt dimension ≤ dimension := by
        apply (Real.sqrt_le_left hdim).mpr
        nlinarith
      have hroot : Real.sqrt
          (pointError error + C * dimension * lineError error ratio) ≤
          dimension * Real.sqrt K * (error ^ (t / 2) + ratio ^ (u / 2)) := by
        calc
          _ ≤ Real.sqrt (dimension * K * (error ^ t + ratio ^ u)) :=
            Real.sqrt_le_sqrt hsum
          _ = Real.sqrt dimension * Real.sqrt K *
              Real.sqrt (error ^ t + ratio ^ u) := by
            rw [Real.sqrt_mul (mul_nonneg hdim hK), Real.sqrt_mul hdim]
          _ ≤ _ := mul_le_mul
            (mul_le_mul_of_nonneg_right hrootDim (Real.sqrt_nonneg K)) hrootSum
            (Real.sqrt_nonneg _) (mul_nonneg hdim (Real.sqrt_nonneg K))
      have hratioSmall : ratio ≤ ratio ^ (u / 2) := by
        simpa using Real.rpow_le_rpow_of_exponent_ge' hratio hratioOne
          (by positivity : 0 ≤ u / 2) (by
            have : u ≤ 2 := min_le_right _ _
            linarith : u / 2 ≤ 1)
      have hratioDim :=
        hratioSmall.trans (le_mul_of_one_le_left hy hdimension)
      refine (min_le_right _ _).trans ?_
      dsimp [directPassingErrorEnvelope, D]
      nlinarith
    · exact hlarge (by
        have := Real.one_le_rpow (le_of_not_ge hratioOne) (by positivity : 0 ≤ u / 2)
        linarith)
  · exact hlarge (by
      have := Real.one_le_rpow (le_of_not_ge herrorOne) (by positivity : 0 ≤ t / 2)
      linarith)

end MIPStarRE.QPBT
