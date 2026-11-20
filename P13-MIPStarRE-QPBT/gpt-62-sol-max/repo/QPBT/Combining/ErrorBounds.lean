module

public import QPBT.Combining.PowerEnvelope
public import QPBT.Test.LowDegreeGameMeasurements
public import QPBT.Test.SoundnessDefs
public import Mathlib.Analysis.MeanInequalitiesPow

/-! # Scalar error bounds for combining polynomial measurements

This module proves the formalization-only scalar estimates used by the combining
argument: nonnegativity of the real fourth root, the quarter-power form of a
square root of two deficit terms, polynomial bounds after conditioning,
composition with the dimension factor retained, and absorption into the global
polynomial-pair error scale. The estimates quantify over error functions and
numerical parameters; they do not construct measurements, and none of them is
specific to Claims 17-1 through 17-3.

## References

The auxiliary blueprint statements are `thm:qld-conditioned-polynomial-bound`,
`thm:qld-combining-polynomial-bound`, and `thm:qld-global-pair-error-bound` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`. They support the calculations
in `lem:qld-xz-lines`, `lem:qld-4-13`, and `lem:qld-4-7` of
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963,1134-1246`
and `:1278-1288,1402`. The corrected error notation and the retained dimension
factor are documented in `docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

noncomputable section

/-- The real fourth root is nonnegative on all of `ℝ`. For `x < 0` the real power
`x ^ (1/4)` is defined as `|x| ^ (1/4) * cos (π/4)`, which is positive, and for
`0 ≤ x` it is the usual fourth root. The estimates of `lem:qld-4-13` are stated
with quarter powers of error quantities whose nonnegativity is not always
available at the point of use, so the bound is recorded without a sign
hypothesis. -/
theorem rpow_quarter_nonneg (x : ℝ) : 0 ≤ Real.rpow x (1 / 4 : ℝ) := by
  change 0 ≤ x ^ (1 / 4 : ℝ)
  rcases lt_or_ge x 0 with hx | hx
  · rw [Real.rpow_def_of_neg hx,
      show (1 / 4 : ℝ) * Real.pi = Real.pi / 4 by ring, Real.cos_pi_div_four]
    positivity
  · exact Real.rpow_nonneg hx _

/-- Subadditivity of the square root on nonnegative inputs. -/
theorem sqrt_add_le_sum_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  simp only [Real.sqrt_eq_rpow]
  exact Real.rpow_add_le_add_rpow hx hy (by norm_num) (by norm_num)

/-- The quarter-power form of the two deficit terms. -/
theorem sqrt_deficit_bound_le (m δP δQ : ℝ) (hm : 1 ≤ m) (hP : 0 ≤ δP)
    (hQ : 0 ≤ δQ) :
    Real.sqrt (2 * Real.sqrt (4 * m ^ 2 * δP) + 2 * Real.sqrt (4 * δQ)) ≤
      2 * Real.sqrt m * (Real.rpow δP (1 / 4 : ℝ) + Real.rpow δQ (1 / 4 : ℝ)) := by
  have h (d x : ℝ) (hd : 0 ≤ d) (hx : 0 ≤ x) :
      Real.sqrt (2 * Real.sqrt (4 * d ^ 2 * x)) = 2 * Real.sqrt d * x ^ (1 / 4 : ℝ) := by
    have hroot : Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
      simp only [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
      norm_num
    rw [show 4 * d ^ 2 * x = (2 * d) ^ 2 * x by ring,
      Real.sqrt_mul (by positivity : 0 ≤ (2 * d) ^ 2) x, Real.sqrt_sq (by positivity),
      show 2 * (2 * d * Real.sqrt x) = (2 : ℝ) ^ 2 * (d * Real.sqrt x) by ring,
      Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ) ^ 2) _, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_mul hd, hroot]
    ring
  have e := h 1 δQ (by norm_num) hQ
  simp only [one_pow, mul_one, Real.sqrt_one] at e
  have hm0 : 0 ≤ m := zero_le_one.trans hm
  have hm' : 1 ≤ Real.sqrt m := by simpa using Real.sqrt_le_sqrt hm
  refine (sqrt_add_le_sum_sqrt (by positivity) (by positivity)).trans ?_
  rw [h m δP hm0 hP, e, mul_add]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (by linarith)
    (Real.rpow_nonneg hQ _))

private abbrev UnitErrors := Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1

private def unitErrors : ErrorDomain UnitErrors where
  size := fun _ => 1
  noise := fun v => max (v.1 : ℝ) (v.2 : ℝ)
  size_ge_one := fun _ => le_rfl
  noise_nonneg := fun v => v.1.2.1.trans (le_max_left ..)
  noise_le_one := fun v => max_le v.1.2.2 v.2.2.2

private theorem unitErrors_fst : unitErrors.Polynomial (fun v => v.1.val) :=
  unitErrors.polynomial_noise.mono fun v => ⟨v.1.2.1, le_max_left ..⟩

private theorem unitErrors_snd : unitErrors.Polynomial (fun v => v.2.val) :=
  unitErrors.polynomial_noise.mono fun v => ⟨v.2.2.1, le_max_right ..⟩

private theorem unitErrors_envelope {f : UnitErrors → ℝ} (h : unitErrors.Polynomial f) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ ∀ v, f v ≤ C * ((v.1 : ℝ) ^ r + (v.2 : ℝ) ^ r) := by
  obtain ⟨C, r, hC, hr, _, hbound⟩ := h.exists_envelope
  refine ⟨C, r, hC.le, hr, fun v => (hbound v).trans ?_⟩
  simp only [unitErrors, Real.one_rpow, mul_one, Real.rpow_max v.1.2.1 v.2.2.1 hr.le]
  exact mul_le_mul_of_nonneg_left (max_le
    (le_add_of_nonneg_right (Real.rpow_nonneg v.2.2.1 _))
    (le_add_of_nonneg_left (Real.rpow_nonneg v.1.2.1 _))) (by linarith)

/-- Additive polynomial errors remain polynomial after conditioning and insertion
of a polynomially small point error. The minimum uses the independent unit bound
for normalized POVM consistency, not a replacement measurement. This scalar lemma
supports `lem:qld-xz-lines`, paper lines 950--963; see issue Dengnifer/MIPStarRE-QPBT-bak#118 and
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`. -/
theorem exists_conditioned_polynomial_bound (pointError : ℝ → ℝ)
    (hpoint : IsPolyErr pointError) (constant : ℝ) (hconstant : 1 ≤ constant)
    (pastingError : ℝ → ℝ → ℝ) (hpasting : IsPolyErr₂ pastingError) :
    ∃ lineError : ℝ → ℝ → ℝ, IsPolyErr₂ lineError ∧
      ∀ error ratio mass : ℝ, 0 ≤ error → 0 ≤ ratio →
        1 / 2 ≤ mass → mass ≤ 1 →
        min 1 (mass * pastingError ratio
          ((8 * pointError error + constant * (error + Real.sqrt error)) / mass) + ratio) ≤
          lineError error ratio := by
  obtain ⟨C, r, s, hC, hr, hs, hpaste⟩ := hpasting
  have hc := zero_le_one.trans hconstant
  have hpoint' := unitErrors_fst.compose hpoint
  let numerator (v : UnitErrors) :=
    8 * pointError v.1 + constant * ((v.1 : ℝ) + Real.sqrt v.1)
  have hn : unitErrors.Polynomial numerator :=
    (hpoint'.scale (C := 8) (by norm_num)).add ((unitErrors_fst.add unitErrors_fst.sqrt).scale hc)
  have h := (((unitErrors_snd.rpow hr).add ((hn.scale (C := 2) (by norm_num)).rpow hs)).scale
    (zero_le_one.trans hC)).add unitErrors_snd
  obtain ⟨K, t, hK, ht, hb⟩ := unitErrors_envelope h
  refine ⟨fun x y => K * (x ^ t + y ^ t), isPolyErr₂_power_envelope hK ht ht, ?_⟩
  intro x y m hx hy hm hmo
  apply min_one_le_power_envelope hx hy ht.le ht.le hK
  intro hx1 hy1
  let v : UnitErrors := (⟨x, hx, hx1⟩, ⟨y, hy, hy1⟩)
  have hz : 0 ≤ numerator v := by
    have := hpoint.nonneg_at x hx
    dsimp [numerator, v]
    positivity
  have hm0 : 0 < m := by linarith
  have hdiv : numerator v / m ≤ 2 * numerator v := by
    exact (div_le_iff₀ hm0).mpr (by nlinarith [mul_nonneg hz (sub_nonneg.mpr hm)])
  obtain ⟨hy0, hyb⟩ := hpaste y (numerator v / m) hy (div_nonneg hz hm0.le)
  calc
    _ ≤ pastingError y (numerator v / m) + y := by
      exact add_le_add (mul_le_of_le_one_left hy0 hmo) le_rfl
    _ ≤ C * (y ^ r + (2 * numerator v) ^ s) + y := by
      refine add_le_add (hyb.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by linarith))) le_rfl
      exact Real.rpow_le_rpow (div_nonneg hz hm0.le) hdiv hs.le
    _ ≤ _ := hb v


/-- Polynomial absorption for the first combining route, including large errors.
The independent unit bound on consistency accounts for the minimum. The factor
`dimension` is retained, as required by the correction to `lem:qld-4-13` in
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`, paper lines 1134--1246. -/
theorem exists_combining_polynomial_bound (pointError : ℝ → ℝ)
    (hpoint : IsPolyErr pointError) (lineError : ℝ → ℝ → ℝ)
    (hline : IsPolyErr₂ lineError) (constant : ℝ) (hconstant : 0 ≤ constant) :
    ∃ combinedError : ℝ → ℝ → ℝ, IsPolyErr₂ combinedError ∧
      ∀ error ratio dimension : ℝ, 0 ≤ error → 0 ≤ ratio → 1 ≤ dimension →
        min 1 (constant * ((pointError error) ^ (1 / 2 : ℝ) + Real.sqrt dimension *
          ((lineError error ratio) ^ (1 / 4 : ℝ) + (pointError error) ^ (1 / 4 : ℝ) +
            error ^ (1 / 4 : ℝ)))) ≤ dimension * combinedError error ratio := by
  have hp := unitErrors_fst.compose hpoint
  have hl := unitErrors_fst.compose₂ unitErrors_snd hline
  have h := ((hp.rpow (p := 1 / 2) (by norm_num)).add
    (((hl.rpow (p := 1 / 4) (by norm_num)).add (hp.rpow (p := 1 / 4) (by norm_num))).add
      (unitErrors_fst.rpow (p := 1 / 4) (by norm_num)))).scale hconstant
  obtain ⟨K, t, hK, ht, hb⟩ := unitErrors_envelope h
  refine ⟨fun x y => K * (x ^ t + y ^ t), isPolyErr₂_power_envelope hK ht ht, ?_⟩
  intro x y m hx hy hm
  rw [← mul_assoc]
  apply min_one_le_power_envelope hx hy ht.le ht.le (one_le_mul_of_one_le_of_one_le hm hK)
  intro hx1 hy1
  let v : UnitErrors := (⟨x, hx, hx1⟩, ⟨y, hy, hy1⟩)
  have hp0 := hpoint.nonneg_at x hx
  have hl0 := hline.nonneg_at x y hx hy
  have ht0 : 0 ≤ lineError x y ^ (1 / 4 : ℝ) + pointError x ^ (1 / 4 : ℝ) + x ^ (1 / 4 : ℝ) :=
    by positivity
  have hnorm := mul_le_mul_of_nonneg_left
    (add_le_add (le_mul_of_one_le_left (Real.rpow_nonneg hp0 (1 / 2 : ℝ)) hm)
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_self_iff.mpr (Or.inr hm)) ht0)) hconstant
  apply hnorm.trans
  convert mul_le_mul_of_nonneg_left (hb v) (zero_le_one.trans hm) using 1 <;> dsimp [v] <;> ring


end

end MIPStarRE.QPBT
