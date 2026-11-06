/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Surface.CongruenceAuxiliary
import CCDN.AuxiliaryPolynomial.HypersurfaceRankArchimedean
import Mathlib.Algebra.Order.Star.Real

/-! Numerical degree selection for the smooth-congruence auxiliary on a
surface. All constants are independent of coefficients and box radius. -/

namespace CCDN
noncomputable section
open MvPolynomial Finset

section
variable (d : ℕ) (K : ℝ)

/-- A constant, depending on the degree `d` and the logarithmic height constant `K`, bounding
the height charge of the smooth-congruence determinant estimate for a surface of degree `d`
whose coefficient height `H` satisfies `log H ≤ K (log B + 1)`. -/
def surfaceCongruenceChargeConstant : ℝ :=
  Real.log (2 + 27 * (d : ℝ) ^ 4 * hypersurfaceHeightConstant 4 *
    (1 + K / (d : ℝ) ^ 2)) + 2 * mertensError + 1

/-- The constant `8 log d + 2 surfaceCongruenceChargeConstant d K + E + 6d + 22`, with `E` the
determinant error in dimension one, controlling the numerical gap between the upper and lower
bounds for surface congruence determinants. -/
def surfaceCongruenceGapConstant : ℝ :=
  8 * Real.log d + 2 * surfaceCongruenceChargeConstant d K +
    hypersurfaceDeterminantError 1 + 6 * d + 22

end

theorem surface_congruence_lower_eq (d s : ℕ) (H Q : ℝ) :
    affineCongruenceDeterminantLower 1 d s H Q =
      (Real.sqrt 2 / 3 * (s : ℝ) * Real.sqrt s) *
        (Real.log s + 2 * Q - 8 * Real.log d -
          2 * congruenceHeightCharge 4 d H Q - hypersurfaceDeterminantError 1) -
            3 * s * Q := by
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hp : s ^ (1 + 1 / 2 : ℝ) = s * Real.sqrt s := by
    rw [Real.rpow_add' hs (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
  norm_num at hp
  unfold affineCongruenceDeterminantLower hypersurfaceDeterminantMain
  norm_num
  rw [hp, ← Real.sqrt_eq_rpow]
  ring

section
variable (d : ℕ) (K : ℝ)

/-- The constant `d + 2 (exp (G / 2) + 1) + 1`, with `G` the gap constant
`surfaceCongruenceGapConstant d K`, which scales the degree of the surface congruence
auxiliaries. -/
def surfaceCongruenceDegreeConstant : ℝ :=
  d + 2 * (Real.exp (surfaceCongruenceGapConstant d K / 2) + 1) + 1

/-- The auxiliary degree constant `surfaceCongruenceDegreeConstant d K` is positive. -/
theorem surfaceCongruenceDegreeConstant_pos :
    0 < surfaceCongruenceDegreeConstant d K := by
  unfold surfaceCongruenceDegreeConstant
  positivity

end

/-- One integer degree, with a constant fixed before the height and congruences,
works for every standard-monomial rank satisfying the elementary power bound. -/
theorem surface_congruence_degree_selection {d : ℕ} (hd : 0 < d)
    {K B H Q : ℝ} (hK : 0 ≤ K) (hB : 1 ≤ B) (hH : 1 ≤ H) (hQ : 0 ≤ Q)
    (hheight : Real.log H ≤ K * (Real.log B + 1)) :
    ∃ M : ℕ, d ≤ M ∧
      (M : ℝ) ≤ surfaceCongruenceDegreeConstant d K *
        (B ^ (1 / Real.sqrt (d : ℝ)) / Real.exp Q + 1) * (1 + Real.log B + Q) ∧
      ∀ s : ℕ, (d : ℝ) * ((M : ℝ) - d + 1) ^ 2 / 2 ≤ s →
        surfaceWeightedDeterminantUpper d s B <
          affineCongruenceDeterminantLower 1 d s H Q := by
  let T := 1 + Real.log B + Q
  let ρ := B ^ (1 / Real.sqrt d) / Real.exp Q
  let E := Real.exp (surfaceCongruenceGapConstant d K / 2) + 1
  let S := E * (ρ + 1) * T
  have hB0 := zero_lt_one.trans_le hB
  have hdR : (1 : ℝ) ≤ d := mod_cast hd
  have hT : 1 ≤ T := by dsimp [T]; linarith [Real.log_nonneg hB]
  have hT0 := zero_lt_one.trans_le hT
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hE : 1 ≤ E := by
    dsimp [E]; linarith [Real.exp_pos (surfaceCongruenceGapConstant d K / 2)]
  have hE0 := zero_lt_one.trans_le hE
  have hS0 : 0 < S := by dsimp [S]; positivity
  have hST : T ≤ S := by
    have hh := mul_le_mul hE (show 1 ≤ ρ + 1 by linarith) (by norm_num) hE0.le
    have hh' := mul_le_mul_of_nonneg_right hh hT0.le
    simpa [one_mul] using hh'
  let M := d + ⌈2 * S⌉₊
  have hMl : 2 * S ≤ M - d + 1 := by
    have hh := Nat.le_ceil (2 * S)
    dsimp [M]
    push_cast
    linarith
  refine ⟨M, (Nat.le_add_right _ _), (by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 2 * S by positivity)
    have hprod : 1 ≤ (ρ + 1) * T := by
      nlinarith
    have hscale := mul_le_mul_of_nonneg_left hprod (show 0 ≤ (d : ℝ) + 1 by positivity)
    dsimp [M] at *
    push_cast
    change _ ≤ (d + 2 * E + 1) * (ρ + 1) * T
    dsimp [S] at hh
    nlinarith), ?_⟩
  intro s hs
  have hsq : S ^ 2 ≤ s := by nlinarith
  have hsR := lt_of_lt_of_le (sq_pos_of_pos hS0) hsq
  have hsN : 0 < s := mod_cast hsR
  have hroot :=
    hST.trans (Real.le_sqrt_of_sq_le hsq)
  have hlogS : 2 * Real.log S ≤ Real.log s := by
    simpa [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (sq_pos_of_pos hS0) hsq
  have hlogE : surfaceCongruenceGapConstant d K / 2 ≤ Real.log E := by
    have hh := Real.log_le_log (Real.exp_pos (surfaceCongruenceGapConstant d K / 2))
      (show Real.exp (surfaceCongruenceGapConstant d K / 2) ≤ E by dsimp [E]; linarith)
    simpa [Real.log_exp] using hh
  have hlogρ : Real.log ρ ≤ Real.log (ρ + 1) :=
    Real.log_le_log hρ (by linarith)
  have hρeq : Real.log ρ = (1 / Real.sqrt d) * Real.log B - Q := by
    dsimp [ρ]
    rw [Real.log_div (by positivity) (Real.exp_ne_zero _), Real.log_rpow hB0, Real.log_exp]
  have hSeq : Real.log S = Real.log E + Real.log (ρ + 1) + Real.log T := by
    dsimp [S]
    rw [Real.log_mul (by positivity) hT0.ne', Real.log_mul hE0.ne' (by positivity)]
  have hrank : (2 / Real.sqrt d) * Real.log B +
      2 * Real.log T + surfaceCongruenceGapConstant d K ≤ Real.log s + 2 * Q := by
    rw [hSeq] at hlogS
    rw [hρeq] at hlogρ
    have heq : (2 / Real.sqrt d) * Real.log B =
        2 * ((1 / Real.sqrt d) * Real.log B) := by ring
    rw [heq]
    linarith
  unfold surfaceWeightedDeterminantUpper
  dsimp [T] at hroot hrank
  clear * - hd hsN hK hB hH hQ hheight hroot hrank
  have hsR : (0 : ℝ) < s := mod_cast hsN
  have hdR : (0 : ℝ) < d := mod_cast hd
  have hsd := Real.sqrt_pos.mpr hdR
  have hss := Real.sqrt_pos.mpr hsR
  have hlogB := Real.log_nonneg hB
  have hfac : Real.log (s.factorial : ℝ) ≤ (s : ℝ) * Real.log s := by
    have hh : (s.factorial : ℝ) ≤ (s : ℝ) ^ s := mod_cast Nat.factorial_le_pow s
    simpa using Real.log_le_log (by positivity) hh
  have hfac' := hfac.trans (mul_le_mul_of_nonneg_left (by
    have hh := log_le_dimension_root (r := 2) (by omega) hsR
    simpa only [Nat.cast_ofNat, ← Real.sqrt_eq_rpow] using hh) hsR.le)
  have hcharge : congruenceHeightCharge 4 d H Q ≤
      Real.log (1 + Real.log B + Q) + surfaceCongruenceChargeConstant d K := by
    have hc :=
      zero_le_one.trans (hypersurfaceHeightConstant_one_le 4)
    have hlogH := Real.log_nonneg hH
    have hT : 1 ≤ 1 + Real.log B + Q := by linarith
    have hheight' : Real.log H ≤ K * (1 + Real.log B + Q) := by nlinarith
    let A := 27 * (d : ℝ) ^ 4 * hypersurfaceHeightConstant 4
    have hA : 0 ≤ A := by positivity
    have hdiv := div_le_div_of_nonneg_right hheight' (sq_nonneg (d : ℝ))
    have hinside : 1 + A * (1 + Real.log H / (d : ℝ) ^ 2) + Q ≤
        (2 + A * (1 + K / (d : ℝ) ^ 2)) * (1 + Real.log B + Q) := by
      have hm := mul_le_mul_of_nonneg_left hdiv hA
      have hc1 := mul_le_mul_of_nonneg_left hT hA
      have he : K * (1 + Real.log B + Q) / d ^ 2 =
          K / d ^ 2 * (1 + Real.log B + Q) := by ring
      rw [he] at hm
      nlinarith
    have hleft : 0 < 1 + A * (1 + Real.log H / d ^ 2) + Q := by positivity
    have hright : 0 < 2 + A * (1 + K / d ^ 2) := by positivity
    have hh := Real.log_le_log hleft hinside
    rw [Real.log_mul hright.ne' (by grind)] at hh
    unfold congruenceHeightCharge surfaceCongruenceChargeConstant
    dsimp [A] at hh
    simp [mul_assoc] at hh ⊢
    nlinarith
  have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by simp_all
  let A : ℝ := Real.sqrt 2 / 3 * s * Real.sqrt s
  have hA : 0 < A := by positivity
  have hsplit : Real.sqrt (2 * s / d) =
      Real.sqrt 2 * Real.sqrt s / Real.sqrt d := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num)]
  have hmain : (2 / 3 : ℝ) * s * Real.sqrt (2 * s / d) =
      A * (2 / Real.sqrt d) := by
    rw [hsplit]
    dsimp [A]
    ring
  have herr : Real.log s.factorial + (2 * d + 2) * s * Real.log B + 3 * s * Q ≤
      A * (6 * d + 21) := by
    have hb : Real.log B ≤ Real.sqrt s := by linarith
    have hq : Q ≤ Real.sqrt s := by linarith
    have hb' := mul_le_mul_of_nonneg_left hb
      (show 0 ≤ (2 * (d : ℝ) + 2) * s by positivity)
    have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ 3 * (s : ℝ) by positivity)
    have hA' : s * Real.sqrt s ≤ 3 * A := by
      have hh := mul_le_mul_of_nonneg_right hsqrt2
        (show 0 ≤ (s : ℝ) * Real.sqrt s by positivity)
      grind
    have hscale := mul_le_mul_of_nonneg_left hA'
      (show 0 ≤ 2 * (d : ℝ) + 7 by positivity)
    nlinarith
  have hbracket :
      (2 / Real.sqrt (d : ℝ)) * Real.log B + (6 * d + 22) ≤
        Real.log s + 2 * Q - 8 * Real.log d -
          2 * congruenceHeightCharge 4 d H Q - hypersurfaceDeterminantError 1 := by
    unfold surfaceCongruenceGapConstant at hrank
    linarith
  have hm := mul_le_mul_of_nonneg_left hbracket hA.le
  rw [surface_congruence_lower_eq, hmain]
  change _ < A * _ - _
  nlinarith

/-- The smooth residue classes have a proper auxiliary of degree
O_d,K((B^(1/√d)/exp Q + 1)(1 + log B + Q)). -/
theorem exists_surface_congruence_auxiliary
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) {K H B : ℝ} (hK : 0 ≤ K) (hH : 1 ≤ H) (hB : 1 ≤ B)
    (hcoeff : CoefficientHeightLE f H)
    (hheight : Real.log H ≤ K * (Real.log B + 1))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : ℕ → IntPoint 3)
    (ha : ∀ p ∈ P, MvPolynomial.eval₂ (Int.castRingHom (ZMod p))
      (fun j => (a p j : ZMod p)) f = 0)
    (hsmooth : ∀ p ∈ P, ∃ j, MvPolynomial.eval (fun i => (a p i : ZMod p))
      (MvPolynomial.pderiv j (MvPolynomial.map (Int.castRingHom (ZMod p)) f)) ≠ 0) :
    ∃ g : MvPolynomial (Fin 3) ℤ, g ≠ 0 ∧
      ¬ MvPolynomial.map (Int.castRingHom ℚ) f ∣ MvPolynomial.map (Int.castRingHom ℚ) g ∧
      (g.totalDegree : ℝ) ≤ surfaceCongruenceDegreeConstant f.totalDegree K *
        (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) /
          Real.exp (∑ p ∈ P, Real.log p) + 1) *
        (1 + Real.log B + ∑ p ∈ P, Real.log p) ∧
      ∀ x ∈ affineCongruencePoints f B P a, MvPolynomial.eval x g = 0 := by
  have hQ : 0 ≤ ∑ p ∈ P, Real.log p := Finset.sum_nonneg fun p hp =>
    Real.log_nonneg (mod_cast (hP p hp).one_le)
  obtain ⟨M, hdM, hM, hgap⟩ :=
    surface_congruence_degree_selection hd hK hB hH hQ hheight
  have hf : f ≠ 0 := by aesop
  have hg := hgap (surfaceCongruenceRank f M) (surface_congruence_rank_power_bounds f hf hdM).1
  let fQ := map (Int.castRingHom ℚ) f
  let S := standardMonomialPrefix (Ideal.span {fQ}) MonomialOrder.degLex M
  let e := (Fintype.equivFin S).symm
  let mon : Fin (Fintype.card S) → (Fin 3 →₀ ℕ) := fun j => (e j).val
  have hc : Fintype.card S = surfaceCongruenceRank f M := Fintype.card_coe S
  have hdegree :=
    rational_map_totalDegree f
  have hN : 0 < Fintype.card S := by
    rw [hc]
    have hb := (surface_congruence_rank_power_bounds f hf hdM).1
    have hMR : (f.totalDegree : ℝ) ≤ M := mod_cast hdM
    have hpos := lt_of_lt_of_le
      (by positivity : (0 : ℝ) < (f.totalDegree : ℝ) *
        ((M : ℝ) - f.totalDegree + 1) ^ 2 / 2) hb
    exact_mod_cast hpos
  have hmon := Subtype.val_injective.comp e.injective
  have hstd (j) : mon j ∈ Ideal.standardExponents (Ideal.span {fQ}) MonomialOrder.degLex :=
    (mem_standardMonomialPrefix _ _ _ _).mp (e j).property |>.1
  have hdeg (j) : Finsupp.degree (mon j) ≤ M :=
    (mem_standardMonomialPrefix _ _ _ _).mp (e j).property |>.2
  have hweight : (∑ j, ((Finsupp.degree (mon j) : ℕ) : ℝ)) ≤
      (2 / 3 : ℝ) * Fintype.card S *
        Real.sqrt (2 * Fintype.card S / f.totalDegree) +
          (2 * f.totalDegree + 2) * Fintype.card S := by
    have hw := surface_standard_monomial_weight fQ (by aesop) (hdegree ▸ hd) (hdegree ▸ hdM)
    have hsum : (∑ j, ((Finsupp.degree (mon j) : ℕ) : ℝ)) =
        ∑ j ∈ S, ((Finsupp.degree j : ℕ) : ℝ) := by
      rw [← Finset.sum_coe_sort S]
      exact e.sum_comp (fun j => ((Finsupp.degree j.val : ℕ) : ℝ))
    rwa [hsum, Fintype.card_coe, ← hdegree]
  have hgap' : Real.log ((Fintype.card S).factorial : ℝ) +
      (∑ j, ((Finsupp.degree (mon j) : ℕ) : ℝ)) * Real.log B <
      affineCongruenceDeterminantLower 1 f.totalDegree (Fintype.card S)
        H (∑ p ∈ P, Real.log p) := by
    apply lt_of_le_of_lt (add_le_add_right
      (mul_le_mul_of_nonneg_right hweight (Real.log_nonneg hB)) _)
    simpa [hc, surfaceWeightedDeterminantUpper] using hg
  let X := affineCongruencePoints f B P a
  let ex := (Fintype.equivFin X).symm
  let x : Fin (Fintype.card X) → IntPoint 3 := fun i => (ex i).val
  have hx (i) := mem_affineCongruencePoints.mp (ex i).property
  obtain ⟨g, hg0, hgnd, hgdeg, hgz⟩ : ∃ g : MvPolynomial (Fin 3) ℤ, g ≠ 0 ∧
      ¬ fQ ∣ map (Int.castRingHom ℚ) g ∧ g.totalDegree ≤ M ∧ ∀ i, eval (x i) g = 0 := by
    apply exists_standard_auxiliary_of_zero_determinants fQ mon hmon hstd hdeg x
    intro b
    have hxB : IsBoxZeroFamily f B (x ∘ b) :=
      ⟨hB, fun i => (hx (b i)).2.1, fun i j => (hx (b i)).1 j⟩
    have hres : IsSmoothResidueFamily f P a (x ∘ b) :=
      ⟨hP, ha, hsmooth, fun p hp i j => (hx (b i)).2.2 p hp j⟩
    generalize x ∘ b = x at hxB hres ⊢
    by_contra hne
    let G : Fin (Fintype.card S) → MvPolynomial (Fin (1 + 2)) ℤ :=
      fun j => monomial (mon j) 1
    have hG : ∀ j, (G j).totalDegree ≤ M := fun j =>
      (totalDegree_monomial_le _ _).trans (hdeg j)
    have hmat : (Matrix.of fun i j => eval (x i) (G j)) = evaluationMatrix mon x := by
      ext i j
      simp only [Matrix.of_apply, G, eval_monomial, one_mul]
      rfl
    have hrows : LinearIndependent ℚ
        ((Matrix.of fun i j => eval (x i) (G j)).map ((↑) : ℤ → ℚ)).row := by
      rw [hmat]
      apply Matrix.linearIndependent_row_iff_isUnit.mpr
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      apply isUnit_iff_ne_zero.mpr
      change ((Int.castRingHom ℚ).mapMatrix (evaluationMatrix mon x)).det ≠ 0
      rw [← RingHom.map_det (Int.castRingHom ℚ)]
      change ((evaluationMatrix mon x).det : ℚ) ≠ 0
      exact_mod_cast hne
    refine (not_lt_of_ge (le_trans ?_
      (weighted_evaluation_det_log_bound mon x hxB.one_le_radius hxB.abs_le hne))) hgap'
    rw [← Int.cast_abs, ← square_minorGcd_eq_abs_det, ← hmat]
    have hx := hxB.eval_eq_zero
    let F := scaledHomogenize f.totalDegree 1 f
    have hf0 := ne_zero_of_irreducible_map hir
    have hF := scaledHomogenize_homogeneous 1 f le_rfl
    have hFir :=
      (unscaledHomogenize_absolute_irreducible_iff f hf0).mpr hir
    let Hc := fun j => scaledHomogenize M 1 (G j)
    have hHc := fun j => scaledHomogenize_homogeneous 1 _ (hG j)
    let z : Fin (Fintype.card S) → IntPoint (1 + 3) := fun i => Fin.cons 1 (x i)
    have hz : ∀ i, eval (z i) F = 0 := by
      intro i
      rw [← affineChart_eval, affineChart_scaledHomogenize_one]
      grind
    have he : (Matrix.of fun i j => eval (z i) (Hc j)) =
        Matrix.of fun i j => eval (x i) (G j) := by
      ext i j
      change eval (Fin.cons 1 (x i)) (scaledHomogenize M 1 (G j)) = _
      rw [← affineChart_eval, affineChart_scaledHomogenize_one]
      rfl
    have hrows' : LinearIndependent ℚ
        ((Matrix.of fun i j => eval (z i) (Hc j)).map ((↑) : ℤ → ℚ)).row := by
      rw [he]
      exact hrows
    have hchart : projectivePlaneChart (0 : Fin (1 + 3)) F = f := by
      simp only [projectivePlaneChart, Equiv.swap_self, Equiv.coe_refl, rename_id_apply, F,
        affineChart_scaledHomogenize_one]
    rw [← he]
    have hev : IsIndependentEvaluation F M Hc z :=
      ⟨hHc, fun i => primitive_affine_integer_coordinates (x i), hz, hrows'⟩
    obtain ⟨bad, hmem⟩ := exists_hypersurface_bad_prime_finset F hF hd hFir
    have hFdegree := hF.totalDegree (scaledHomogenize_ne_zero _ one_ne_zero hf0)
    have hheight : (integerCoefficientHeight F : ℝ) ≤ H := by
      rw [show F = scaledHomogenize f.totalDegree 1 f from rfl,
        integerCoefficientHeight_scaledHomogenize_one]
      exact integerCoefficientHeight_le f (by linarith) hcoeff
    have hc := hypersurface_and_congruence_prime_charge F hFir (hFdegree ▸ hd) H hH
      (fun e => (coefficient_abs_le_integerCoefficientHeight F e).trans hheight) bad P
      (fun p hp => by grind) hres.prime
    change (∑ p ∈ bad ∪ P, Real.log p / p) ≤
      congruenceHeightCharge (1 + 3) F.totalDegree H (∑ p ∈ P, Real.log p) at hc
    rw [hFdegree] at hc
    have hh := hypersurface_log_lower_at_rank_of_local_divisors_congruence (n := 1) hN hd (bad ∪ P) P
      subset_union_right hres.prime (fun _ => hypersurfaceMultiplicityExponent (1 + 1) 1 (Fintype.card S))
      (one_pos.trans_le (Int.Matrix.one_le_minorGcd hev.rows_linearIndependent))
      (fun p hp hcut => ?_) (fun p hp => ?_)
    · have he : hypersurfaceDeterminantMain 1 (Fintype.card S) - (1 + 2 : ℝ) * (Fintype.card S) ≤
          (hypersurfaceMultiplicityExponent (1 + 1) 1 (Fintype.card S) : ℝ) := by
        have he := local_exponent_separated_lower_bound (1 + 1) (Fintype.card S) _ (by omega) one_pos
          (fun K => hypersurfaceMultiplicityExponent_cutoff_pos (1 + 1) (Fintype.card S) K (by omega) one_pos)
        simpa only [Nat.cast_one, div_one, hypersurfaceDeterminantMain,
          Nat.cast_add, Nat.cast_one, show (1 : ℝ) + 1 + 1 = 1 + 2 by ring] using he
      have hsum : 0 ≤ ∑ p ∈ P, Real.log (p : ℝ) :=
        sum_nonneg fun p _ => Real.log_natCast_nonneg p
      have hmul := mul_le_mul_of_nonneg_right he hsum
      rw [← mul_sum] at hh
      have := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤
        factorialRoot 1 / (1 + 2 : ℝ) * ((Fintype.card S) : ℝ) ^ (1 + 1 / (1 + 1 : ℝ)) * (1 + 1))
      unfold hypersurfaceRankLowerBound at hh
      unfold affineCongruenceDeterminantLower
      norm_num [factorialRoot] at hh this hmul ⊢
      linarith
    · have : Fact p.Prime := ⟨(mem_filter.mp (mem_sdiff.mp hp).1).2⟩
      obtain ⟨hf0, hir⟩ := hypersurface_good_reduction F p fun hb =>
        (mem_sdiff.mp hp).2 (mem_union_left P ((hmem p).mpr ⟨mod_cast hcut, hb⟩))
      simpa only [hypersurfaceDeterminantMain_div] using
        projective_hypersurface_minorGcd_dvd F hF hd hf0 hir hcut Hc hev.isHomogeneous z hev.primitive
          hev.eval_eq_zero
    · let : Fact p.Prime := ⟨hres.prime p hp⟩
      obtain ⟨j, hj⟩ := hres.smooth p hp
      rw [← hchart] at hj
      obtain ⟨μ, hμ, _, hpow, hcomp⟩ := exists_hypersurface_reduction_multiplicity (p := p)
        (projectivePlaneChart 0 F) (a p) (fun h => by simp [h] at hj)
        (by simpa [hchart] using hres.eval_eq_zero p hp)
      obtain rfl : μ = 1 := by
        rw [originShift_map] at hpow
        exact origin_order_eq_one_of_smooth _ _ hμ hpow ⟨j, hj⟩
      apply Finset.dvd_gcd
      intro S' _
      rw [Matrix.plucker_row_eq_det_submatrix]
      exact projective_hypersurface_local_det_divisibility F hF _ (fun j => hev.isHomogeneous _) z
        0 (a p) hpow hcomp (fun i => isCoprime_one_right)
        (fun i j => by simpa [z] using hres.dvd_sub p hp i j) hev.eval_eq_zero
  refine ⟨g, hg0, hgnd, le_trans (mod_cast hgdeg) hM, ?_⟩
  intro y hy
  obtain ⟨i, hi⟩ := ex.surjective ⟨y, hy⟩
  have hh := hgz i
  change eval (ex i).val g = 0 at hh
  simpa [hi] using hh

