module

public import CCDN.Algebra.ProjectiveTranslation
public import CCDN.AuxiliaryPolynomial.DegreeBound
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
public import CCDN.AuxiliaryPolynomial.Nonmultiple
import CCDN.Algebra.HomogeneousLinearDescent
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.Algebra.PrimitiveNormalization
import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeCoordinates
import CCDN.AuxiliaryPolynomial.HypersurfacePositionHeight
import CCDN.AuxiliaryPolynomial.HypersurfaceRankArchimedean
import CCDN.AuxiliaryPolynomial.HypersurfaceRankProfile
import CCDN.Determinant.HomogeneousDeterminantComparison
import CCDN.Determinant.HypersurfaceDeterminantRank
import CCDN.ForMathlib.Log
import CCDN.ForMathlib.MvPolynomial
import CCDN.Height.CountingHypotheses
import CCDN.Plane.IntegerPlaneLogHeight
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma nonabsolute_projective_auxiliary {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (hred : ¬ Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) (map (Int.castRingHom ℚ) f))) :
    ∃ g : MvPolynomial (Fin (n + 1)) ℤ, g ≠ 0 ∧ g.IsHomogeneous d ∧ ¬ f ∣ g ∧
      projectiveZeroLocus (map (Int.castRingHom ℚ) f) ⊆
        projectiveZeroLocus (map (Int.castRingHom ℚ) g) := by
  classical
  let fQ := map (Int.castRingHom ℚ) f
  let φ := algebraMap ℚ (AlgebraicClosure ℚ)
  have hfQ_hom : fQ.IsHomogeneous d := hf.map _
  have hmap0 : map φ fQ ≠ 0 := fun he =>
    hir.ne_zero ((map_injective φ φ.injective) (by simpa using he))
  have hmapu : ¬ IsUnit (map φ fQ) := fun hu => by
    have he := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
    rw [(hfQ_hom.map _).totalDegree hmap0] at he; omega
  have hfac : ∃ g h : MvPolynomial (Fin (n + 1)) (AlgebraicClosure ℚ),
      map φ fQ = g * h ∧ ¬ IsUnit g ∧ ¬ IsUnit h := by
    by_contra! hn
    exact hred ⟨hmapu, fun g h he => if hu : IsUnit g then Or.inl hu else Or.inr (hn g h he hu)⟩
  obtain ⟨g, h, hfac, hgu, hhu⟩ := hfac
  have hg0 : g ≠ 0 := fun he => hmap0 (by simp [hfac, he])
  have hh0 : h ≠ 0 := fun he => hmap0 (by simp [hfac, he])
  obtain ⟨hdegrees, htop⟩ := homogeneous_factorization_top (hfQ_hom.map _) hmap0 hg0 hh0 hfac
  obtain ⟨g₀, hg₀, hg₀hom, hgz⟩ := exists_nonzero_homogeneous_linear_descent (k := ℚ)
    (homogeneousComponent g.totalDegree g) (homogeneousComponent_totalDegree_ne_zero hg0)
    (homogeneousComponent_isHomogeneous _ _)
  obtain ⟨h₀, hh₀, hh₀hom, hhz⟩ := exists_nonzero_homogeneous_linear_descent (k := ℚ)
    (homogeneousComponent h.totalDegree h) (homogeneousComponent_totalDegree_ne_zero hh0)
    (homogeneousComponent_isHomogeneous _ _)
  have hgd := totalDegree_pos_of_ne_zero_of_not_isUnit hg0 hgu
  have hhd := totalDegree_pos_of_ne_zero_of_not_isUnit hh0 hhu
  have hq0 : g₀ * h₀ ≠ 0 := mul_ne_zero hg₀ hh₀
  have hqhom : (g₀ * h₀).IsHomogeneous d := hdegrees ▸ hg₀hom.mul hh₀hom
  have hqnd : ¬ fQ ∣ g₀ * h₀ := fun hdiv => by
    rcases hir.prime.dvd_or_dvd hdiv with hgdiv | hhdiv
    · have he := totalDegree_le_of_dvd_of_isDomain hgdiv hg₀
      rw [hfQ_hom.totalDegree hir.ne_zero, hg₀hom.totalDegree hg₀] at he; omega
    · have he := totalDegree_le_of_dvd_of_isDomain hhdiv hh₀
      rw [hfQ_hom.totalDegree hir.ne_zero, hh₀hom.totalDegree hh₀] at he; omega
  obtain ⟨G, a, _, ha, he⟩ := exists_primitive_integer_model (g₀ * h₀) hq0
  have hG0 : G ≠ 0 := fun hz => mul_ne_zero (C_eq_zero.not.mpr ha) hq0 (by simpa [hz] using he.symm)
  refine ⟨G, hG0, rational_scalar_model_homogeneous he hqhom, fun hdiv => hqnd ?_, fun x hx => ?_⟩
  · have hh := dvd_mul_of_dvd_right (map_dvd (map (Int.castRingHom ℚ)) hdiv) (C a⁻¹)
    simpa only [fQ, he, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, C_1, one_mul] using hh
  · refine (rational_scalar_model_zero_iff ha he x.rep).mpr ?_
    have hev := congrArg φ hx
    rw [map_eval, htop, eval_mul, map_zero] at hev
    rw [eval_mul]
    exact (mul_eq_zero.mp hev).elim (fun h1 => by rw [hgz x.rep h1, zero_mul])
      (fun h2 => by rw [hhz x.rep h2, mul_zero])

private lemma hypersurface_kernel_ratio_lower {r d M s : ℕ} (hd : 0 < d) (hdM : d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M) :
    1 / ((d : ℝ) * (r + 1 : ℝ)) - 1 / (M : ℝ) ≤
      ((r + 1 + (M - d)).choose (M - d) : ℝ) / ((M : ℝ) * s) := by
  obtain ⟨hlo, hhi⟩ := hypersurface_rank_binomial_bounds hdM hr
  have hs : 0 < s := lt_of_lt_of_le
    (Nat.mul_pos hd (Nat.choose_pos (by omega : r ≤ r + (M - d)))) hlo
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hs0 : (0 : ℝ) < s := mod_cast hs
  have hM0 : (0 : ℝ) < M := mod_cast lt_of_lt_of_le hd hdM
  have hr0 : (0 : ℝ) < r + 1 := by positivity
  let K : ℝ := (r + 1 + (M - d)).choose (M - d)
  let Qhi : ℝ := (r + M).choose r
  have hhigh : (s : ℝ) ≤ (d : ℝ) * Qhi := by dsimp [Qhi]; exact_mod_cast hhi
  have hR : ((r : ℝ) + M + 1) * Qhi = ((s : ℝ) + K) * (r + 1) := by
    have hh : (r + M + 1) * (r + M).choose r = (r + 1 + M).choose (r + 1) * (r + 1) := by
      rw [show r + 1 + M = r + M + 1 by omega]
      exact Nat.add_one_mul_choose_eq (r + M) r
    rw [Nat.choose_symm_add (a := r + 1) (b := M), ← hr] at hh
    have hhR := congrArg (fun x : ℕ => (x : ℝ)) hh
    push_cast [Nat.cast_sub hdM] at hhR
    exact hhR
  have hRmul : ((M : ℝ) + r + 1) * s ≤ (d : ℝ) * (r + 1) * ((s : ℝ) + K) := by
    have hh := mul_le_mul_of_nonneg_left hhigh (show 0 ≤ (r : ℝ) + M + 1 by positivity)
    nlinarith
  change 1 / ((d : ℝ) * (r + 1 : ℝ)) - 1 / (M : ℝ) ≤ K / ((M : ℝ) * s)
  rw [le_div_iff₀ (mul_pos hM0 hs0)]
  field_simp
  nlinarith [mul_le_mul_of_nonneg_right hd1 (mul_nonneg hr0.le hs0.le)]

private lemma hypersurface_rank_root_bounds {r d M s : ℕ} (hrpos : 0 < r) (hdM : d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M) :
    (d : ℝ) ^ (1 / (r : ℝ)) * ((M : ℝ) - d + 1) ≤
        (r.factorial : ℝ) ^ (1 / (r : ℝ)) * (s : ℝ) ^ (1 / (r : ℝ)) ∧
      (r.factorial : ℝ) ^ (1 / (r : ℝ)) * (s : ℝ) ^ (1 / (r : ℝ)) ≤
        (d : ℝ) ^ (1 / (r : ℝ)) * ((M : ℝ) + r) := by
  obtain ⟨hl, hu⟩ := hypersurface_rank_power_bounds hdM hr
  have hfac : (0 : ℝ) < r.factorial := by positivity
  have hmd : (0 : ℝ) ≤ (M : ℝ) - d + 1 := by linarith [show (d : ℝ) ≤ M from mod_cast hdM]
  have hlroot := Real.rpow_le_rpow (mul_nonneg (Nat.cast_nonneg d) (pow_nonneg hmd r))
    ((div_le_iff₀ hfac).mp hl) (by positivity : 0 ≤ 1 / (r : ℝ))
  have huroot := Real.rpow_le_rpow (mul_nonneg (Nat.cast_nonneg s) hfac.le)
    ((le_div_iff₀ hfac).mp hu) (by positivity : 0 ≤ 1 / (r : ℝ))
  rw [Real.mul_rpow (Nat.cast_nonneg d) (pow_nonneg hmd r),
    Real.mul_rpow (Nat.cast_nonneg s) hfac.le, one_div,
    Real.pow_rpow_inv_natCast hmd hrpos.ne'] at hlroot
  rw [Real.mul_rpow (Nat.cast_nonneg s) hfac.le,
    Real.mul_rpow (Nat.cast_nonneg d) (by positivity), one_div,
    Real.pow_rpow_inv_natCast (by positivity) hrpos.ne'] at huroot
  exact ⟨by simpa only [one_div, mul_comm] using hlroot,
    by simpa only [one_div, mul_comm] using huroot⟩

private lemma hypersurface_rank_log_lower {r d M s : ℕ} (hd : 0 < d) (hM : 2 * d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M) :
    Real.log d + (r : ℝ) * Real.log M -
      ((r : ℝ) * Real.log 2 + Real.log (r.factorial : ℝ)) ≤ Real.log s := by
  have hdM : d ≤ M := by omega
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have hM0 : (0 : ℝ) < M := mod_cast lt_of_lt_of_le hd hdM
  have hdMR : 2 * (d : ℝ) ≤ M := mod_cast hM
  have hfac : (0 : ℝ) < r.factorial := by positivity
  obtain ⟨hl, _⟩ := hypersurface_rank_power_bounds hdM hr
  have hl' : (d : ℝ) * ((M : ℝ) / 2) ^ r / (r.factorial : ℝ) ≤ s :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) r) hd0.le) hfac.le).trans hl
  have hlow := Real.log_le_log (by positivity) hl'
  rw [Real.log_div (by positivity) hfac.ne', Real.log_mul hd0.ne' (by positivity),
    Real.log_pow, Real.log_div hM0.ne' (by norm_num)] at hlow
  linarith

private lemma auxiliary_reciprocal_bound {r d M X a : ℝ} (hr : 0 ≤ r) (hd : 1 ≤ d)
    (hM : 2 * d ≤ M) (hX : 0 < X) (ha : X * (M - d) / ((r + 1) * M) ≤ a) :
    0 < a ∧ 1 / a ≤ (r + 1) / X * (1 + 2 * d / M) := by
  have hd0 : 0 < d := by linarith
  have hM0 : 0 < M := by linarith
  have hr1 : 0 < r + 1 := by linarith
  have hMd : 0 < M - d := by linarith
  have ha0 : 0 < a := (by positivity : 0 < X * (M - d) / ((r + 1) * M)).trans_le ha
  refine ⟨ha0, (div_le_iff₀ ha0).mpr ?_⟩
  refine (show 1 ≤ (r + 1) / X * (1 + 2 * d / M) * (X * (M - d) / ((r + 1) * M)) by
    field_simp; nlinarith [mul_nonneg hd0.le (sub_nonneg.mpr hM)]).trans
    (mul_le_mul_of_nonneg_left ha (by positivity))

private lemma auxiliary_kernel_quotient_bound {r d M X a k : ℝ}
    (hr : 0 ≤ r) (hd : 1 ≤ d) (hM : 0 < M) (hX : 0 < X) (ha : 0 < a) (hk : 0 ≤ k)
    (hupper : a ≤ X * (M + r) / ((r + 1) * M))
    (hlower : 1 / (d * (r + 1)) - 1 / M ≤ k) :
    1 / (d * X) - (2 * r + 1) / (X * M) ≤ k / a := by
  let q := 1 / (d * X) - (2 * r + 1) / (X * M)
  by_cases hq : q ≤ 0
  · exact hq.trans (div_nonneg hk ha.le)
  have hq0 : 0 ≤ q := le_of_not_ge hq
  have hd0 : 0 < d := by linarith
  have hr1 : 0 < r + 1 := by linarith
  refine (le_div_iff₀ ha).mpr ((mul_le_mul_of_nonneg_left hupper hq0).trans ?_)
  refine (show q * (X * (M + r) / ((r + 1) * M)) ≤ 1 / (d * (r + 1)) - 1 / M by
    dsimp only [q]; field_simp
    nlinarith [mul_nonneg (mul_nonneg hr hM.le) (show 0 ≤ d - 1 by linarith),
      mul_nonneg (mul_nonneg hd0.le hr) (show 0 ≤ 2 * r + 1 by linarith)]).trans hlower

private lemma auxiliary_small_height_bracket_bound {r d M X a k u b l : ℝ}
    (hr : 0 ≤ r) (hd : 1 ≤ d) (hM : 2 * d ≤ M) (hX : 0 < X)
    (halow : X * (M - d) / ((r + 1) * M) ≤ a)
    (haup : a ≤ X * (M + r) / ((r + 1) * M))
    (hk : 0 ≤ k) (hklow : 1 / (d * (r + 1)) - 1 / M ≤ k)
    (hb : 0 ≤ b) (hl : 0 ≤ l) (hheight : l ≤ 2 * d * (r + 1) * b)
    (hscale : d * b ≤ X * M) (hcomparison : a * u ≤ b - k * l) :
    u ≤ (r + 1) / X * b - l / (d * X) + 4 * (r + 1) ^ 2 := by
  have hM0 : 0 < M := by linarith
  obtain ⟨ha, hrecip⟩ := auxiliary_reciprocal_bound hr hd hM hX halow
  have hquot := auxiliary_kernel_quotient_bound hr hd hM0 hX ha hk haup hklow
  have hu : u ≤ b / a - (k / a) * l := by
    have hh := (le_div_iff₀ ha).mpr (by nlinarith [hcomparison] : u * a ≤ b - k * l)
    convert hh using 1; ring
  have hb' : b / a ≤ ((r + 1) / X * (1 + 2 * d / M)) * b := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using
      mul_le_mul_of_nonneg_right hrecip hb
  have hl' := mul_le_mul_of_nonneg_right hquot hl
  have herr1 : 2 * (r + 1) * d * b / (X * M) ≤ 2 * (r + 1) :=
    (div_le_iff₀ (mul_pos hX hM0)).mpr
      (by nlinarith [mul_le_mul_of_nonneg_left hscale (show 0 ≤ 2 * (r + 1) by linarith)])
  have herr2 : (2 * r + 1) * l / (X * M) ≤ 2 * (2 * r + 1) * (r + 1) :=
    (div_le_iff₀ (mul_pos hX hM0)).mpr
      (by nlinarith [mul_le_mul_of_nonneg_left hheight (show 0 ≤ 2 * r + 1 by linarith),
        mul_le_mul_of_nonneg_left hscale (show 0 ≤ 2 * (2 * r + 1) * (r + 1) by positivity)])
  have he : ((r + 1) / X * (1 + 2 * d / M)) * b - (1 / (d * X) - (2 * r + 1) / (X * M)) * l =
      (r + 1) / X * b - l / (d * X) + 2 * (r + 1) * d * b / (X * M) +
        (2 * r + 1) * l / (X * M) := by ring
  have hbound : u ≤ ((r + 1) / X * (1 + 2 * d / M)) * b -
      (1 / (d * X) - (2 * r + 1) / (X * M)) * l := by nlinarith [hb', hl']
  rw [he] at hbound; nlinarith

private lemma auxiliary_large_height_bracket_bound {r d M X a k u b l h T : ℝ}
    (hr : 0 ≤ r) (hd : 1 ≤ d) (hM : 8 * d * (r + 1) ≤ M) (hX : 0 < X)
    (halow : X * (M - d) / ((r + 1) * M) ≤ a)
    (haup : a ≤ X * (M + r) / ((r + 1) * M))
    (hk : 0 ≤ k) (hklow : 1 / (d * (r + 1)) - 1 / M ≤ k)
    (hb : 0 ≤ b) (hl : 0 ≤ l) (hT : 0 ≤ T)
    (hheight : 2 * d * (r + 1) * b ≤ h) (hposition : h ≤ l + T * d * X)
    (hcomparison : a * u ≤ b - k * l) :
    u ≤ T - h / (8 * d * X) := by
  have hd0 : 0 < d := by linarith
  have hM2 : 2 * d ≤ M := by nlinarith [mul_nonneg hd0.le hr]
  have hM0 : 0 < M := by linarith
  obtain ⟨ha, hrecip⟩ := auxiliary_reciprocal_bound hr hd hM2 hX halow
  have hquot := auxiliary_kernel_quotient_bound hr hd hM0 hX ha hk haup hklow
  have hrecip' : 1 / a ≤ 5 * (r + 1) / (4 * X) := hrecip.trans
    (by field_simp; nlinarith [mul_nonneg hd0.le hr, mul_nonneg hr (sub_nonneg.mpr hM)])
  have hquot' : 3 / (4 * d * X) ≤ k / a :=
    (by field_simp; nlinarith [mul_nonneg hd0.le hr] :
      3 / (4 * d * X) ≤ 1 / (d * X) - (2 * r + 1) / (X * M)).trans hquot
  have hu : u ≤ b / a - (k / a) * l := by
    have hh := (le_div_iff₀ ha).mpr (by nlinarith [hcomparison] : u * a ≤ b - k * l)
    convert hh using 1; ring
  have hb' : b / a ≤ (5 * (r + 1) / (4 * X)) * b := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using
      mul_le_mul_of_nonneg_right hrecip' hb
  have hl' := mul_le_mul_of_nonneg_right hquot' hl
  have hu' : u ≤ (10 * d * (r + 1) * b - 6 * l) / (8 * d * X) :=
    (by linarith : u ≤ (5 * (r + 1) / (4 * X)) * b - (3 / (4 * d * X)) * l).trans_eq
      (by field_simp; ring)
  have hden : 0 < 8 * d * X := by positivity
  have hmul := (le_div_iff₀ hden).mp hu'
  refine le_of_mul_le_mul_right ?_ hden
  rw [show (T - h / (8 * d * X)) * (8 * d * X) = T * (8 * d * X) - h by field_simp]
  nlinarith [mul_nonneg (mul_nonneg hT hd0.le) hX.le]

private lemma normalized_no_auxiliary_comparison {n d M t : ℕ}
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    (hd : 0 < d) (hdM : d ≤ M)
    (z : Fin t → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0) {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i, InBox (z i) B)
    (bad : Finset ℕ) (hbad : ∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction f p)
    (hnone : ¬ ∃ g, IsPointAuxiliary f g M z)
    {A E₀ : ℝ} (_hA : 0 < A) (hcharge : ∑ p ∈ bad, Real.log p / p ≤ Real.log A + E₀) :
    ∃ s : ℕ, 0 < s ∧ s + (n + 2 + (M - d)).choose (M - d) = (n + 2 + M).choose M ∧
      ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) * (s : ℝ) ^ (1 / (n + 1 : ℝ)) /
          ((n + 2 : ℝ) * M) *
        (Real.log s - (n + 1 : ℝ) * (4 * Real.log d + Real.log A) -
          (hypersurfaceDeterminantError n + (n + 1 : ℝ) * E₀ +
            (n + 2 : ℝ) * hypersurfaceArchimedeanError (n + 1) /
              ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)))) ≤
        Real.log B - ((n + 2 + (M - d)).choose (M - d) : ℝ) / ((M : ℝ) * s) *
          Real.log |((MonomialOrder.lex.leadingCoeff f : ℤ) : ℝ)| := by
  obtain ⟨s, a, _, _, hr, hi, hupper⟩ :=
    homogeneous_no_auxiliary_box_comparison MonomialOrder.lex f hf hf0 hdM z hz hB hbox
      (dvd_of_not_exists_isPointAuxiliary hnone)
  have hs : 0 < s := by
    have hr' := hr
    rw [← Nat.choose_symm_add (a := n + 2) (b := M - d),
      ← Nat.choose_symm_add (a := n + 2) (b := M)] at hr'
    have hmon := Nat.choose_le_choose (n + 2) (show n + 2 + (M - d) ≤ n + 1 + M by omega)
    have hpas : (n + 2 + M).choose (n + 2) =
        (n + 1 + M).choose (n + 1) + (n + 1 + M).choose (n + 2) := by
      convert Nat.choose_succ_succ' (n + 1 + M) (n + 1) using 1; congr 1; omega
    have hp : 0 < (n + 1 + M).choose (n + 1) := Nat.choose_pos (by omega)
    omega
  let F := fun j => (monomial (homogeneousMonomials (n + 2) M j) 1 : MvPolynomial (Fin (n + 3)) ℤ)
  have hF (j) : (F j).IsHomogeneous M :=
    isHomogeneous_monomial _ (homogeneousMonomials_degree (n + 2) M j)
  have he : (Matrix.of fun i j => eval ((z ∘ a) i) (F j)) =
      evaluationMatrix (homogeneousMonomials (n + 2) M) (z ∘ a) := by
    ext i j; simp [F, evaluationMatrix, eval_monomial]
  have hlower := hypersurface_determinant_log_lower_at_rank hs f hf hd F hF (z ∘ a)
    (fun i => hprim (a i)) (fun i => hz (a i)) (by rw [he]; exact hi) bad
    fun p _ hp hcut => hasGoodReduction_of_not_mem hbad p (Finset.mem_sdiff.mp hp).2 hcut
  rw [he] at hlower
  have hc := hlower.trans hupper
  unfold hypersurfaceRankLowerBound at hc
  have hs0 : (0 : ℝ) < s := mod_cast hs
  have hM0 : (0 : ℝ) < M := mod_cast lt_of_lt_of_le hd hdM
  have hnN : n + 1 + 1 = n + 2 := by omega
  have harch := hypersurface_rank_archimedean_error (r := n + 1) (by omega) hd hdM
    (by simpa only [hnN] using hr)
  simp only [hnN, Nat.cast_add, Nat.cast_one] at harch
  have hkernel : ((n + 2 + M).choose M : ℝ) - s = (n + 2 + (M - d)).choose (M - d) := by
    have hh : (s : ℝ) + ((n + 2 + (M - d)).choose (M - d) : ℝ) = (n + 2 + M).choose M := mod_cast hr
    linarith
  rw [hkernel] at hc
  let fac := ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ))
  have hfac0 : 0 < fac := by dsimp [fac]; positivity
  have hcost := mul_le_mul_of_nonneg_left hcharge
    (show 0 ≤ fac / (n + 2 : ℝ) * (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) * (n + 1 : ℝ) by positivity)
  let T := Real.log s - (n + 1 : ℝ) * (4 * Real.log d + Real.log A) -
    (hypersurfaceDeterminantError n + (n + 1 : ℝ) * E₀)
  let U := (n + 2 : ℝ) * hypersurfaceArchimedeanError (n + 1) / fac
  have hsplit : fac / (n + 2 : ℝ) * (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) * (T - U) =
      fac / (n + 2 : ℝ) * (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) * T -
        hypersurfaceArchimedeanError (n + 1) * (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) := by
    dsimp only [U]; field_simp
  have hraw : fac / (n + 2 : ℝ) * (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) * (T - U) ≤
      s * M * Real.log B - ((n + 2 + (M - d)).choose (M - d) : ℝ) *
        Real.log |((MonomialOrder.lex.leadingCoeff f : ℤ) : ℝ)| := by
    rw [hsplit]; dsimp only [T, fac] at hcost ⊢; unfold factorialRoot at hc; linarith
  refine ⟨s, hs, hr, ?_⟩
  have hquot := div_le_div_of_nonneg_right hraw (mul_nonneg hM0.le hs0.le)
  convert hquot using 1
  · rw [Real.rpow_add hs0, Real.rpow_one]
    dsimp only [T, U, fac]; field_simp; ring
  · field_simp

private lemma auxDegreeBound_translate_le {n d : ℕ} (hd : 0 < d) {B b H h : ℝ} (hB : 1 ≤ B)
    (hb : 0 ≤ b) (hh0 : 0 < h) (hhH : h ≤ H) :
    auxDegreeBound n d (((d : ℝ) + 1) * B) b H ≤
      (Real.exp ((n + 2 : ℝ) ^ 2 / (n + 1 : ℝ)) + (n + 3 : ℝ)) * auxDegreeBound n d B b h := by
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  let R := ((d : ℝ) + 1) * B
  let D := (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))
  let α := boxExponent n d
  let q := heightExponent n d
  let Q := D * b * B ^ α / h ^ q
  let l := (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B
  let E := Real.exp ((n + 2 : ℝ) ^ 2 / (n + 1 : ℝ))
  have hfactor : ((d : ℝ) + 1) ^ α ≤ E := by
    rw [Real.rpow_def_of_pos (by positivity)]
    refine Real.exp_le_exp.mpr ?_
    have hh := mul_le_mul_of_nonneg_right
      (log_nat_add_one_le_root (r := n + 1) (by omega) hd)
      (show 0 ≤ α by dsimp [α, boxExponent, degreeRoot]; positivity)
    convert hh using 1
    dsimp [α, boxExponent, degreeRoot]
    simp only [Nat.cast_add, Nat.cast_one, hnR]; field_simp
  have hRpow : R ^ α ≤ E * B ^ α := by
    rw [show R = ((d : ℝ) + 1) * B from rfl, Real.mul_rpow (by positivity) (by linarith)]
    exact mul_le_mul_of_nonneg_right hfactor (by positivity)
  have hQ' : D * b * R ^ α / H ^ q ≤ E * Q := by
    calc D * b * R ^ α / H ^ q
        ≤ D * b * R ^ α / h ^ q :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (Real.rpow_le_rpow hh0.le hhH (by dsimp [q, heightExponent]; positivity))
      _ ≤ D * b * (E * B ^ α) / h ^ q :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hRpow (by positivity)) (by positivity)
      _ = E * Q := by dsimp [Q]; ring
  have hlogcost : (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log ((d : ℝ) + 1) ≤ (n + 2 : ℝ) * d := by
    have hh := mul_le_mul_of_nonneg_left
      (log_nat_add_one_le_root (r := n + 1) (by omega) hd)
      (Real.rpow_nonneg hd0.le (1 - 1 / (n + 1 : ℝ)))
    have he : (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * (d : ℝ) ^ (1 / (n + 1 : ℝ)) = d := by
      rw [← Real.rpow_add hd0, sub_add_cancel, Real.rpow_one]
    simp only [Nat.cast_add, Nat.cast_one, hnR] at hh
    rwa [← mul_left_comm, he] at hh
  have hdD : (d : ℝ) ≤ D := le_rpow_four_sub_inv hd
  have hl' : (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log R ≤ l + (n + 2 : ℝ) * D := by
    dsimp only [R, l]
    rw [Real.log_mul (by positivity) (by linarith), mul_add]
    linarith [mul_le_mul_of_nonneg_left hdD (show 0 ≤ (n + 2 : ℝ) by positivity)]
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hl0 : 0 ≤ l := mul_nonneg (Real.rpow_nonneg hd0.le _) (Real.log_nonneg hB)
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  change D * b * R ^ α / H ^ q + (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log R + D ≤
    (E + (n + 3 : ℝ)) * (Q + l + D)
  nlinarith [mul_nonneg (show 0 ≤ (n + 3 : ℝ) by positivity) hQ0,
    mul_nonneg (show 0 ≤ E + (n + 2 : ℝ) by positivity) hl0,
    mul_nonneg hE0 hD0]

private lemma small_height_step {n d t : ℕ}
    (model : MvPolynomial (Fin (n + 3)) ℤ) (hmodel_hom : model.IsHomogeneous d)
    (hmodel0 : model ≠ 0) (hd : 0 < d)
    (w : Fin t → IntPoint (n + 3)) (hw_prim : ∀ i, Finset.univ.gcd (w i) = 1)
    (hw_eval : ∀ i, eval (w i) model = 0) {R_box : ℝ} (hR1 : 1 ≤ R_box)
    (hw_box : ∀ i, InBox (w i) R_box)
    (bad : Finset ℕ) (hbad_m : ∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction model p)
    {H T_pos err_s K_pos : ℝ} (hH : 1 ≤ H) (hcg : CoefficientHeightLE model H)
    (hsmall : Real.log H ≤ 2 * d * (n + 2 : ℝ) * Real.log R_box)
    (hposition : Real.log H ≤ Real.log |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)| +
      T_pos * d * degreeRoot n d)
    (herr_s : err_s = (hypersurfaceDeterminantError n +
      (n + 2 : ℝ) * hypersurfaceArchimedeanError (n + 1) /
        ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) +
      ((n + 1 : ℝ) * Real.log 2 + Real.log ((n + 1).factorial : ℝ)) +
      4 * (n + 2 : ℝ) ^ 2) / (n + 1 : ℝ))
    (hCs : Real.exp (T_pos / (n + 1 : ℝ)) * Real.exp err_s ≤ K_pos)
    (hK_pos_4 : 4 ≤ K_pos) :
    ∃ M : ℕ, (M : ℝ) ≤ K_pos * auxDegreeBound n d R_box (primeSetFactor bad) H ∧
      ∃ g, IsPointAuxiliary model g M w := by
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hnN : n + 1 + 1 = n + 2 := by omega
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  let L_lead := |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)|
  have hL1 : 1 ≤ L_lead := by
    dsimp only [L_lead]; exact_mod_cast Int.one_le_abs
      (MonomialOrder.lex.leadingCoeff_ne_zero_iff.mpr hmodel0)
  have hL0 : 0 < L_lead := by linarith
  let b_fac := primeSetFactor bad
  have hb0 : 0 < b_fac := Real.exp_pos _
  let thr := Real.exp err_s * (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b_fac *
    R_box ^ boxExponent n d / L_lead ^ heightExponent n d
  have hthr0 : 0 ≤ thr := by dsimp [thr, boxExponent, heightExponent]; positivity
  let l := (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log R_box
  have hl0 : 0 ≤ l := mul_nonneg (Real.rpow_nonneg hd0.le _) (Real.log_nonneg hR1)
  obtain ⟨M, hM2, hscale, hthreshold, hbound⟩ :=
    auxiliary_integer_degree_selection (2 * d) hl0 hthr0
  have hexists : ∃ g, IsPointAuxiliary model g M w := by
    by_contra hnone
    have hdM : d ≤ M := by omega
    obtain ⟨s, _, hr, hc⟩ := normalized_no_auxiliary_comparison model hmodel_hom hmodel0 hd hdM
      w hw_prim hw_eval hR1 hw_box bad hbad_m hnone hb0 (by rw [Real.log_exp, add_zero])
    simp only [mul_zero, add_zero] at hc
    have hr' : s + (n + 1 + 1 + (M - d)).choose (M - d) = (n + 1 + 1 + M).choose M := by
      simpa only [hnN] using hr
    obtain ⟨hroot_lo, hroot_hi⟩ := hypersurface_rank_root_bounds (r := n + 1) (by omega) hdM hr'
    simp only [Nat.cast_add, Nat.cast_one] at hroot_lo hroot_hi
    have hX : 0 < (d : ℝ) ^ (1 / (n + 1 : ℝ)) := by positivity
    have halow : (d : ℝ) ^ (1 / (n + 1 : ℝ)) * ((M : ℝ) - d) / ((n + 2 : ℝ) * M) ≤
        ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) * (s : ℝ) ^ (1 / (n + 1 : ℝ)) /
          ((n + 2 : ℝ) * M) :=
      div_le_div_of_nonneg_right (by linarith only [hroot_lo, hX]) (by positivity)
    have haup : ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) * (s : ℝ) ^ (1 / (n + 1 : ℝ)) /
          ((n + 2 : ℝ) * M) ≤
        (d : ℝ) ^ (1 / (n + 1 : ℝ)) * ((M : ℝ) + (n + 1 : ℝ)) / ((n + 2 : ℝ) * M) :=
      div_le_div_of_nonneg_right hroot_hi (by positivity)
    have hk := hypersurface_kernel_ratio_lower (r := n + 1) hd hdM hr'
    simp only [hnN, Nat.cast_add, Nat.cast_one, hnR] at hk
    have hht_L : Real.log L_lead ≤ 2 * d * (n + 2 : ℝ) * Real.log R_box :=
      (Real.log_le_log hL0 (hcg (MonomialOrder.lex.degree model))).trans hsmall
    have hsc : (d : ℝ) * Real.log R_box ≤ (d : ℝ) ^ (1 / (n + 1 : ℝ)) * M := by
      have hh := mul_le_mul_of_nonneg_right hscale hX.le
      dsimp only [l] at hh
      rw [Real.rpow_sub hd0, Real.rpow_one] at hh
      have he : (d : ℝ) / (d : ℝ) ^ (1 / (n + 1 : ℝ)) * Real.log R_box *
          (d : ℝ) ^ (1 / (n + 1 : ℝ)) = d * Real.log R_box := by field_simp
      linarith only [hh, he]
    have hbr := auxiliary_small_height_bracket_bound (r := (n + 1 : ℝ))
      (k := ((n + 2 + (M - d)).choose (M - d) : ℝ) / ((M : ℝ) * s)) (by positivity) hd1
      (mod_cast hM2) hX (by simpa only [hnR] using halow) (by simpa only [hnR] using haup)
      (by positivity) (by simpa only [hnR] using hk) (Real.log_nonneg hR1) (Real.log_nonneg hL1)
      (by simpa only [hnR] using hht_L) hsc (by simpa only [hnR] using hc)
    simp only [hnR] at hbr
    have hlog_s := hypersurface_rank_log_lower (r := n + 1) hd hM2 hr'
    simp only [Nat.cast_add, Nat.cast_one] at hlog_s
    have hraw : (n + 1 : ℝ) * Real.log M ≤
        (n + 2 : ℝ) / (d : ℝ) ^ (1 / (n + 1 : ℝ)) * Real.log R_box -
          Real.log L_lead / ((d : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ))) +
          4 * (n + 2 : ℝ) ^ 2 +
          (hypersurfaceDeterminantError n +
            (n + 2 : ℝ) * hypersurfaceArchimedeanError (n + 1) /
              ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ))) +
          ((n + 1 : ℝ) * Real.log 2 + Real.log ((n + 1).factorial : ℝ)) +
          (4 * (n + 1 : ℝ) - 1) * Real.log d + (n + 1 : ℝ) * Real.log b_fac := by
      linarith only [hbr, hlog_s]
    have hn1_pos : (0 : ℝ) < n + 1 := by positivity
    have hdiv := div_le_div_of_nonneg_right hraw hn1_pos.le
    rw [mul_div_cancel_left₀ (Real.log M) hn1_pos.ne'] at hdiv
    have hlogM : Real.log M ≤ err_s + (4 - 1 / (n + 1 : ℝ)) * Real.log d + Real.log b_fac +
        (n + 2 : ℝ) / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ))) * Real.log R_box -
        Real.log L_lead / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ))) := by
      rw [herr_s]; convert hdiv using 1; field_simp; ring
    have hMle : (M : ℝ) ≤ thr := by
      refine Real.natCast_le_of_log_le_log (lt_of_lt_of_le hd hdM) (by dsimp [thr]; positivity) ?_
      dsimp only [thr, boxExponent, heightExponent, degreeRoot]
      rw [Real.log_div (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) hb0.ne',
        Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp,
        Real.log_rpow hd0, Real.log_rpow (by linarith : 0 < R_box), Real.log_rpow hL0]
      convert hlogM using 1; ring
    exact (not_lt_of_ge hMle) hthreshold
  obtain ⟨g, hg⟩ := hexists
  have hinv : 1 / L_lead ^ heightExponent n d ≤
      Real.exp (T_pos / (n + 1 : ℝ)) / H ^ heightExponent n d := by
    have hq0 : 0 ≤ heightExponent n d := by dsimp [heightExponent, degreeRoot]; positivity
    refine (Real.log_le_log_iff (by positivity) (by positivity)).mp ?_
    rw [Real.log_div one_ne_zero (by positivity),
      Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_one, Real.log_exp,
      Real.log_rpow hL0, Real.log_rpow (by linarith : 0 < H)]
    have he : heightExponent n d * (T_pos * d * degreeRoot n d) = T_pos / (n + 1 : ℝ) := by
      dsimp [heightExponent, degreeRoot]; field_simp
    nlinarith only [mul_le_mul_of_nonneg_left hposition hq0, he]
  have hthr_le : thr ≤ Real.exp (T_pos / (n + 1 : ℝ)) * Real.exp err_s *
      auxMainTerm n d R_box b_fac H := by
    have hm := mul_le_mul_of_nonneg_left hinv
      (show 0 ≤ Real.exp err_s * (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * b_fac *
        R_box ^ boxExponent n d by positivity)
    dsimp only [thr, auxMainTerm]
    convert hm using 1 <;> ring
  refine ⟨M, ?_, g, hg⟩
  push_cast at hbound
  let Q := auxMainTerm n d R_box b_fac H
  let D := (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))
  have hQ0 : 0 ≤ Q := by dsimp [Q, auxMainTerm]; positivity
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hdD : (d : ℝ) ≤ D := le_rpow_four_sub_inv hd
  change (M : ℝ) ≤ K_pos * (Q + l + D)
  nlinarith only [hbound, hthr_le, hd1, hdD,
    mul_le_mul_of_nonneg_right hCs hQ0,
    mul_le_mul_of_nonneg_right (show 1 ≤ K_pos by linarith only [hK_pos_4]) hl0,
    mul_le_mul_of_nonneg_right hK_pos_4 hD0]

private lemma large_height_step {n d t : ℕ}
    (model : MvPolynomial (Fin (n + 3)) ℤ) (hmodel_hom : model.IsHomogeneous d)
    (hmodel0 : model ≠ 0) (hd : 0 < d)
    (w : Fin t → IntPoint (n + 3)) (hw_prim : ∀ i, Finset.univ.gcd (w i) = 1)
    (hw_eval : ∀ i, eval (w i) model = 0) {R_box : ℝ} (hR1 : 1 ≤ R_box)
    (hw_box : ∀ i, InBox (w i) R_box)
    (bad : Finset ℕ) (hbad_m : ∀ p, p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction model p)
    {H T_pos err_l K_pos : ℝ} (hH : 1 ≤ H) (hT_pos : 0 ≤ T_pos)
    (hcharge : ∑ p ∈ bad, Real.log p / p ≤
      Real.log (hypersurfaceHeightConstant (n + 3) * (1 + Real.log H / (d : ℝ) ^ 2)) +
        2 * mertensError + 1)
    (hlarge : 2 * d * (n + 2 : ℝ) * Real.log R_box ≤ Real.log H)
    (hposition : Real.log H ≤ Real.log |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)| +
      T_pos * d * degreeRoot n d)
    (herr_l : err_l = Real.log (8 * (n + 1 : ℝ)) +
      ((hypersurfaceDeterminantError n +
          (n + 1 : ℝ) * (Real.log (hypersurfaceHeightConstant (n + 3)) + 2 * mertensError + 1) +
          (n + 2 : ℝ) * hypersurfaceArchimedeanError (n + 1) /
            ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ))) +
        ((n + 1 : ℝ) * Real.log 2 + Real.log ((n + 1).factorial : ℝ)) + T_pos) / (n + 1 : ℝ))
    (hCl : 8 * (n + 2 : ℝ) + Real.exp err_l + 2 ≤ K_pos) (hK0 : 0 ≤ K_pos) :
    ∃ M : ℕ, (M : ℝ) ≤ K_pos * auxDegreeBound n d R_box (primeSetFactor bad) H ∧
      ∃ g, IsPointAuxiliary model g M w := by
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hnN : n + 1 + 1 = n + 2 := by omega
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  let L_lead := |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)|
  have hL1 : 1 ≤ L_lead := by
    dsimp only [L_lead]; exact_mod_cast Int.one_le_abs
      (MonomialOrder.lex.leadingCoeff_ne_zero_iff.mpr hmodel0)
  let thr_l := Real.exp err_l * (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))
  have hthr_l0 : 0 ≤ thr_l := by dsimp [thr_l]; positivity
  obtain ⟨M, hM8, _, hthreshold, hbound⟩ :=
    auxiliary_integer_degree_selection (8 * d * (n + 2)) le_rfl hthr_l0
  have hexists : ∃ g, IsPointAuxiliary model g M w := by
    by_contra hnone
    have hdM : d ≤ M := by nlinarith
    have hM2 : 2 * d ≤ M := by nlinarith
    let A_ht := 1 + Real.log H / (d : ℝ) ^ 2
    have hHlog : 0 ≤ Real.log H := Real.log_nonneg hH
    have hA_ht0 : 0 < A_ht := by dsimp [A_ht]; positivity
    have hK_ht0 : 0 < hypersurfaceHeightConstant (n + 3) :=
      zero_lt_one.trans_le (hypersurfaceHeightConstant_one_le _)
    have hch' : ∑ p ∈ bad, Real.log p / p ≤ Real.log A_ht +
        (Real.log (hypersurfaceHeightConstant (n + 3)) + 2 * mertensError + 1) := by
      rw [Real.log_mul hK_ht0.ne' hA_ht0.ne'] at hcharge
      linarith only [hcharge]
    obtain ⟨s, _, hr, hc⟩ := normalized_no_auxiliary_comparison model hmodel_hom hmodel0 hd hdM
      w hw_prim hw_eval hR1 hw_box bad hbad_m hnone hA_ht0 hch'
    have hr' : s + (n + 1 + 1 + (M - d)).choose (M - d) = (n + 1 + 1 + M).choose M := by
      simpa only [hnN] using hr
    obtain ⟨hroot_lo, hroot_hi⟩ := hypersurface_rank_root_bounds (r := n + 1) (by omega) hdM hr'
    simp only [Nat.cast_add, Nat.cast_one] at hroot_lo hroot_hi
    have hX : 0 < (d : ℝ) ^ (1 / (n + 1 : ℝ)) := by positivity
    have halow : (d : ℝ) ^ (1 / (n + 1 : ℝ)) * ((M : ℝ) - d) / ((n + 2 : ℝ) * M) ≤
        ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) * (s : ℝ) ^ (1 / (n + 1 : ℝ)) /
          ((n + 2 : ℝ) * M) :=
      div_le_div_of_nonneg_right (by linarith only [hroot_lo, hX]) (by positivity)
    have haup : ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) * (s : ℝ) ^ (1 / (n + 1 : ℝ)) /
          ((n + 2 : ℝ) * M) ≤
        (d : ℝ) ^ (1 / (n + 1 : ℝ)) * ((M : ℝ) + (n + 1 : ℝ)) / ((n + 2 : ℝ) * M) :=
      div_le_div_of_nonneg_right hroot_hi (by positivity)
    have hk := hypersurface_kernel_ratio_lower (r := n + 1) hd hdM hr'
    simp only [hnN, Nat.cast_add, Nat.cast_one, hnR] at hk
    have hM8R : 8 * (d : ℝ) * ((n + 1 : ℝ) + 1) ≤ M := by
      simpa only [hnR, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
        (mod_cast hM8 : ((8 * d * (n + 2) : ℕ) : ℝ) ≤ M)
    have hbr := auxiliary_large_height_bracket_bound (r := (n + 1 : ℝ))
      (k := ((n + 2 + (M - d)).choose (M - d) : ℝ) / ((M : ℝ) * s)) (by positivity) hd1 hM8R hX
      (by simpa only [hnR] using halow) (by simpa only [hnR] using haup) (by positivity)
      (by simpa only [hnR] using hk) (Real.log_nonneg hR1) (Real.log_nonneg hL1) hT_pos
      (by simpa only [hnR] using hlarge) hposition (by simpa only [hnR] using hc)
    have hn1_pos : (0 : ℝ) < n + 1 := by positivity
    have hn1_1 : (1 : ℝ) ≤ n + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hXle : (d : ℝ) ^ (1 / (n + 1 : ℝ)) ≤ d := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hd1
        ((div_le_one hn1_pos).mpr hn1_1)
    have hlog1 : Real.log A_ht ≤ (Real.log H / (d : ℝ) ^ 2) / (8 * (n + 1 : ℝ)) +
        Real.log (8 * (n + 1 : ℝ)) := by
      have hh := Real.log_le_sub_one_of_pos (show 0 < A_ht / (8 * (n + 1 : ℝ)) by positivity)
      rw [Real.log_div hA_ht0.ne' (by positivity),
        show A_ht / (8 * (n + 1 : ℝ)) = 1 / (8 * (n + 1 : ℝ)) +
          (Real.log H / (d : ℝ) ^ 2) / (8 * (n + 1 : ℝ)) by dsimp [A_ht]; ring] at hh
      have h18 : 1 / (8 * (n + 1 : ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      linarith only [hh, h18]
    have hcancel : (n + 1 : ℝ) * Real.log A_ht -
        Real.log H / (8 * d * (d : ℝ) ^ (1 / (n + 1 : ℝ))) ≤
        (n + 1 : ℝ) * Real.log (8 * (n + 1 : ℝ)) := by
      have hcost' := mul_le_mul_of_nonneg_left hlog1 hn1_pos.le
      have he : (n + 1 : ℝ) * ((Real.log H / (d : ℝ) ^ 2) / (8 * (n + 1 : ℝ))) =
          Real.log H / (8 * (d : ℝ) ^ 2) := by field_simp
      rw [mul_add, he] at hcost'
      have hdiv := div_le_div_of_nonneg_left hHlog
        (by positivity : 0 < 8 * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
        (show 8 * (d : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)) ≤ 8 * (d : ℝ) ^ 2 by
          nlinarith only [hd0, hXle])
      linarith only [hcost', hdiv]
    have hlog_s := hypersurface_rank_log_lower (r := n + 1) hd hM2 hr'
    simp only [Nat.cast_add, Nat.cast_one] at hlog_s
    have hraw : (n + 1 : ℝ) * Real.log M ≤ (4 * (n + 1 : ℝ) - 1) * Real.log d +
        (n + 1 : ℝ) * Real.log (8 * (n + 1 : ℝ)) +
        (hypersurfaceDeterminantError n +
          (n + 1 : ℝ) * (Real.log (hypersurfaceHeightConstant (n + 3)) + 2 * mertensError + 1) +
          (n + 2 : ℝ) * hypersurfaceArchimedeanError (n + 1) /
            ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ))) +
        ((n + 1 : ℝ) * Real.log 2 + Real.log ((n + 1).factorial : ℝ)) + T_pos := by
      linarith only [hbr, hcancel, hlog_s]
    have hdiv := div_le_div_of_nonneg_right hraw hn1_pos.le
    rw [mul_div_cancel_left₀ (Real.log M) hn1_pos.ne'] at hdiv
    have hlogM : Real.log M ≤ err_l + (4 - 1 / (n + 1 : ℝ)) * Real.log d := by
      rw [herr_l]; convert hdiv using 1; field_simp; ring
    have hMle : (M : ℝ) ≤ thr_l := by
      refine Real.natCast_le_of_log_le_log (lt_of_lt_of_le hd hdM) (by dsimp [thr_l]; positivity) ?_
      dsimp only [thr_l]
      rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_rpow hd0]
      exact hlogM
    exact (not_lt_of_ge hMle) hthreshold
  obtain ⟨g, hg⟩ := hexists
  refine ⟨M, ?_, g, hg⟩
  push_cast at hbound
  let D := (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))
  have hdD : (d : ℝ) ≤ D := le_rpow_four_sub_inv hd
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hD1 : 1 ≤ D := hd1.trans hdD
  have hQl : 0 ≤ auxMainTerm n d R_box (primeSetFactor bad) H +
      (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log R_box :=
    add_nonneg (by dsimp [auxMainTerm]; positivity)
      (mul_nonneg (Real.rpow_nonneg hd0.le _) (Real.log_nonneg hR1))
  dsimp only [thr_l] at hbound
  unfold auxDegreeBound
  nlinarith only [hbound, hD1, mul_le_mul_of_nonneg_left hdD (show 0 ≤ 8 * (n + 2 : ℝ) by positivity),
    mul_le_mul_of_nonneg_right hCl hD0, mul_nonneg hK0 hQl]

private lemma hypersurface_projective_auxiliary_exists (n : ℕ) :
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ {d : ℕ} (f : MvPolynomial (Fin (n + 3)) ℤ),
      f.IsHomogeneous d → 0 < d → Irreducible f → ∀ {B : ℝ}, 1 ≤ B →
      ∃ M : ℕ,
        (M : ℝ) ≤ K₀ * auxDegreeBound n d B (hypersurfaceBadPrimeFactor f)
          (integerCoefficientHeight f) ∧
        ∃ g : MvPolynomial (Fin (n + 3)) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
          (∀ x : ProjectivePoint (n + 2), x.mulHeight ≤ B →
            x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) f) →
            x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) g)) ∧ ¬ f ∣ g := by
  classical
  let T_pos : ℝ := (5 * (n + 2 : ℝ) + 5) * (n + 2 : ℝ)
  have hT_pos : 0 ≤ T_pos := by dsimp [T_pos]; positivity
  let E_log : ℝ := (n + 1 : ℝ) * Real.log 2 + Real.log ((n + 1).factorial : ℝ)
  let E_arch : ℝ := (n + 2 : ℝ) * hypersurfaceArchimedeanError (n + 1) /
    ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ))
  let err_s : ℝ := (hypersurfaceDeterminantError n + E_arch + E_log + 4 * (n + 2 : ℝ) ^ 2) /
    (n + 1 : ℝ)
  let err_l : ℝ := Real.log (8 * (n + 1 : ℝ)) +
    ((hypersurfaceDeterminantError n +
        (n + 1 : ℝ) * (Real.log (hypersurfaceHeightConstant (n + 3)) + 2 * mertensError + 1) +
        E_arch) + E_log + T_pos) / (n + 1 : ℝ)
  let K_pos : ℝ := 4 + 8 * (n + 2 : ℝ) + Real.exp err_l +
    Real.exp (T_pos / (n + 1 : ℝ)) * Real.exp err_s
  let K_tr : ℝ := Real.exp ((n + 2 : ℝ) ^ 2 / (n + 1 : ℝ)) + (n + 3 : ℝ)
  have hK_pos_4 : 4 ≤ K_pos := by
    have : 0 < Real.exp err_l := Real.exp_pos _
    have : 0 < Real.exp (T_pos / (n + 1 : ℝ)) * Real.exp err_s :=
      mul_pos (Real.exp_pos _) (Real.exp_pos _)
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    dsimp [K_pos]; linarith
  have hK_tr_1 : 1 ≤ K_tr := by
    have := Real.exp_pos ((n + 2 : ℝ) ^ 2 / (n + 1 : ℝ))
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    dsimp [K_tr]; linarith
  refine ⟨K_pos * K_tr, one_le_mul_of_one_le_of_one_le (by linarith) hK_tr_1,
    fun {d} f hf hd hir {B} hB => ?_⟩
  by_cases habs : AbsolutelyIrreducible f
  · have hf0 : f ≠ 0 := hir.ne_zero
    let S_pts := projectivePoints (projectiveZeroLocus (map (Int.castRingHom ℚ) f)) B
    let e_pts := (Fintype.equivFin S_pts).symm
    let z : Fin (Fintype.card S_pts) → IntPoint (n + 3) := fun i =>
      primitiveProjectiveRep (e_pts i).val
    have hz_prim (i) : Finset.univ.gcd (z i) = 1 := primitiveProjectiveRep_gcd _
    have hz_eval (i) : eval (z i) f = 0 :=
      (mem_integer_projectiveZeroLocus hf _).mp (mem_projectivePoints.mp (e_pts i).property).2
    have hz_box (i j) : |(z i j : ℝ)| ≤ B :=
      (primitiveProjectiveRep_bound _ j).trans (mem_projectivePoints.mp (e_pts i).property).1
    obtain ⟨a, H, ha, hH, hcf, hcg, hpos⟩ := exists_hypersurface_coefficient_position
      (r := n + 1) (by omega) hd f hf hf0
    let model := homogeneousTranslation ℤ a f
    let w := fun i => homogeneousPointTranslation (-a) (z i)
    have hmodel_hom : model.IsHomogeneous d := homogeneousTranslation_homogeneous a hf
    have hmodel0 : model ≠ 0 := (homogeneousTranslation ℤ a).injective.ne (by simpa using hf0)
    have hmodel_ir : AbsolutelyIrreducible model := by
      dsimp only [AbsolutelyIrreducible, model]
      rw [homogeneousTranslation_map]
      exact (MulEquiv.irreducible_iff
        (f := homogeneousTranslation (AlgebraicClosure ℚ) ((Int.castRingHom _) ∘ a))).mpr habs
    have hmodel_deg : model.totalDegree = d := hmodel_hom.totalDegree hmodel0
    have hw_prim (i) : Finset.univ.gcd (w i) = 1 :=
      (homogeneousPointTranslation_gcd (-a) (z i)).trans (hz_prim i)
    have hw_eval (i) : eval (w i) model = 0 := by
      dsimp only [w, model]; rw [homogeneousTranslation_eval]
      change eval (homogeneousPointTranslation a (homogeneousPointTranslation (-a) (z i))) f = 0
      have he := homogeneousPointTranslation_inverse (-a) (z i)
      simp only [neg_neg] at he; rw [he, hz_eval i]
    let R_box := ((d : ℝ) + 1) * B
    have hR1 : 1 ≤ R_box :=
      one_le_mul_of_one_le_of_one_le (by linarith [Nat.cast_nonneg (α := ℝ) d]) hB
    have hw_box (i) : InBox (w i) R_box :=
      homogeneousPointTranslation_box hB a ha (z i) (hz_box i)
    obtain ⟨bad, hbad_m, hcharge⟩ := exists_fin_hypersurface_bad_prime_charge model hmodel_ir
      (hmodel_deg ▸ hd) H hH hcg
    rw [hmodel_deg] at hbad_m hcharge
    have hbad_f (p) : p ∈ bad ↔ stepanovThreshold d < p ∧ HypersurfaceBadReduction f p := by
      rw [hbad_m]; refine and_congr_right fun _ => ?_
      by_cases hp : p.Prime
      · let : Fact p.Prime := ⟨hp⟩
        rw [homogeneous_hypersurfaceBadReduction_iff _ hmodel_hom hmodel0,
          homogeneous_hypersurfaceBadReduction_iff _ hf hf0,
          show model = homogeneousTranslation ℤ a f from rfl, homogeneousTranslation_map]
        exact not_congr (MulEquiv.irreducible_iff
          (f := homogeneousTranslation (AlgebraicClosure (ZMod p)) ((Int.castRingHom _) ∘ a)))
      · exact ⟨fun h => (hp h.1).elim, fun h => (hp h.1).elim⟩
    have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
    have hposition : Real.log H ≤
        Real.log |((MonomialOrder.lex.leadingCoeff model : ℤ) : ℝ)| + T_pos * d * degreeRoot n d := by
      simpa only [T_pos, degreeRoot, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, hnR] using hpos
    have hpos_aux : ∃ M : ℕ, (M : ℝ) ≤ K_pos * auxDegreeBound n d R_box (primeSetFactor bad) H ∧
        ∃ g, IsPointAuxiliary model g M w := by
      by_cases hsmall : Real.log H ≤ 2 * d * (n + 2 : ℝ) * Real.log R_box
      · refine small_height_step model hmodel_hom hmodel0 hd w hw_prim hw_eval hR1 hw_box
          bad hbad_m hH hcg hsmall hposition rfl ?_ hK_pos_4
        have : 0 < Real.exp err_l := Real.exp_pos _
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        dsimp [K_pos]; linarith
      · refine large_height_step model hmodel_hom hmodel0 hd w hw_prim hw_eval hR1 hw_box
          bad hbad_m hH hT_pos hcharge (le_of_not_ge hsmall) hposition rfl ?_ (by linarith)
        have : 0 < Real.exp (T_pos / (n + 1 : ℝ)) * Real.exp err_s :=
          mul_pos (Real.exp_pos _) (Real.exp_pos _)
        dsimp [K_pos]; linarith
    obtain ⟨M, hMbound, g_pos, hg0, hgh, hgw, hgnd⟩ := hpos_aux
    let G := homogeneousTranslation ℤ (-a) g_pos
    have hGhom : G.IsHomogeneous M := homogeneousTranslation_homogeneous (-a) hgh
    have hGnd : ¬ f ∣ G := fun hdvd => hgnd <| by
      have hh := map_dvd (homogeneousTranslation ℤ a).toRingHom hdvd
      change model ∣ homogeneousTranslation ℤ a (homogeneousTranslation ℤ (-a) g_pos) at hh
      rwa [show homogeneousTranslation ℤ a (homogeneousTranslation ℤ (-a) g_pos) = g_pos from
        (homogeneousTranslation ℤ a).apply_symm_apply g_pos] at hh
    refine ⟨M, ?_, G, (homogeneousTranslation ℤ (-a)).injective.ne (by simpa using hg0),
      hGhom, fun x hxB hxf => ?_, hGnd⟩
    · have htr := auxDegreeBound_translate_le (n := n) hd hB (Real.exp_pos _).le
        (mod_cast integerCoefficientHeight_pos f hf0)
        (integerCoefficientHeight_le f (by linarith) hcf) (b := primeSetFactor bad)
      rw [hypersurfaceBadPrimeFactor_eq_exp f habs (hf.totalDegree hf0) bad hbad_f]
      exact hMbound.trans ((mul_le_mul_of_nonneg_left htr (by linarith)).trans_eq (by ring))
    · obtain ⟨i, hi⟩ := e_pts.surjective ⟨x, mem_projectivePoints.mpr ⟨hxB, hxf⟩⟩
      have hh : eval (primitiveProjectiveRep (e_pts i).val) G = 0 := by
        dsimp only [G]; rw [homogeneousTranslation_eval]; exact hgw i
      rw [hi] at hh
      exact (mem_integer_projectiveZeroLocus hGhom x).mpr hh
  · have hQ := rational_map_irreducible_of_integer f hir (by rw [hf.totalDegree hir.ne_zero]; exact hd)
    have hred : ¬ AbsolutelyIrreducibleRat (map (Int.castRingHom ℚ) f) :=
      (absolutelyIrreducibleRat_map_iff f).not.mpr habs
    obtain ⟨g, hg0, hgh, hgnd, hzeros⟩ := nonabsolute_projective_auxiliary f hf hd hQ hred
    refine ⟨d, ?_, g, hg0, hgh, fun x _ hx => hzeros hx, hgnd⟩
    unfold auxDegreeBound auxMainTerm
    rw [hypersurfaceBadPrimeFactor_eq_zero f habs, mul_zero, zero_mul, zero_div, zero_add]
    have hdD : (d : ℝ) ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) := le_rpow_four_sub_inv hd
    have hl : 0 ≤ (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.log_nonneg hB)
    exact (hdD.trans (le_add_of_nonneg_left hl)).trans
      (le_mul_of_one_le_left (by positivity)
        (one_le_mul_of_one_le_of_one_le (by linarith) hK_tr_1))

def hypersurfaceAbsoluteAuxiliaryConstant (n : ℕ) : ℝ :=
  (hypersurface_projective_auxiliary_exists n).choose

lemma hypersurfaceAbsoluteAuxiliaryConstant_one_le (n : ℕ) :
    1 ≤ hypersurfaceAbsoluteAuxiliaryConstant n := by
  unfold hypersurfaceAbsoluteAuxiliaryConstant
  exact (hypersurface_projective_auxiliary_exists n).choose_spec.1

lemma hypersurfaceAbsoluteAuxiliaryConstant_pos (n : ℕ) :
    0 < hypersurfaceAbsoluteAuxiliaryConstant n :=
  zero_lt_one.trans_le (hypersurfaceAbsoluteAuxiliaryConstant_one_le n)

@[expose]
def hypersurfaceAuxiliaryDegreeBound (n d : ℕ) (B b H : ℝ) : ℝ :=
  hypersurfaceAbsoluteAuxiliaryConstant n * auxDegreeBound n d B b H

theorem hypersurface_projective_auxiliary {n d : ℕ} (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hd : 0 < d) (hir : Irreducible f) {B : ℝ} (hB : 1 ≤ B) :
    ∃ M : ℕ,
      (M : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n d B (hypersurfaceBadPrimeFactor f)
        (integerCoefficientHeight f) ∧
      ∃ g : MvPolynomial (Fin (n + 3)) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ x : ProjectivePoint (n + 2), x.mulHeight ≤ B →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) f) →
          x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) g)) ∧ ¬ f ∣ g := by
  unfold hypersurfaceAuxiliaryDegreeBound hypersurfaceAbsoluteAuxiliaryConstant
  exact (hypersurface_projective_auxiliary_exists n).choose_spec.2 f hf hd hir hB

end
end CCDN
