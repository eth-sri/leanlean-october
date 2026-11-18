module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Height.Box
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.AuxiliaryPolynomial.AffineHypersurfaceAuxiliary
import CCDN.AuxiliaryPolynomial.HypersurfaceHeightTransfer
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.Curve.AffineCurveCount
import CCDN.ForMathlib.Log
import CCDN.ForMathlib.MvPolynomial
import CCDN.Height.ScaledHypersurfaceHeight
import CCDN.Hilbert.FilteredPrimeDecomposition
import CCDN.Surface.CompleteIntersectionDegreeBudget
import CCDN.Surface.CurveComponents
import CCDN.Surface.DegreeOneCount
import CCDN.Surface.PrimitiveSurfaceFixedDegree
import CCDN.Surface.TopFormBadPrimes

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma sum_curveBound_le_surface_degree_budget {ι : Type*}
    (s : Finset ι) (δ : ι → ℕ) {d : ℕ} (hd : 16 ≤ d)
    {B K₀ : ℝ} (hK₀ : 0 ≤ K₀) (hB : 1 ≤ B) (hδ : ∀ i ∈ s, 2 ≤ δ i)
    (hD : (∑ i ∈ s, (δ i : ℝ)) ≤ K₀ * (d : ℝ) ^ (9 / 2 : ℝ) * B ^ (1 / Real.sqrt d)) :
    ∑ i ∈ s, curveBound (δ i) B ≤ Real.exp 1 * (480 * K₀ + 2 * K₀ ^ 4) * (d : ℝ) ^ 18 * B := by
  have hB0 : 0 < B := by linarith
  have hlogB := Real.log_nonneg hB
  let U := (96 * Real.exp 1) * B ^ (1 / 2 : ℝ) * (Real.log B + 1)
  have hU0 : 0 ≤ U := by dsimp [U]; positivity
  have hpoint (i) (hi : i ∈ s) : curveBound (δ i) B ≤
      (δ i : ℝ) * U + (2 * Real.exp 1) * (δ i : ℝ) ^ 4 := by
    have hδ2 : (2 : ℝ) ≤ δ i := mod_cast hδ i hi
    have hδ0 : (0 : ℝ) < δ i := by linarith
    by_cases hsmall : (δ i : ℝ) ≤ Real.log B
    · have hpoly : (δ i : ℝ) ^ 3 ≤ 48 * Real.exp ((δ i : ℝ) / 2) := by
        have hh := Real.pow_div_factorial_le_exp ((δ i : ℝ) / 2) (by positivity) 3
        norm_num at hh; nlinarith
      have hexp : (δ i : ℝ) / 2 + Real.log B / δ i ≤ 1 + Real.log B / 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hsmall) (sub_nonneg.mpr hδ2),
          div_mul_cancel₀ (Real.log B) hδ0.ne']
      have hrw : (δ i : ℝ) ^ 3 * B ^ (1 / (δ i : ℝ)) ≤ (48 * Real.exp 1) * B ^ (1 / 2 : ℝ) := calc
        (δ i : ℝ) ^ 3 * B ^ (1 / (δ i : ℝ))
            ≤ (48 * Real.exp ((δ i : ℝ) / 2)) * B ^ (1 / (δ i : ℝ)) :=
              mul_le_mul_of_nonneg_right hpoly (by positivity)
        _ = 48 * Real.exp ((δ i : ℝ) / 2 + Real.log B / δ i) := by
            rw [Real.rpow_def_of_pos hB0, Real.exp_add, mul_assoc]; congr 2; congr 1; ring
        _ ≤ 48 * Real.exp (1 + Real.log B / 2) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)
        _ = (48 * Real.exp 1) * B ^ (1 / 2 : ℝ) := by
            rw [Real.exp_add, Real.rpow_def_of_pos hB0, mul_assoc]; congr 2; congr 1; ring
      have hc : curveBound (δ i) B ≤ U := by
        have hh := mul_le_mul hrw (show Real.log B + δ i ≤ 2 * (Real.log B + 1) by linarith)
          (by positivity) (by positivity)
        unfold curveBound; dsimp [U]; convert hh using 1; ring
      have hd1 : (1 : ℝ) ≤ δ i := by linarith
      exact (hc.trans (by simpa using mul_le_mul_of_nonneg_right hd1 hU0)).trans
        (le_add_of_nonneg_right (by positivity))
    · have hpow : B ^ (1 / (δ i : ℝ)) ≤ Real.exp 1 := by
        rw [Real.rpow_def_of_pos hB0]
        apply Real.exp_le_exp.mpr
        simpa only [mul_one_div] using (div_le_one hδ0).mpr (le_of_not_ge hsmall)
      have hh := mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (δ i : ℝ) ^ 3))
        (show Real.log B + δ i ≤ 2 * δ i by linarith) (by positivity) (by positivity)
      have hc : curveBound (δ i) B ≤ (2 * Real.exp 1) * (δ i : ℝ) ^ 4 := by
        unfold curveBound; convert hh using 1; ring
      exact hc.trans (le_add_of_nonneg_left (by positivity))
  let S_sum := ∑ i ∈ s, (δ i : ℝ)
  have hS0 : 0 ≤ S_sum := Finset.sum_nonneg fun _ _ => by positivity
  have h4 : ∑ i ∈ s, (δ i : ℝ) ^ 4 ≤ S_sum ^ 4 := calc
    ∑ i ∈ s, (δ i : ℝ) ^ 4 = ∑ i ∈ s, (δ i : ℝ) * (δ i : ℝ) ^ 3 :=
      Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ ∑ i ∈ s, (δ i : ℝ) * S_sum ^ 3 := Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
        (Finset.single_le_sum (fun _ _ => Nat.cast_nonneg _) hi) 3) (by positivity)
    _ = S_sum ^ 4 := by rw [← Finset.sum_mul]; ring
  have hqtr : 1 / Real.sqrt (d : ℝ) ≤ (1 / 4 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (Real.le_sqrt_of_sq_le (mod_cast hd))
  have hd1 : (1 : ℝ) ≤ d := mod_cast (by omega : 1 ≤ d)
  have hd0 : (0 : ℝ) < d := by linarith
  have hsmall_wt : B ^ (1 / Real.sqrt (d : ℝ)) * (B ^ (1 / 2 : ℝ) * (Real.log B + 1)) ≤ 5 * B := by
    have hlog5 : B ^ (1 / 2 : ℝ) * (Real.log B + 1) ≤ 5 * B ^ (3 / 4 : ℝ) := by
      have hh := Real.rpow_half_mul_log_add_le (ε := (1 / 4 : ℝ)) (D := 1) hB (by norm_num) (by norm_num)
      norm_num at hh ⊢; exact hh
    calc B ^ (1 / Real.sqrt (d : ℝ)) * (B ^ (1 / 2 : ℝ) * (Real.log B + 1))
        ≤ B ^ (1 / Real.sqrt (d : ℝ)) * (5 * B ^ (3 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog5 (by positivity)
      _ = 5 * B ^ (1 / Real.sqrt (d : ℝ) + (3 / 4 : ℝ)) := by rw [Real.rpow_add hB0]; ring
      _ ≤ 5 * B := by
          simpa only [Real.rpow_one] using mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hB
              (show 1 / Real.sqrt (d : ℝ) + (3 / 4 : ℝ) ≤ 1 by linarith)) (by norm_num : (0 : ℝ) ≤ 5)
  have hdp : (d : ℝ) ^ (9 / 2 : ℝ) ≤ (d : ℝ) ^ 18 := by
    simpa only [Real.rpow_ofNat] using
      Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num : (9 / 2 : ℝ) ≤ 18)
  have hpart1 : S_sum * U ≤ (480 * Real.exp 1) * K₀ * (d : ℝ) ^ 18 * B := calc
    S_sum * U ≤ (K₀ * (d : ℝ) ^ (9 / 2 : ℝ) * B ^ (1 / Real.sqrt d)) * U :=
      mul_le_mul_of_nonneg_right hD hU0
    _ = (96 * Real.exp 1) * K₀ * (d : ℝ) ^ (9 / 2 : ℝ) *
          (B ^ (1 / Real.sqrt d) * (B ^ (1 / 2 : ℝ) * (Real.log B + 1))) := by dsimp [U]; ring
    _ ≤ (96 * Real.exp 1) * K₀ * (d : ℝ) ^ (9 / 2 : ℝ) * (5 * B) :=
        mul_le_mul_of_nonneg_left hsmall_wt (by positivity)
    _ = (480 * Real.exp 1) * K₀ * (d : ℝ) ^ (9 / 2 : ℝ) * B := by ring
    _ ≤ (480 * Real.exp 1) * K₀ * (d : ℝ) ^ 18 * B := by gcongr
  have hpart2 : S_sum ^ 4 ≤ K₀ ^ 4 * (d : ℝ) ^ 18 * B := by
    have hpow := pow_le_pow_left₀ hS0 hD 4
    rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hd0.le (9 / 2 : ℝ) 4,
      ← Real.rpow_mul_natCast hB0.le (1 / Real.sqrt d) 4] at hpow
    norm_num only [show (9 / 2 : ℝ) * (4 : ℕ) = 18 by norm_num, Real.rpow_ofNat] at hpow
    have hbox : B ^ ((1 / Real.sqrt (d : ℝ)) * (4 : ℕ)) ≤ B := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB
        (show (1 / Real.sqrt (d : ℝ)) * (4 : ℕ) ≤ 1 by norm_num only [Nat.cast_ofNat]; linarith)
    exact hpow.trans (mul_le_mul_of_nonneg_left hbox (by positivity))
  calc ∑ i ∈ s, curveBound (δ i) B
      ≤ ∑ i ∈ s, ((δ i : ℝ) * U + (2 * Real.exp 1) * (δ i : ℝ) ^ 4) := Finset.sum_le_sum hpoint
    _ = S_sum * U + (2 * Real.exp 1) * ∑ i ∈ s, (δ i : ℝ) ^ 4 := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    _ ≤ (480 * Real.exp 1) * K₀ * (d : ℝ) ^ 18 * B +
          (2 * Real.exp 1) * (K₀ ^ 4 * (d : ℝ) ^ 18 * B) :=
        add_le_add hpart1 (mul_le_mul_of_nonneg_left (h4.trans hpart2) (by positivity))
    _ = Real.exp 1 * (480 * K₀ + 2 * K₀ ^ 4) * (d : ℝ) ^ 18 * B := by ring

private theorem surface_top_form_auxiliary_rational
    (f : MvPolynomial (Fin 3) ℤ) (hir : HasAbsIrreducibleTopForm f) {B : ℝ} (hB : 1 ≤ B) :
    ∃ g : MvPolynomial (Fin 3) ℤ, g ≠ 0 ∧
      ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g ∧
      (g.totalDegree : ℝ) ≤
        (affineHypersurfaceAuxiliaryConstant 1 *
          (2 * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant 3 + 2)) *
          (f.totalDegree : ℝ) ^ (7 / 2 : ℝ) * B ^ (1 / Real.sqrt f.totalDegree) ∧
      ∀ x : IntPoint 3, InBox x B → eval x f = 0 → eval x g = 0 := by
  have hf0 : f ≠ 0 := fun hz => hir.ne_zero (by simp [hz])
  obtain ⟨c, u, hc, huprim, he⟩ := exists_primitive_integer_factor f hf0
  obtain ⟨huDeg, huTop⟩ := absolute_top_irreducible_of_integer_scalar_factor hc he hir
  have huIr := huprim.irreducible_of_absolute_top huTop
  have habs := absolute_irreducible_of_top_homogeneousComponent_irreducible u huTop
  have hd : 0 < u.totalDegree := absolute_integer_polynomial_totalDegree_pos u habs
  let d := u.totalDegree
  let F := homogeneousComponent d u
  have hF0 : F ≠ 0 := homogeneousComponent_totalDegree_ne_zero huIr.ne_zero
  have hFd : F.totalDegree = d := (homogeneousComponent_isHomogeneous d u).totalDegree hF0
  let L := (integerCoefficientHeight F : ℝ)
  have hL : 1 ≤ L := leading_height_one_le u huIr.ne_zero
  let q := 1 / ((2 : ℝ) * d * (d : ℝ) ^ (1 / 2 : ℝ))
  let K₀ := Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant 3
  have hK0 : 0 ≤ K₀ := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans (hypersurfaceHeightConstant_one_le 3))
  have hbF : hypersurfaceBadPrimeFactor F ≤ K₀ * (1 + Real.log L / (d : ℝ) ^ 2) := by
    simpa only [hFd] using hypersurfaceBadPrimeFactor_le_height F L hL
      (coefficient_abs_le_integerCoefficientHeight F)
  have htr : (Real.log L + (d : ℝ) ^ 2) / L ^ q ≤ 2 * (d : ℝ) ^ 2 := by
    simpa only [q, Nat.cast_ofNat, Real.log_one, zero_add, Real.one_rpow, div_one] using
      hypersurface_logarithmic_height_transfer (r := 2) (by omega) hd (Y := 1) le_rfl hL
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hratio : hypersurfaceBadPrimeFactor u / L ^ q ≤ 2 * K₀ := calc
    hypersurfaceBadPrimeFactor u / L ^ q ≤ hypersurfaceBadPrimeFactor F / L ^ q :=
      div_le_div_of_nonneg_right (hypersurfaceBadPrimeFactor_le_top_homogeneousComponent u huTop)
        (by positivity)
    _ ≤ (K₀ / (d : ℝ) ^ 2) * ((Real.log L + (d : ℝ) ^ 2) / L ^ q) := by
      have hh := div_le_div_of_nonneg_right hbF (by positivity : 0 ≤ L ^ q)
      convert hh using 1; field_simp; ring
    _ ≤ (K₀ / (d : ℝ) ^ 2) * (2 * (d : ℝ) ^ 2) := mul_le_mul_of_nonneg_left htr (by positivity)
    _ = 2 * K₀ := by field_simp
  obtain ⟨g, ⟨hg0, hgnd, hgz⟩, hgdeg⟩ := affine_hypersurface_auxiliary u huprim huIr hd hB
  let Q := B ^ (1 / (d : ℝ) ^ (1 / 2 : ℝ))
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hB (by positivity)
  have hlogB : Real.log B ≤ (d : ℝ) ^ (1 / 2 : ℝ) * Q := by
    have hh := Real.log_le_rpow_div (by linarith : 0 ≤ B)
      (by positivity : 0 < 1 / (d : ℝ) ^ (1 / 2 : ℝ))
    simpa only [Q, one_div, div_inv_eq_mul, mul_comm] using hh
  have hd_half : (d : ℝ) ^ (1 / 2 : ℝ) * (d : ℝ) ^ (1 / 2 : ℝ) = d := by
    rw [← Real.rpow_add hd0]; norm_num
  have hdD : (d : ℝ) ≤ (d : ℝ) ^ (7 / 2 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num : (1 : ℝ) ≤ 7 / 2)
  have hlow : (d : ℝ) ^ (1 / 2 : ℝ) * Real.log B + (d : ℝ) ^ (7 / 2 : ℝ) ≤
      2 * (d : ℝ) ^ (7 / 2 : ℝ) * Q := by
    have h1 : (d : ℝ) ^ (1 / 2 : ℝ) * Real.log B ≤ (d : ℝ) ^ (7 / 2 : ℝ) * Q := calc
      (d : ℝ) ^ (1 / 2 : ℝ) * Real.log B ≤ (d : ℝ) ^ (1 / 2 : ℝ) * ((d : ℝ) ^ (1 / 2 : ℝ) * Q) :=
        mul_le_mul_of_nonneg_left hlogB (by positivity)
      _ = d * Q := by rw [← mul_assoc, hd_half]
      _ ≤ (d : ℝ) ^ (7 / 2 : ℝ) * Q := mul_le_mul_of_nonneg_right hdD (by positivity)
    have h2 : (d : ℝ) ^ (7 / 2 : ℝ) ≤ (d : ℝ) ^ (7 / 2 : ℝ) * Q :=
      le_mul_of_one_le_right (by positivity) hQ1
    linarith
  have hp72 : (d : ℝ) ^ (3 / 2 : ℝ) * (d : ℝ) ^ 2 = (d : ℝ) ^ (7 / 2 : ℝ) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_add hd0]; norm_num
  have hmain : (d : ℝ) ^ (3 / 2 : ℝ) *
      min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * hypersurfaceBadPrimeFactor u) *
      Q / L ^ q ≤ (2 * K₀) * (d : ℝ) ^ (7 / 2 : ℝ) * Q := calc
    _ ≤ (d : ℝ) ^ (3 / 2 : ℝ) * ((d : ℝ) ^ 2 * hypersurfaceBadPrimeFactor u) * Q / L ^ q := by
        gcongr; exact min_le_right _ _
    _ = ((d : ℝ) ^ (3 / 2 : ℝ) * (d : ℝ) ^ 2) * Q * (hypersurfaceBadPrimeFactor u / L ^ q) := by ring
    _ ≤ ((d : ℝ) ^ (3 / 2 : ℝ) * (d : ℝ) ^ 2) * Q * (2 * K₀) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = (2 * K₀) * (d : ℝ) ^ (7 / 2 : ℝ) * Q := by rw [hp72]; ring
  have hexpr : affineAuxiliaryDegreeExpression 1 d B L (hypersurfaceBadPrimeFactor u) ≤
      (2 * K₀ + 2) * (d : ℝ) ^ (7 / 2 : ℝ) * B ^ (1 / Real.sqrt d) := by
    rw [Real.sqrt_eq_rpow]
    unfold affineAuxiliaryDegreeExpression
    norm_num only [Nat.cast_one, show (1 : ℝ) + 1 = 2 by norm_num,
      show (2 : ℝ) - 1 / 2 = 3 / 2 by norm_num, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
      show (4 : ℝ) - 1 / 2 = 7 / 2 by norm_num]
    dsimp only [Q, q] at hmain hlow
    nlinarith only [hmain, hlow]
  have hudvd : u ∣ f := ⟨C c, by rw [he]; ring⟩
  refine ⟨g, hg0, fun h => hgnd (huprim.rational_map_dvd_iff.mp
    ((map_dvd (map (Int.castRingHom ℚ)) hudvd).trans h)), ?_, fun x hx hxf => hgz x hx ?_⟩
  · have hh := hgdeg.trans (mul_le_mul_of_nonneg_left hexpr (affineHypersurfaceAuxiliaryConstant_pos 1).le)
    rw [← huDeg]
    dsimp only [K₀, d] at hh
    convert hh using 1; ring
  · rw [he, eval_mul, eval_C] at hxf
    exact (mul_eq_zero.mp hxf).resolve_left hc

private theorem affine_surface_count_large_degree :
    ∃ K_big : ℝ, 0 < K_big ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      16 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        K_big * (f.totalDegree : ℝ) ^ 18 * B := by
  classical
  obtain ⟨K_cv, hK_cv, hcv⟩ := affine_curve_count 3 (by omega)
  obtain ⟨K_ln, hK_ln, hlines⟩ := surface_degree_one_component_contribution
  let K_aux := affineHypersurfaceAuxiliaryConstant 1 *
    (2 * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant 3 + 2)
  have hK_aux : 0 < K_aux := by
    have := affineHypersurfaceAuxiliaryConstant_pos 1
    have := zero_le_one.trans (hypersurfaceHeightConstant_one_le 3)
    dsimp [K_aux]; positivity
  let A_nl := K_cv * Real.exp 1 * (480 * K_aux + 2 * K_aux ^ 4)
  refine ⟨A_nl + K_ln + K_aux, by dsimp [A_nl]; positivity, fun f hir hd B hB => ?_⟩
  have habs := absolute_irreducible_of_top_homogeneousComponent_irreducible f hir
  have hfQ : Irreducible (map (Int.castRingHom ℚ) f) := rational_irreducible_of_charZero_map f habs
  have hd0 : (0 : ℝ) < f.totalDegree := mod_cast (by omega : 0 < f.totalDegree)
  have hd1 : (1 : ℝ) ≤ f.totalDegree := mod_cast (by omega : 1 ≤ f.totalDegree)
  obtain ⟨g, _, hgnd, hgdeg, hgz⟩ := surface_top_form_auxiliary_rational f hir hB
  obtain ⟨S, δ, hcomp, hsec_eq, hbudget, _⟩ := exists_completeIntersection_curve_components
    (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) g) hfQ hgnd
  rw [totalDegree_map_of_injective Int.cast_injective f,
    totalDegree_map_of_injective Int.cast_injective g] at hbudget
  have hsum_S : ((∑ P ∈ S, δ P : ℕ) : ℝ) ≤
      K_aux * (f.totalDegree : ℝ) ^ (9 / 2 : ℝ) * B ^ (1 / Real.sqrt f.totalDegree) := by
    have hbR : ((∑ P ∈ S, δ P : ℕ) : ℝ) ≤ (f.totalDegree : ℝ) * g.totalDegree := mod_cast hbudget
    have hp92 : (f.totalDegree : ℝ) * (f.totalDegree : ℝ) ^ (7 / 2 : ℝ) =
        (f.totalDegree : ℝ) ^ (9 / 2 : ℝ) := calc
      (f.totalDegree : ℝ) * (f.totalDegree : ℝ) ^ (7 / 2 : ℝ)
          = (f.totalDegree : ℝ) ^ (1 : ℝ) * (f.totalDegree : ℝ) ^ (7 / 2 : ℝ) := by rw [Real.rpow_one]
      _ = (f.totalDegree : ℝ) ^ (9 / 2 : ℝ) := by rw [← Real.rpow_add hd0]; norm_num
    refine hbR.trans ((mul_le_mul_of_nonneg_left hgdeg hd0.le).trans_eq ?_)
    dsimp only [K_aux]; rw [show (f.totalDegree : ℝ) * (K_aux * (f.totalDegree : ℝ) ^ (7 / 2 : ℝ) *
      B ^ (1 / Real.sqrt f.totalDegree)) =
      K_aux * ((f.totalDegree : ℝ) * (f.totalDegree : ℝ) ^ (7 / 2 : ℝ)) *
      B ^ (1 / Real.sqrt f.totalDegree) by ring, hp92]
  let T₂ := S.filter fun P => 2 ≤ δ P
  let T₁ := S.filter fun P => δ P = 1
  let L₁ := ⋃ P ∈ T₁, idealZeroLocus P
  have hsum_T2 : (∑ P ∈ T₂, (δ P : ℝ)) ≤
      K_aux * (f.totalDegree : ℝ) ^ (9 / 2 : ℝ) * B ^ (1 / Real.sqrt f.totalDegree) := by
    have hsub : ∑ P ∈ T₂, δ P ≤ ∑ P ∈ S, δ P :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; omega)
    have hcast : ((∑ P ∈ T₂, δ P : ℕ) : ℝ) ≤ ((∑ P ∈ S, δ P : ℕ) : ℝ) := mod_cast hsub
    rw [Nat.cast_sum] at hcast
    exact hcast.trans hsum_S
  have hnl_cnt : (count (⋃ P ∈ T₂, idealZeroLocus P) B : ℝ) ≤ A_nl * (f.totalDegree : ℝ) ^ 18 * B := calc
    (count (⋃ P ∈ T₂, idealZeroLocus P) B : ℝ) ≤ ∑ P ∈ T₂, (count (idealZeroLocus P) B : ℝ) :=
      mod_cast count_biUnion_finset_le T₂ idealZeroLocus B
    _ ≤ ∑ P ∈ T₂, K_cv * curveBound (δ P) B := Finset.sum_le_sum fun P hP => by
      obtain ⟨hPS, hδ⟩ := Finset.mem_filter.mp hP
      exact hcv P (hcomp P hPS).isPrime (δ P) (by omega) (hcomp P hPS).degree B hB
    _ = K_cv * ∑ P ∈ T₂, curveBound (δ P) B := (Finset.mul_sum _ _ _).symm
    _ ≤ K_cv * (Real.exp 1 * (480 * K_aux + 2 * K_aux ^ 4) * (f.totalDegree : ℝ) ^ 18 * B) :=
      mul_le_mul_of_nonneg_left (sum_curveBound_le_surface_degree_budget T₂ δ hd hK_aux.le hB
        (fun _ hP => (Finset.mem_filter.mp hP).2) hsum_T2) hK_cv.le
    _ = A_nl * (f.totalDegree : ℝ) ^ 18 * B := by dsimp [A_nl]; ring
  have hout : count (zeroLocus (map (Int.castRingHom ℚ) f) \ L₁) B ≤
      count (⋃ P ∈ T₂, idealZeroLocus P) B :=
    Finset.card_le_card fun x hx => by
      obtain ⟨hbox, hxf, hxL⟩ := mem_integralPoints.mp hx
      have hzero : eval x f = 0 := Int.cast_injective (α := ℚ)
        (by change (Int.castRingHom ℚ) (eval x f) = (Int.castRingHom ℚ) 0; rwa [map_eval, map_zero])
      have hgz0 : eval (rationalPoint x) (map (Int.castRingHom ℚ) g) = 0 := by
        have hh := congrArg (Int.castRingHom ℚ) (hgz x hbox hzero)
        rwa [map_eval, map_zero] at hh
      have hxsec : rationalPoint x ∈
          zeroLocus (map (Int.castRingHom ℚ) f) ∩ zeroLocus (map (Int.castRingHom ℚ) g) :=
        ⟨hxf, hgz0⟩
      rw [hsec_eq] at hxsec
      obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hxsec
      obtain ⟨hPS, hxP⟩ := Set.mem_iUnion.mp hxP
      have hpos := (hcomp P hPS).pos
      have hne1 : δ P ≠ 1 := fun h1 => hxL (Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨hPS, h1⟩, hxP⟩⟩)
      exact mem_integralPoints.mpr ⟨hbox, Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨hPS, by omega⟩, hxP⟩⟩⟩
  have hln_cnt : (count L₁ B : ℝ) ≤ K_ln * (f.totalDegree : ℝ) ^ 6 * B + T₁.card :=
    hlines f hir (by omega) B (by linarith) T₁
      (fun P hP => by
        obtain ⟨hPS, h1⟩ := Finset.mem_filter.mp hP
        exact ⟨(hcomp P hPS).isPrime, (hcomp P hPS).height_eq, h1 ▸ (hcomp P hPS).degree⟩)
      (fun P hP => (hcomp P (Finset.mem_filter.mp hP).1).mem)
  have hT1_card : T₁.card ≤ ∑ P ∈ S, δ P := calc
    T₁.card ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = ∑ _P ∈ S, 1 := by simp
    _ ≤ ∑ P ∈ S, δ P := Finset.sum_le_sum fun P hP => (hcomp P hP).pos
  have hBpow : B ^ (1 / Real.sqrt f.totalDegree) ≤ B := by
    have hrt1 : (1 : ℝ) ≤ Real.sqrt f.totalDegree := by simpa using Real.sqrt_le_sqrt hd1
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hB ((div_le_one (by positivity)).mpr hrt1)
  have hdpow : (f.totalDegree : ℝ) ^ (9 / 2 : ℝ) ≤ (f.totalDegree : ℝ) ^ 18 := by
    simpa only [Real.rpow_ofNat] using
      Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num : (9 / 2 : ℝ) ≤ 18)
  have hd6 : (f.totalDegree : ℝ) ^ 6 ≤ (f.totalDegree : ℝ) ^ 18 :=
    pow_le_pow_right₀ hd1 (by omega)
  have hcard_le : (T₁.card : ℝ) ≤ K_aux * (f.totalDegree : ℝ) ^ 18 * B :=
    ((Nat.cast_le.mpr hT1_card).trans hsum_S).trans (by gcongr)
  have htot : count (zeroLocus (map (Int.castRingHom ℚ) f)) B ≤
      count (zeroLocus (map (Int.castRingHom ℚ) f) \ L₁) B + count L₁ B :=
    (count_mono (fun x hx => if hxL : x ∈ L₁ then Or.inr hxL else Or.inl ⟨hx, hxL⟩) le_rfl).trans
      (count_union_le _ _ B)
  have houtR : (count (zeroLocus (map (Int.castRingHom ℚ) f) \ L₁) B : ℝ) ≤
      A_nl * (f.totalDegree : ℝ) ^ 18 * B := (Nat.cast_le.mpr hout).trans hnl_cnt
  have hlnR : (count L₁ B : ℝ) ≤ (K_ln + K_aux) * (f.totalDegree : ℝ) ^ 18 * B :=
    (hln_cnt.trans (add_le_add
      (show K_ln * (f.totalDegree : ℝ) ^ 6 * B ≤ K_ln * (f.totalDegree : ℝ) ^ 18 * B by gcongr)
      hcard_le)).trans_eq (by ring)
  have htotR : (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
      (count (zeroLocus (map (Int.castRingHom ℚ) f) \ L₁) B : ℝ) + count L₁ B := mod_cast htot
  exact (htotR.trans (add_le_add houtR hlnR)).trans_eq (by ring)

private theorem top_form_surface_bounded_degree_linear_bound (t : ℕ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      5 ≤ f.totalDegree → f.totalDegree < t → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤ K₀ * B := by
  induction t with
  | zero => exact ⟨1, one_pos, fun _ _ _ ht => absurd ht (Nat.not_lt_zero _)⟩
  | succ t ih =>
    obtain ⟨K₀, hK₀, hbound⟩ := ih
    by_cases ht : 5 ≤ t
    · obtain ⟨K₁, hK₁, hb'⟩ := primitive_surface_fixed_degree_linear_bound t ht
      refine ⟨K₀ + K₁, by positivity, fun f hir hd hlt B hB => ?_⟩
      have hB0 : 0 ≤ B := by linarith
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq
      · exact (hbound f hir hd hlt B hB).trans (by gcongr; linarith)
      · have hf0 : f ≠ 0 := fun hz => hir.ne_zero (by simp [hz])
        obtain ⟨c, u, hc, hprim, he⟩ := exists_primitive_integer_factor f hf0
        obtain ⟨hudeg, hutop⟩ := absolute_top_irreducible_of_integer_scalar_factor hc he hir
        have hzero : zeroLocus (map (Int.castRingHom ℚ) f) =
            zeroLocus (map (Int.castRingHom ℚ) u) := Set.ext fun x => by
          change eval x (map (Int.castRingHom ℚ) f) = 0 ↔ eval x (map (Int.castRingHom ℚ) u) = 0
          rw [he, map_mul, map_C, eval_mul, eval_C]
          exact mul_eq_zero_iff_left (show (c : ℚ) ≠ 0 from mod_cast hc)
        rw [hzero]
        exact (hb' u hprim hutop (hudeg.trans heq) B hB).trans (by gcongr; linarith)
    · exact ⟨K₀, hK₀, fun f hir hd hlt => hbound f hir hd (by omega)⟩

theorem affine_surface_dimension_growth :
    ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        K₀ * (f.totalDegree : ℝ) ^ 18 * B := by
  obtain ⟨K_big, hK_big, hbig⟩ := affine_surface_count_large_degree
  obtain ⟨K_sm, hK_sm, hsmall⟩ := top_form_surface_bounded_degree_linear_bound 16
  refine ⟨K_big + K_sm, by positivity, fun f hir hd B hB => ?_⟩
  have hB0 : 0 ≤ B := by linarith
  have hdpow : 1 ≤ (f.totalDegree : ℝ) ^ 18 :=
    one_le_pow₀ (mod_cast (by omega : 1 ≤ f.totalDegree))
  by_cases hlarge : 16 ≤ f.totalDegree
  · exact (hbig f hir hlarge B hB).trans (by gcongr; linarith)
  · calc (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ)
        ≤ K_sm * B := hsmall f hir hd (by omega) B hB
      _ ≤ (K_big + K_sm) * 1 * B := by gcongr; linarith
      _ ≤ (K_big + K_sm) * (f.totalDegree : ℝ) ^ 18 * B := by gcongr

end
end CCDN
