module

public import CCDN.Algebra.ScaledHomogenization
public import CCDN.AuxiliaryPolynomial.HypersurfaceAuxiliaryTheorem
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
public import CCDN.AuxiliaryPolynomial.ScalingPrime
import CCDN.Algebra.AffineTranslation
import CCDN.Algebra.HomogeneousSlice
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.Algebra.ScaledHomogenizationPrimitive
import CCDN.Algebra.ScaledHypersurfaceModel
import CCDN.AuxiliaryPolynomial.AffineLeadingTranslation
import CCDN.AuxiliaryPolynomial.AffineTranslationCount
import CCDN.AuxiliaryPolynomial.HypersurfaceHeightTransfer
import CCDN.AuxiliaryPolynomial.HypersurfacePositionHeight
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceAuxiliary
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceBadPrimes
import CCDN.ForMathlib.Log
import CCDN.ForMathlib.MvPolynomial
import CCDN.Height.ProjectiveIntegerHeight
import CCDN.Height.ScaledHypersurfaceHeight
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

public section
namespace CCDN
noncomputable section
open MvPolynomial

@[expose]
def affineAuxiliaryDegreeExpression (n d : ℕ) (B L b : ℝ) : ℝ :=
  (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) *
      min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) *
      B ^ (1 / (d : ℝ) ^ (1 / (n + 1 : ℝ))) /
        L ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) +
    (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
      (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))

private lemma scaled_affine_auxiliary {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hir : Irreducible f) (hd : 0 < f.totalDegree)
    {h : ℤ} (hh1 : 1 ≤ h) (hFprim : PrimitiveIntegerPolynomial (scaledHomogenize f.totalDegree h f))
    {B : ℝ} (hB : 1 ≤ B) (hhB : (h : ℝ) ≤ B) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n f.totalDegree B
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree h f))
        (integerCoefficientHeight (scaledHomogenize f.totalDegree h f) : ℝ) := by
  let d := f.totalDegree
  let F := scaledHomogenize d h f
  have hh0 : h ≠ 0 := by omega
  have hhQ : (h : ℚ) ≠ 0 := mod_cast hh0
  have hFhom : F.IsHomogeneous d := scaledHomogenize_homogeneous h f le_rfl
  have hFir : Irreducible F := by
    apply hFprim.irreducible_of_rational_map
    rw [scaledHomogenize_map]
    have hdeg : (map (Int.castRingHom ℚ) f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective Int.cast_injective f
    rw [← hdeg]
    exact scaledHomogenize_irreducible _ (rational_map_irreducible_of_integer f hir hd)
      (by simpa using hhQ)
  obtain ⟨M, hM, G, _, hGhom, hGzero, hGnd⟩ := hypersurface_projective_auxiliary F hFhom hd hFir hB
  let g := homogeneousSlice (n + 2) h G
  have hdegF : (homogeneousSlice (n + 2) h F).totalDegree = d := by
    rw [homogeneousSlice_scaledHomogenize h f le_rfl,
      totalDegree_mul_of_isDomain (C_eq_zero.not.mpr (pow_ne_zero d hh0)) hir.ne_zero,
      totalDegree_C, zero_add]
  have hndQ := rational_homogeneousSlice_not_dvd hh0 hFhom
    (scaledHomogenize_ne_zero d hh0 hir.ne_zero) hGhom hFprim hdegF hGnd
  have hgnd : ¬ f ∣ g := fun hdvd => hndQ <| by
    rw [homogeneousSlice_scaledHomogenize h f le_rfl, map_mul, map_C]
    simpa only [Int.coe_castRingHom, Int.cast_pow] using
      ((isUnit_iff_ne_zero.mpr (pow_ne_zero d hhQ)).map C).mul_left_dvd.mpr
        (map_dvd (map (Int.castRingHom ℚ)) hdvd)
  refine ⟨g, ⟨fun hz => hgnd (hz ▸ dvd_zero _), hgnd, fun x hx hxf => ?_⟩,
    (Nat.cast_le.mpr (homogeneousSlice_degree_le h hGhom)).trans hM⟩
  let v : IntPoint (n + 3) := Fin.cons h x
  have hv0 : v ≠ 0 := fun hz => hh0 (congrFun hz 0)
  let P := Projectivization.mk ℚ (rationalPoint v) (rationalPoint_ne_zero hv0)
  have hPB : P.mulHeight ≤ B := projective_integer_height_le v hv0 <| Fin.cases
    (by simpa [v, abs_of_nonneg (show (0 : ℝ) ≤ h by exact_mod_cast (by omega : 0 ≤ h))] using hhB)
    hx
  have hvF := congrArg (Int.castRingHom ℚ)
    (show eval v F = 0 by rw [scaledHomogenize_eval h f le_rfl, hxf, mul_zero])
  rw [map_eval, map_zero] at hvF
  have hPG := (mem_projectiveZeroLocus_mk (hGhom.map _) _ _).mp
    (hGzero P hPB ((mem_projectiveZeroLocus_mk (hFhom.map _) _ _).mpr hvF))
  rw [homogeneousSlice_eval]
  apply Int.cast_injective (α := ℚ)
  change (Int.castRingHom ℚ) (eval v G) = (Int.castRingHom ℚ) 0
  rwa [map_eval, map_zero]

private lemma hypersurfaceBadPrimeFactor_scaledHomogenize_le {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f ≠ 0) {p : ℕ} (hp : p.Prime) :
    hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree (p : ℤ) f) ≤
      Real.exp 1 * hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree 1 f) := by
  classical
  let d := f.totalDegree
  let F := scaledHomogenize d (p : ℤ) f
  let F₁ := scaledHomogenize d 1 f
  have hpZ : (p : ℤ) ≠ 0 := mod_cast hp.ne_zero
  have hir_iff {K : Type} [Field K] (φ : ℤ →+* K) (hh : φ (p : ℤ) ≠ 0) :
      Irreducible (map φ F) ↔ Irreducible (map φ F₁) := by
    dsimp only [F, F₁]
    rw [scaledHomogenize_map, scaledHomogenize_map, map_one]
    have hd' : (map φ f).totalDegree ≤ d := totalDegree_map_le _ _
    have heq : firstCoordinateScaleHom K (φ p) (scaledHomogenize d (φ p) (map φ f)) =
        C (φ p ^ d) * scaledHomogenize d 1 (map φ f) := by
      apply affineChart_injective_on_homogeneous
        (firstCoordinateScaleHom_homogeneous _ (scaledHomogenize_homogeneous _ _ hd'))
        ((scaledHomogenize_homogeneous 1 _ hd').C_mul _)
      rw [← homogeneousSlice_eq_chart_scale, homogeneousSlice_scaledHomogenize _ _ hd',
        map_mul, affineChart_scaledHomogenize_one]
      simp [affineChart]
    have hu : IsUnit (C (φ p ^ d) : MvPolynomial (Fin (n + 2)) K) :=
      (isUnit_iff_ne_zero.mpr (pow_ne_zero d hh)).map C
    have he := MulEquiv.irreducible_iff (f := firstCoordinateScale K (φ p) hh)
      (x := scaledHomogenize d (φ p) (map φ f))
    change Irreducible (firstCoordinateScaleHom K (φ p) _) ↔ _ at he
    exact (he.symm.trans (by rw [heq, irreducible_isUnit_mul hu]))
  by_cases hF : AbsolutelyIrreducible F
  · have hF₁ : AbsolutelyIrreducible F₁ := (hir_iff _ (by
      simpa only [Int.coe_castRingHom, Int.cast_natCast] using
        (Nat.cast_ne_zero.mpr hp.ne_zero : (p : AlgebraicClosure ℚ) ≠ 0))).mp hF
    have hdF : F.totalDegree = d :=
      (scaledHomogenize_homogeneous (p : ℤ) f le_rfl).totalDegree (scaledHomogenize_ne_zero d hpZ hf)
    have hdF₁ : F₁.totalDegree = d :=
      (scaledHomogenize_homogeneous 1 f le_rfl).totalDegree (scaledHomogenize_ne_zero d one_ne_zero hf)
    let S := (finite_fin_hypersurface_bad_primes F hF
      (absolute_integer_polynomial_totalDegree_pos F hF)).toFinset
    let T := (finite_fin_hypersurface_bad_primes F₁ hF₁
      (absolute_integer_polynomial_totalDegree_pos F₁ hF₁)).toFinset
    have hS (q) : q ∈ S ↔ stepanovThreshold F.totalDegree < q ∧ HypersurfaceBadReduction F q :=
      Set.Finite.mem_toFinset _
    have hT (q) : q ∈ T ↔ stepanovThreshold F₁.totalDegree < q ∧ HypersurfaceBadReduction F₁ q :=
      Set.Finite.mem_toFinset _
    have hsub : S ⊆ insert p T := fun q hq => by
      rcases eq_or_ne q p with rfl | hqp
      · exact Finset.mem_insert_self q T
      · obtain ⟨hthr, hbad⟩ := (hS q).mp hq
        let : Fact q.Prime := ⟨hbad.1⟩
        have hpK : (p : AlgebraicClosure (ZMod q)) ≠ 0 := by
          rw [Ne, CharP.cast_eq_zero_iff _ q]
          exact fun h => hqp ((Nat.prime_dvd_prime_iff_eq hbad.1 hp).mp h)
        rw [homogeneous_hypersurfaceBadReduction_iff _ (scaledHomogenize_homogeneous _ _ le_rfl)
          (scaledHomogenize_ne_zero d hpZ hf)] at hbad
        refine Finset.mem_insert_of_mem ((hT q).mpr ⟨by rwa [hdF₁, ← hdF], ?_⟩)
        rw [homogeneous_hypersurfaceBadReduction_iff _ (scaledHomogenize_homogeneous _ _ le_rfl)
          (scaledHomogenize_ne_zero d one_ne_zero hf)]
        exact mt (hir_iff _ (by simpa using hpK)).mpr hbad
    have hnn (q) (hq : q ∈ insert p T) : 0 ≤ Real.log q / q := by
      have hq1 : 1 ≤ q := by
        rcases Finset.mem_insert.mp hq with rfl | hqT
        · exact hp.one_le
        · exact ((hT q).mp hqT).2.1.one_le
      exact div_nonneg (Real.log_nonneg (mod_cast hq1)) (Nat.cast_nonneg q)
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub fun q hq _ => hnn q hq
    have h2 : ∑ q ∈ insert p T, Real.log q / q ≤ (∑ q ∈ T, Real.log q / q) + Real.log p / p := by
      by_cases hm : p ∈ T
      · rw [Finset.insert_eq_of_mem hm]
        exact le_add_of_nonneg_right (hnn p (Finset.mem_insert_self p T))
      · rw [Finset.sum_insert hm, add_comm]
    have hpR : (0 : ℝ) < p := mod_cast hp.pos
    have h3 : Real.log p / p ≤ 1 :=
      (div_le_one hpR).mpr (by linarith [Real.log_le_sub_one_of_pos hpR])
    rw [hypersurfaceBadPrimeFactor_eq_exp F hF rfl S hS,
      hypersurfaceBadPrimeFactor_eq_exp F₁ hF₁ rfl T hT, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  · rw [hypersurfaceBadPrimeFactor_eq_zero F hF]
    exact mul_nonneg (Real.exp_pos _).le (hypersurfaceBadPrimeFactor_nonneg _)

private lemma affine_scaling_box_power {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    {B A p : ℝ} (hB : 1 ≤ B) (hA : 1 ≤ A) (hp : 0 < p) (hBp : B / A ≤ p) :
    B ^ (((r : ℝ) + 1) / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))) /
        p ^ (1 / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))) ≤
      A * B ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) := by
  have hr1 : (1 : ℝ) ≤ r := mod_cast hr
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hroot : (1 : ℝ) ≤ (d : ℝ) ^ (1 / (r : ℝ)) := Real.one_le_rpow hd1 (by positivity)
  let β := 1 / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))
  have hβ1 : β ≤ 1 := (div_le_one (by positivity)).mpr (one_le_mul_of_one_le_of_one_le hr1 hroot)
  have hBA : B / p ≤ A := (div_le_iff₀ hp).mpr (by nlinarith [(div_le_iff₀ (by linarith : 0 < A)).mp hBp])
  have hpow : (B / p) ^ β ≤ A := (Real.rpow_le_rpow (by positivity) hBA (by dsimp [β]; positivity)).trans
    (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hA hβ1)
  have he : ((r : ℝ) + 1) / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ))) =
      1 / (d : ℝ) ^ (1 / (r : ℝ)) + β := by dsimp [β]; field_simp
  change B ^ (((r : ℝ) + 1) / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))) / p ^ β ≤ _
  rw [he, Real.rpow_add (by linarith), mul_div_assoc, ← Real.div_rpow (by linarith) hp.le]
  exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans_eq (mul_comm _ _)

private lemma affine_coefficient_height_cutoff (n d : ℕ) {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hheight : B / A ≤ ((n + d).choose d : ℝ) * Real.log ((n + d).choose d) +
      ((n + d).choose d : ℝ) * d * Real.log B) :
    B ≤ 4 * A ^ 2 * ((d : ℝ) + 1) ^ (4 * n + 2) := by
  have hN1 : (1 : ℝ) ≤ (n + d).choose d := mod_cast Nat.choose_pos (Nat.le_add_left d n)
  let N : ℝ := (n + d).choose d
  have hN1' : 1 ≤ N := hN1
  have hlogB : Real.log B ≤ 2 * Real.sqrt B := by
    have hh := Real.log_le_rpow_div (by linarith : 0 ≤ B) (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at hh; linarith
  have ht1 : 1 ≤ Real.sqrt B := by simpa using Real.sqrt_le_sqrt hB
  have hNsq : N ≤ N ^ 2 := by nlinarith
  have h1 : N * Real.log N ≤ N ^ 2 * Real.sqrt B :=
    (by nlinarith [Real.log_le_self (by linarith : 0 ≤ N)] : N * Real.log N ≤ N ^ 2).trans
      (le_mul_of_one_le_right (sq_nonneg N) ht1)
  have h2 : N * d * Real.log B ≤ 2 * N ^ 2 * d * Real.sqrt B := by
    calc N * d * Real.log B ≤ N * d * (2 * Real.sqrt B) :=
          mul_le_mul_of_nonneg_left hlogB (by positivity)
      _ ≤ N ^ 2 * d * (2 * Real.sqrt B) := by gcongr
      _ = 2 * N ^ 2 * d * Real.sqrt B := by ring
  have hmain : B ≤ (2 * A * N ^ 2 * ((d : ℝ) + 1)) * Real.sqrt B := by
    have hh := (div_le_iff₀ (by linarith : 0 < A)).mp hheight
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by linarith : 0 ≤ A),
      mul_le_mul_of_nonneg_left ht1 (show 0 ≤ A * N ^ 2 by positivity)]
  have hroot : Real.sqrt B ≤ 2 * A * N ^ 2 * ((d : ℝ) + 1) :=
    (mul_le_mul_iff_right₀ (by linarith : 0 < Real.sqrt B)).mp
      (by simpa only [← pow_two, Real.sq_sqrt (by linarith : 0 ≤ B), mul_comm] using hmain)
  have hcount : N ≤ ((d : ℝ) + 1) ^ n := by
    dsimp [N]; rw [← Nat.choose_symm_add, Nat.add_comm n d]
    exact_mod_cast Nat.choose_add_le_add_one_pow d n
  have hroot' : Real.sqrt B ≤ 2 * A * (((d : ℝ) + 1) ^ n) ^ 2 * ((d : ℝ) + 1) :=
    hroot.trans (by gcongr)
  have hh := pow_le_pow_left₀ (Real.sqrt_nonneg B) hroot' 2
  rw [Real.sq_sqrt (by linarith : 0 ≤ B)] at hh
  calc B ≤ (2 * A * (((d : ℝ) + 1) ^ n) ^ 2 * ((d : ℝ) + 1)) ^ 2 := hh
    _ = 4 * A ^ 2 * ((d : ℝ) + 1) ^ (4 * n + 2) := by
      rw [pow_add, Nat.mul_comm 4 n, pow_mul]; ring

private lemma polynomial_box_projective_power_bound {r d k : ℕ} (hr : 0 < r) (hd : 0 < d)
    {S B : ℝ} (hS : 1 ≤ S) (hB : 1 ≤ B) (hbound : B ≤ S * ((d : ℝ) + 1) ^ k) :
    B ^ (((r : ℝ) + 1) / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))) ≤
      Real.exp (Real.log S + (k : ℝ) * ((r : ℝ) + 1)) * B ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) := by
  have hr1 : (1 : ℝ) ≤ r := mod_cast hr
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hden : (1 : ℝ) ≤ r * (d : ℝ) ^ (1 / (r : ℝ)) :=
    one_le_mul_of_one_le_of_one_le hr1 (Real.one_le_rpow hd1 (by positivity))
  have hlog := Real.log_le_log (by linarith : 0 < B) hbound
  rw [Real.log_mul (by linarith) (by positivity), Real.log_pow] at hlog
  have hstep : Real.log B ≤ (Real.log S + (k : ℝ) * ((r : ℝ) + 1)) *
      ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ))) := by
    nlinarith [mul_le_mul_of_nonneg_left hden (Real.log_nonneg hS),
      mul_le_mul_of_nonneg_left (log_nat_add_one_le_root hr hd) (Nat.cast_nonneg (α := ℝ) k),
      mul_le_mul_of_nonneg_left hr1
        (show 0 ≤ (k : ℝ) * ((r : ℝ) + 1) * (d : ℝ) ^ (1 / (r : ℝ)) by positivity)]
  have hrootB : B ^ (1 / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))) ≤
      Real.exp (Real.log S + (k : ℝ) * ((r : ℝ) + 1)) := by
    rw [Real.rpow_def_of_pos (by linarith), Real.exp_le_exp, ← div_eq_mul_one_div]
    exact (div_le_iff₀ (by linarith)).mpr hstep
  have he : ((r : ℝ) + 1) / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ))) =
      1 / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ))) + 1 / (d : ℝ) ^ (1 / (r : ℝ)) := by
    field_simp; ring
  rw [he, Real.rpow_add (by linarith)]
  exact mul_le_mul_of_nonneg_right hrootB (by positivity)

private lemma scaled_auxiliary_expression_bound {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hf : f ≠ 0) (hd : 0 < f.totalDegree)
    {h : ℤ} (hh1 : 1 ≤ h) {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hhB : (h : ℝ) ≤ B)
    (hbox : B ^ boxExponent n f.totalDegree /
        (h : ℝ) ^ (1 / ((n + 1 : ℝ) * degreeRoot n f.totalDegree)) ≤
      A * B ^ (1 / degreeRoot n f.totalDegree))
    (hbad : hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree h f) ≤
      Real.exp 1 * hypersurfaceBadPrimeFactor f) :
    hypersurfaceAuxiliaryDegreeBound n f.totalDegree B
        (hypersurfaceBadPrimeFactor (scaledHomogenize f.totalDegree h f))
        (integerCoefficientHeight (scaledHomogenize f.totalDegree h f) : ℝ) ≤
      (hypersurfaceAbsoluteAuxiliaryConstant n *
        max ((n + 1 : ℝ) * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 3))
          (Real.exp 1) * A) *
        affineAuxiliaryDegreeExpression n f.totalDegree B
          (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
          (hypersurfaceBadPrimeFactor f) := by
  let d := f.totalDegree
  let F := scaledHomogenize d h f
  let L := (integerCoefficientHeight (homogeneousComponent d f) : ℝ)
  let H := (integerCoefficientHeight F : ℝ)
  let Y := (h : ℝ) ^ d * L
  let b := hypersurfaceBadPrimeFactor f
  let bF := hypersurfaceBadPrimeFactor F
  let β := 1 / ((n + 1 : ℝ) * degreeRoot n d)
  let q := heightExponent n d
  let K₀ := (n + 1 : ℝ) * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 3)
  let K := max K₀ (Real.exp 1)
  let T := Real.log L + d * Real.log B + (d : ℝ) ^ 2
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have hhR1 : (1 : ℝ) ≤ h := mod_cast hh1
  have hhR0 : (0 : ℝ) < h := by linarith
  have hL : 1 ≤ L := leading_height_one_le f hf
  have hY : 1 ≤ Y := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hhR1) hL
  have hYH : Y ≤ H := scaledHomogenize_leading_height_lower f hh1
  have hb : 0 ≤ b := hypersurfaceBadPrimeFactor_nonneg f
  have hbF : 0 ≤ bF := hypersurfaceBadPrimeFactor_nonneg F
  have hK1 : 1 ≤ K := (Real.one_le_exp zero_le_one).trans (le_max_right _ _)
  have hKA1 : 1 ≤ K * A := one_le_mul_of_one_le_of_one_le hK1 hA
  have hYpow : Y ^ q = (h : ℝ) ^ β * L ^ q := by
    dsimp only [Y, q, heightExponent, β]
    rw [Real.mul_rpow (by positivity) (by linarith), ← Real.rpow_natCast, ← Real.rpow_mul hhR0.le]
    congr 2; field_simp
  have hcoef : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * bF / H ^ q ≤
      K * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * min T ((d : ℝ) ^ 2 * b) / ((h : ℝ) ^ β * L ^ q) := by
    rcases le_total T ((d : ℝ) ^ 2 * b) with hmin | hmin
    · rw [min_eq_left hmin]
      have hF0 : F ≠ 0 := scaledHomogenize_ne_zero d (by omega) hf
      have hFdeg : F.totalDegree = d := (scaledHomogenize_homogeneous h f le_rfl).totalDegree hF0
      have htr := hypersurface_badPrime_height_transfer F hF0 hFdeg hd hY hYH
      change (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * bF / H ^ q ≤
        K₀ * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * (Real.log Y + (d : ℝ) ^ 2) / Y ^ q at htr
      rw [hYpow] at htr
      have hnum : Real.log Y + (d : ℝ) ^ 2 ≤ T := by
        dsimp only [Y, T]
        rw [Real.log_mul (by positivity) (by linarith), Real.log_pow]
        nlinarith [mul_le_mul_of_nonneg_left (Real.log_le_log hhR0 hhB) hd0.le]
      have hK0 : 0 ≤ K₀ := mul_nonneg (by positivity)
        (zero_le_one.trans (hypersurfaceHeightConstant_one_le _))
      have hK_le : K₀ ≤ K := le_max_left _ _
      have : 0 ≤ Real.log Y + (d : ℝ) ^ 2 := add_nonneg (Real.log_nonneg hY) (sq_nonneg _)
      exact htr.trans (by gcongr)
    · rw [min_eq_right hmin]
      have hdenom : Y ^ q ≤ H ^ q :=
        Real.rpow_le_rpow (by linarith) hYH (by dsimp [q, heightExponent, degreeRoot]; positivity)
      have hbFK : bF ≤ K * b := hbad.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hb)
      calc (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * bF / H ^ q
          ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * (K * b) / Y ^ q := by
            refine (div_le_div_of_nonneg_left (by positivity) (by positivity) hdenom).trans ?_
            gcongr
        _ = K * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * ((d : ℝ) ^ 2 * b) / ((h : ℝ) ^ β * L ^ q) := by
            rw [rpow_four_sub_eq_mul_sq hd0 n, hYpow]; ring
  let M := (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * min T ((d : ℝ) ^ 2 * b) *
      B ^ (1 / degreeRoot n d) / L ^ q
  have hT0 : 0 ≤ T := add_nonneg
    (add_nonneg (Real.log_nonneg hL) (mul_nonneg hd0.le (Real.log_nonneg hB))) (sq_nonneg _)
  have hmin0 : 0 ≤ min T ((d : ℝ) ^ 2 * b) := le_min hT0 (mul_nonneg (sq_nonneg _) hb)
  have hmain : auxMainTerm n d B bF H ≤ (K * A) * M := by
    calc auxMainTerm n d B bF H
        = ((d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * bF / H ^ q) * B ^ boxExponent n d := by
          dsimp [auxMainTerm]; ring
      _ ≤ (K * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * min T ((d : ℝ) ^ 2 * b) / ((h : ℝ) ^ β * L ^ q)) *
            B ^ boxExponent n d :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = (K * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * min T ((d : ℝ) ^ 2 * b) / L ^ q) *
            (B ^ boxExponent n d / (h : ℝ) ^ β) := by ring
      _ ≤ (K * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * min T ((d : ℝ) ^ 2 * b) / L ^ q) *
            (A * B ^ (1 / degreeRoot n d)) :=
          mul_le_mul_of_nonneg_left hbox (by positivity)
      _ = (K * A) * M := by dsimp [M]; ring
  let E := (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B + (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))
  have hE0 : 0 ≤ E := add_nonneg
    (mul_nonneg (Real.rpow_nonneg hd0.le _) (Real.log_nonneg hB)) (Real.rpow_nonneg hd0.le _)
  have hsum : auxDegreeBound n d B bF H ≤ (K * A) * (M + E) := by
    change auxMainTerm n d B bF H + _ + _ ≤ _
    have : auxMainTerm n d B bF H + (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
        (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) = auxMainTerm n d B bF H + E := by dsimp [E]; ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_right hKA1 hE0]
  have hh := mul_le_mul_of_nonneg_left hsum (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
  unfold hypersurfaceAuxiliaryDegreeBound affineAuxiliaryDegreeExpression
  dsimp only [M, E, T, q, heightExponent, degreeRoot] at hh
  convert hh using 1; ring

private lemma affineAuxiliaryDegreeExpression_translation {n d : ℕ} (hd : 0 < d)
    {B L b : ℝ} (hB : 1 ≤ B) (hL : 1 ≤ L) (hb : 0 ≤ b) :
    affineAuxiliaryDegreeExpression n d (B + d) L b ≤
      (2 * Real.exp ((n : ℝ) + 2)) * affineAuxiliaryDegreeExpression n d B L b := by
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hlog : Real.log (B + d) ≤ Real.log B + Real.log ((d : ℝ) + 1) := by
    rw [← Real.log_mul (by linarith) (by positivity)]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hlogd : Real.log ((d : ℝ) + 1) ≤ d := Real.log_add_one_le_self d.cast_nonneg
  have hmin : min (Real.log L + d * Real.log (B + d) + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) ≤
      2 * min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) := by
    rcases le_total (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (by
        nlinarith [Real.log_nonneg hL, Real.log_nonneg hB,
          mul_le_mul_of_nonneg_left hlog hd0.le, mul_le_mul_of_nonneg_left hlogd hd0.le])
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (by nlinarith [sq_nonneg (d : ℝ)])
  let root := (d : ℝ) ^ (1 / (n + 1 : ℝ))
  have hroot0 : 0 < root := by dsimp [root]; positivity
  have hpow : (B + d) ^ (1 / root) ≤ Real.exp ((n : ℝ) + 2) * B ^ (1 / root) := by
    have hf : ((d : ℝ) + 1) ^ (1 / root) ≤ Real.exp ((n : ℝ) + 2) := by
      rw [Real.rpow_def_of_pos (by positivity), Real.exp_le_exp, ← div_eq_mul_one_div]
      refine (div_le_iff₀ hroot0).mpr ?_
      simpa only [root, Nat.cast_add, Nat.cast_one, show (n : ℝ) + 1 + 1 = n + 2 by ring] using
        log_nat_add_one_le_root (r := n + 1) (by omega) hd
    calc (B + d) ^ (1 / root) ≤ (((d : ℝ) + 1) * B) ^ (1 / root) :=
          Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)
      _ = ((d : ℝ) + 1) ^ (1 / root) * B ^ (1 / root) :=
          Real.mul_rpow (by positivity) (by linarith)
      _ ≤ Real.exp ((n : ℝ) + 2) * B ^ (1 / root) :=
          mul_le_mul_of_nonneg_right hf (by positivity)
  have hlow : (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log (B + d) +
      (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) ≤
      (2 * Real.exp ((n : ℝ) + 2)) * ((d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
        (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))) := by
    have hdpow : (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * d ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) := by
      calc (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * d
          = (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * (d : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) := by rw [← Real.rpow_add hd0]; congr 1; ring
        _ ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
    have hlow0 : 0 ≤ (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) := by positivity
    have hstep : (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log (B + d) +
        (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) ≤
        2 * ((d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B + (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))) := by
      nlinarith [Real.log_nonneg hB, mul_le_mul_of_nonneg_left hlog hlow0,
        mul_le_mul_of_nonneg_left hlogd hlow0]
    have hE1 : 1 ≤ Real.exp ((n : ℝ) + 2) := Real.one_le_exp (by positivity)
    have hnn : 0 ≤ (d : ℝ) ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
        (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) :=
      add_nonneg (mul_nonneg hlow0 (Real.log_nonneg hB)) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hE1 hnn]
  have hBp : 1 ≤ B + d := by linarith
  have hminB0 : 0 ≤ min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) :=
    le_min (add_nonneg (add_nonneg (Real.log_nonneg hL)
      (mul_nonneg hd0.le (Real.log_nonneg hB))) (sq_nonneg _)) (mul_nonneg (sq_nonneg _) hb)
  have hminBp0 : 0 ≤ min (Real.log L + d * Real.log (B + d) + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) :=
    le_min (add_nonneg (add_nonneg (Real.log_nonneg hL)
      (mul_nonneg hd0.le (Real.log_nonneg hBp))) (sq_nonneg _)) (mul_nonneg (sq_nonneg _) hb)
  have hprod := mul_le_mul hmin hpow (by positivity) (by positivity)
  have hsc := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) / L ^ (1 / ((n + 1 : ℝ) * d * root)) by positivity)
  unfold affineAuxiliaryDegreeExpression
  dsimp only [root] at hsc
  convert add_le_add hsc hlow using 1 <;> ring

private lemma hypersurfaceBadPrimeFactor_affineTranslation {n : ℕ}
    (a : Fin (n + 1) → ℤ) (f : MvPolynomial (Fin (n + 1)) ℤ) :
    hypersurfaceBadPrimeFactor (affineTranslation ℤ a f) = hypersurfaceBadPrimeFactor f := by
  classical
  have hir : AbsolutelyIrreducible (affineTranslation ℤ a f) ↔ AbsolutelyIrreducible f := by
    dsimp only [AbsolutelyIrreducible]; rw [affineTranslation_map, affineTranslation_irreducible_iff]
  by_cases hf : AbsolutelyIrreducible f
  · let bad := (finite_fin_hypersurface_bad_primes f hf
      (absolute_integer_polynomial_totalDegree_pos f hf)).toFinset
    have hbad (p) : p ∈ bad ↔ stepanovThreshold f.totalDegree < p ∧ HypersurfaceBadReduction f p :=
      Set.Finite.mem_toFinset _
    rw [hypersurfaceBadPrimeFactor_eq_exp f hf rfl bad hbad]
    refine hypersurfaceBadPrimeFactor_eq_exp _ (hir.mpr hf) (affineTranslation_totalDegree a f)
      bad fun p => ?_
    rw [hbad]; refine and_congr_right fun _ => exists_congr fun hp => ?_
    let : Fact p.Prime := ⟨hp⟩
    dsimp only
    rw [affineTranslation_map, affineTranslation_totalDegree, affineTranslation_totalDegree,
      affineTranslation_irreducible_iff]
  · rw [hypersurfaceBadPrimeFactor_eq_zero f hf,
      hypersurfaceBadPrimeFactor_eq_zero _ fun h => hf (hir.mp h)]

private lemma affine_hypersurface_auxiliary_exists (n : ℕ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ (f : MvPolynomial (Fin (n + 2)) ℤ), PrimitiveIntegerPolynomial f →
      Irreducible f → 0 < f.totalDegree → ∀ {B : ℝ}, 1 ≤ B →
      ∃ g, IsBoxAuxiliary f g B ∧
        (g.totalDegree : ℝ) ≤ K₀ * affineAuxiliaryDegreeExpression n f.totalDegree B
          (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
          (hypersurfaceBadPrimeFactor f) := by
  let S : ℝ := 4 * scalingPrimeRatio ^ 2
  let k : ℕ := 4 * (n + 2) + 2
  let A : ℝ := max scalingPrimeRatio (Real.exp (Real.log S + (k : ℝ) * (n + 2 : ℝ)))
  let K : ℝ := max ((n + 1 : ℝ) * Real.exp (2 * mertensError + 1) *
    hypersurfaceHeightConstant (n + 3)) (Real.exp 1)
  let C₀ : ℝ := hypersurfaceAbsoluteAuxiliaryConstant n * K * A
  have hR1 : 1 ≤ scalingPrimeRatio := scalingPrimeRatio_one_le
  have hS1 : 1 ≤ S := by dsimp [S]; nlinarith
  have hA1 : 1 ≤ A := hR1.trans (le_max_left _ _)
  have hK1 : 1 ≤ K := (Real.one_le_exp zero_le_one).trans (le_max_right _ _)
  have hC0_1 : 1 ≤ C₀ := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (hypersurfaceAbsoluteAuxiliaryConstant_one_le n) hK1) hA1
  have hnz : ∀ (t : MvPolynomial (Fin (n + 2)) ℤ), PrimitiveIntegerPolynomial t →
      Irreducible t → 0 < t.totalDegree → t.coeff 0 ≠ 0 → ∀ {B : ℝ}, 1 ≤ B →
      ∃ g, IsBoxAuxiliary t g B ∧
        (g.totalDegree : ℝ) ≤ C₀ * affineAuxiliaryDegreeExpression n t.totalDegree B
          (integerCoefficientHeight (homogeneousComponent t.totalDegree t) : ℝ)
          (hypersurfaceBadPrimeFactor t) := by
    intro t htprim htir htd hc B hB
    let d := t.totalDegree
    have hb_un : hypersurfaceBadPrimeFactor (scaledHomogenize d 1 t) ≤
        hypersurfaceBadPrimeFactor t := hypersurfaceBadPrimeFactor_unscaledHomogenize_le t htir.ne_zero
    have hbt0 : 0 ≤ hypersurfaceBadPrimeFactor t := hypersurfaceBadPrimeFactor_nonneg t
    have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
    by_cases hsmall : B ≤ S * ((d : ℝ) + 1) ^ k
    · have h1prim : PrimitiveIntegerPolynomial (scaledHomogenize d 1 t) := fun c hcd =>
        htprim c fun m => by simpa [scaledHomogenize_coefficient] using hcd (homogenizedExponent d m)
      obtain ⟨g, hg, hgdeg⟩ := scaled_affine_auxiliary t htir htd le_rfl h1prim hB
        (by simpa using hB)
      refine ⟨g, hg, hgdeg.trans (scaled_auxiliary_expression_bound t htir.ne_zero htd le_rfl
        hA1 hB (by simpa using hB) ?_ (hb_un.trans (le_mul_of_one_le_left hbt0 he1)))⟩
      rw [Int.cast_one, Real.one_rpow, div_one]
      have hpw := polynomial_box_projective_power_bound (r := n + 1) (by omega) htd hS1 hB hsmall
      simpa only [boxExponent, degreeRoot, Nat.cast_add, Nat.cast_one,
        show (n : ℝ) + 1 + 1 = n + 2 by ring] using
        hpw.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    · have hRB : scalingPrimeRatio ≤ B := by
        have hRS : scalingPrimeRatio ≤ S := by dsimp [S]; nlinarith
        have hpow1 : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ k :=
          one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) d])
        exact (hRS.trans (le_mul_of_one_le_right (by linarith) hpow1)).trans (le_of_not_ge hsmall)
      by_cases hheight : Real.log |(t.coeff 0 : ℝ)| < B / scalingPrimeRatio
      · obtain ⟨p, hp, hlo, hhi, hnd⟩ := exists_scaling_prime hRB hc hheight
        obtain ⟨g, hg, hgdeg⟩ := scaled_affine_auxiliary t htir htd (mod_cast hp.one_le)
          (htprim.scaledHomogenize d hp hnd) hB (by simpa using hhi)
        refine ⟨g, hg, hgdeg.trans (scaled_auxiliary_expression_bound t htir.ne_zero htd
          (mod_cast hp.one_le) hA1 hB (by simpa using hhi) ?_ ?_)⟩
        · have hpw := affine_scaling_box_power (r := n + 1) (by omega) htd hB hR1
            (mod_cast hp.pos) hlo.le
          simpa only [boxExponent, degreeRoot, Int.cast_natCast, Nat.cast_add, Nat.cast_one,
            show (n : ℝ) + 1 + 1 = n + 2 by ring] using
            hpw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        · exact (hypersurfaceBadPrimeFactor_scaledHomogenize_le t htir.ne_zero hp).trans
            (mul_le_mul_of_nonneg_left hb_un (Real.exp_pos _).le)
      · rcases affine_coefficient_height_dichotomy t htir.ne_zero htprim hB with hh | ⟨g, hg, hgdeg⟩
        · have hcoef := Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hc))
            (coefficient_abs_le_integerCoefficientHeight t 0)
          exact (hsmall (affine_coefficient_height_cutoff (n + 2) d hR1 hB
            ((le_of_not_gt hheight).trans (hcoef.trans hh)))).elim
        · refine ⟨g, hg, ?_⟩
          have hL : 1 ≤ (integerCoefficientHeight (homogeneousComponent d t) : ℝ) :=
            leading_height_one_le t htir.ne_zero
          have hdE : (d : ℝ) ≤ affineAuxiliaryDegreeExpression n d B
              (integerCoefficientHeight (homogeneousComponent d t) : ℝ)
              (hypersurfaceBadPrimeFactor t) := by
            have hdD : (d : ℝ) ≤ (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) := le_rpow_four_sub_inv htd
            have hmin0 : 0 ≤ min (Real.log (integerCoefficientHeight (homogeneousComponent d t) : ℝ) +
                d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * hypersurfaceBadPrimeFactor t) :=
              le_min (add_nonneg (add_nonneg (Real.log_nonneg hL)
                (mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg hB))) (sq_nonneg _))
                (mul_nonneg (sq_nonneg _) hbt0)
            have hBlog := Real.log_nonneg hB
            unfold affineAuxiliaryDegreeExpression
            exact hdD.trans (le_add_of_nonneg_left (by positivity))
          exact ((Nat.cast_le.mpr hgdeg).trans hdE).trans
            (le_mul_of_one_le_left (by linarith [Nat.cast_nonneg (α := ℝ) d]) hC0_1)
  refine ⟨(2 * Real.exp ((n : ℝ) + 2)) * C₀, by positivity, fun f hprim hir hd {B} hB => ?_⟩
  let d := f.totalDegree
  obtain ⟨a, ha, hc⟩ := exists_bounded_affine_translation_nonzero_constant f hir.ne_zero
  let t := affineTranslation ℤ a f
  have htd : t.totalDegree = d := affineTranslation_totalDegree a f
  have hBp : 1 ≤ B + d := by linarith [Nat.cast_nonneg (α := ℝ) d]
  obtain ⟨g, hg, hgdeg⟩ := hnz t (hprim.translate_affine a)
    ((affineTranslation_irreducible_iff a f).mpr hir) (htd ▸ hd) hc hBp
  let G := (affineTranslation ℤ a).symm g
  have hGnd : ¬ f ∣ G := fun hdvd => hg.not_dvd <| by
    have hh := map_dvd (affineTranslation ℤ a).toRingHom hdvd
    change affineTranslation ℤ a f ∣ affineTranslation ℤ a ((affineTranslation ℤ a).symm g) at hh
    rwa [AlgEquiv.apply_symm_apply] at hh
  refine ⟨G, ⟨(affineTranslation ℤ a).symm.injective.ne (by simpa using hg.ne_zero), hGnd,
    fun x hx hxf => ?_⟩, ?_⟩
  · change eval x (affineTranslation ℤ (-a) g) = 0
    rw [affineTranslation_eval]
    refine hg.vanishes (x - a) (fun j => ?_) (by rw [affineTranslation_eval, sub_add_cancel, hxf])
    change |((x j - a j : ℤ) : ℝ)| ≤ B + d
    rw [Int.cast_sub]
    have ha' : |(a j : ℝ)| ≤ d := by
      rw [abs_of_nonneg (mod_cast (ha j).1)]; exact_mod_cast (ha j).2
    exact (abs_sub _ _).trans (add_le_add (hx j) ha')
  · rw [show G.totalDegree = g.totalDegree from affineTranslation_totalDegree (-a) g]
    rw [affineTranslation_leading_homogeneousComponent a f, htd,
      hypersurfaceBadPrimeFactor_affineTranslation] at hgdeg
    have htr := affineAuxiliaryDegreeExpression_translation (n := n) hd hB
      (leading_height_one_le f hir.ne_zero) (hypersurfaceBadPrimeFactor_nonneg f)
    refine hgdeg.trans ?_
    calc C₀ * affineAuxiliaryDegreeExpression n d (B + d) _ _
        ≤ C₀ * ((2 * Real.exp ((n : ℝ) + 2)) * affineAuxiliaryDegreeExpression n d B _ _) :=
          mul_le_mul_of_nonneg_left htr (by linarith)
      _ = ((2 * Real.exp ((n : ℝ) + 2)) * C₀) * affineAuxiliaryDegreeExpression n d B _ _ := by ring

def affineHypersurfaceAuxiliaryConstant (n : ℕ) : ℝ :=
  (affine_hypersurface_auxiliary_exists n).choose

lemma affineHypersurfaceAuxiliaryConstant_pos (n : ℕ) :
    0 < affineHypersurfaceAuxiliaryConstant n := by
  unfold affineHypersurfaceAuxiliaryConstant
  exact (affine_hypersurface_auxiliary_exists n).choose_spec.1

theorem affine_hypersurface_auxiliary {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree) {B : ℝ} (hB : 1 ≤ B) :
    ∃ g, IsBoxAuxiliary f g B ∧
      (g.totalDegree : ℝ) ≤ affineHypersurfaceAuxiliaryConstant n *
        affineAuxiliaryDegreeExpression n f.totalDegree B
          (integerCoefficientHeight (homogeneousComponent f.totalDegree f) : ℝ)
          (hypersurfaceBadPrimeFactor f) := by
  unfold affineHypersurfaceAuxiliaryConstant
  exact (affine_hypersurface_auxiliary_exists n).choose_spec.2 f hprim hir hd hB

end
end CCDN
