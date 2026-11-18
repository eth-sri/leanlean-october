module

public import CCDN.Algebra.MonomialEvaluationMatrix
public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Analysis.PrimeCutoff
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimes
public import CCDN.Determinant.HypersurfaceDeterminantRank
public import CCDN.ForMathlib.StandardExponents
public import CCDN.Height.CountingHypotheses
public import CCDN.Plane.IntegerPlaneLogHeight
import ArithmeticHeights.BombieriVaaler
import CCDN.Algebra.RowSelection
import CCDN.AuxiliaryPolynomial.BadPrimeCharge
import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeCoordinates
import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeHeight
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceAuxiliary
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceBadPrimes
import CCDN.Determinant.AffineCongruenceDeterminant
import Mathlib.Algebra.Order.AbsoluteValue.Int

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset Matrix

def congruenceHeightCharge (m d : ℕ) (H Q : ℝ) : ℝ :=
  Real.log (1 + 27 * (d : ℝ) ^ 4 *
    (hypersurfaceHeightConstant m * (1 + Real.log H / (d : ℝ) ^ 2)) + Q) +
      2 * mertensError + 1

def affineCongruenceDeterminantLower (n d s : ℕ) (H Q : ℝ) : ℝ :=
  ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) / (n + 2 : ℝ) *
    (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) *
      (Real.log s - (n + 1 : ℝ) * (4 * Real.log d +
        congruenceHeightCharge (n + 3) d H Q) - hypersurfaceDeterminantError n) +
    (hypersurfaceDeterminantMain n s - (n + 2 : ℝ) * s) * Q

private theorem hypersurface_and_congruence_prime_charge
    {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ)
    (hf : Irreducible (map (Int.castRingHom L) f)) (hd : 0 < f.totalDegree)
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : CoefficientHeightLE f H)
    (bad P : Finset ℕ)
    (hbad : ∀ p ∈ bad, stepanovThreshold f.totalDegree < p ∧ HypersurfaceBadReduction f p)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ bad ∪ P, Real.log p / p) ≤
      congruenceHeightCharge (n + 1) f.totalDegree H (∑ p ∈ P, Real.log p) := by
  classical
  let e : Fin (n + 1) ≃ Option (Fin n) := finSuccEquiv' 0
  let g := rename e f
  have hg : Irreducible (map (Int.castRingHom L) g) := by
    rw [show g = rename e f from rfl, map_rename]
    exact (MulEquiv.irreducible_iff (f := renameEquiv L e)).mpr hf
  have hgd : g.totalDegree = f.totalDegree := totalDegree_renameEquiv e f
  obtain ⟨D, hD, hheight, hdiv⟩ := exists_hypersurface_bad_prime_height_witness g hg
    (hgd ▸ hd) H hH (polynomial_coefficient_bound_renameEquiv e f H hcoeff)
  simp only [hgd, Fintype.card_option, Fintype.card_fin] at hheight
  let q : ℤ := ∏ p ∈ P, (p : ℤ)
  have hq : 0 < q := prod_pos fun p hp => mod_cast (hP p hp).pos
  have hprime (p : ℕ) (hp : p ∈ bad ∪ P) : p.Prime :=
    (mem_union.mp hp).elim (fun hb => (hbad p hb).2.choose) (hP p)
  have hdvd (p : ℕ) (hp : p ∈ bad ∪ P) : (p : ℤ) ∣ D * q := by
    rcases mem_union.mp hp with hb | hp
    · refine dvd_mul_of_dvd_left (hdiv p (hgd ▸ ?_)
        ((hypersurfaceBadReduction_renameEquiv e f p).mpr (hbad p hb).2)) _
      have hcut : 27 * f.totalDegree ^ 4 < p := (hbad p hb).1
      nlinarith [Nat.le_mul_self f.totalDegree, Nat.le_mul_self (f.totalDegree * f.totalDegree)]
    · exact dvd_mul_of_dvd_right (dvd_prod_of_mem (fun p : ℕ => (p : ℤ)) hp) D
  have hC0 : 0 ≤ hypersurfaceHeightConstant (n + 1) :=
    zero_le_one.trans (hypersurfaceHeightConstant_one_le (n + 1))
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH
  have hsumP : 0 ≤ ∑ p ∈ P, Real.log p := sum_nonneg fun p _ => Real.log_natCast_nonneg p
  unfold congruenceHeightCharge
  have hterm : 0 ≤ 27 * (f.totalDegree : ℝ) ^ 4 *
      (hypersurfaceHeightConstant (n + 1) * (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) := by
    positivity
  refine bad_prime_charge_of_height (bad ∪ P) (mul_pos hD hq) hprime hdvd (L := 1)
    (H := 1 + 27 * (f.totalDegree : ℝ) ^ 4 *
      (hypersurfaceHeightConstant (n + 1) * (1 + Real.log H / (f.totalDegree : ℝ) ^ 2)) +
      ∑ p ∈ P, Real.log p)
    (by norm_num) (by linarith) (fun p hp => mod_cast (hprime p hp).one_lt) ?_
  rw [Int.cast_mul, Real.log_mul (mod_cast hD.ne') (mod_cast hq.ne'), one_mul]
  have hlogq : Real.log (q : ℝ) = ∑ p ∈ P, Real.log p := by
    dsimp [q]; rw [Int.cast_prod, Real.log_prod fun p hp => mod_cast (hP p hp).ne_zero]; simp
  linarith

private theorem square_minorGcd_eq_abs_det {s : ℕ} (A : Matrix (Fin s) (Fin s) ℤ) :
    Int.Matrix.minorGcd A = |A.det| := by
  classical
  have hid (f : Fin s ↪o Fin s) : ⇑f = id :=
    (Finset.orderEmbOfFin_unique (s := univ) (by simp) (fun _ => mem_univ _) f.strictMono).trans
      (Finset.orderEmbOfFin_unique (s := univ) (by simp) (fun _ => mem_univ _) strictMono_id).symm
  have hne : (univ : Finset (Fin s ↪o Fin s)).Nonempty :=
    ⟨(OrderIso.refl (Fin s)).toOrderEmbedding, mem_univ _⟩
  rw [Int.Matrix.minorGcd, show (fun f : Fin s ↪o Fin s => (A.submatrix id f).det) =
      fun _ => A.det from funext fun f => by rw [hid f, Matrix.submatrix_id_id],
    Finset.gcd_eq_gcd_image, Finset.image_const hne, Finset.gcd_singleton, id_eq,
    ← Int.abs_eq_normalize]

private theorem weighted_evaluation_det_log_bound {n s : ℕ}
    (mon : Fin s → (Fin n →₀ ℕ)) (z : Fin s → (Fin n → ℤ))
    {B : ℝ} (hB : 1 ≤ B) (hz : ∀ i, InBox (z i) B)
    (hne : (evaluationMatrix mon z).det ≠ 0) :
    Real.log |((evaluationMatrix mon z).det : ℝ)| ≤
      Real.log (s.factorial : ℝ) + (∑ j, ((Finsupp.degree (mon j) : ℕ) : ℝ)) * Real.log B := by
  classical
  let abv : AbsoluteValue ℝ ℝ := AbsoluteValue.abs
  let M_R := (evaluationMatrix mon z).map (Int.castRingHom ℝ)
  have hdet_le : |((evaluationMatrix mon z).det : ℝ)| ≤
      (s.factorial : ℝ) * B ^ (∑ j, Finsupp.degree (mon j)) := by
    have he : M_R.det = ((evaluationMatrix mon z).det : ℝ) := ((Int.castRingHom ℝ).map_det _).symm
    rw [← he]
    calc |M_R.det|
        ≤ ∑ σ : Equiv.Perm (Fin s), abv (Equiv.Perm.sign σ • ∏ j, M_R (σ j) j) := by
          rw [Matrix.det_apply]; exact abv.sum_le _ _
      _ = ∑ σ : Equiv.Perm (Fin s), ∏ j, |M_R (σ j) j| :=
          sum_congr rfl fun σ _ => by rw [abv.map_units_int_smul, abv.map_prod]; rfl
      _ ≤ ∑ _σ : Equiv.Perm (Fin s), ∏ j, B ^ Finsupp.degree (mon j) :=
          sum_le_sum fun σ _ => prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j _ =>
            abs_monomial_value_le (mon j) (z (σ j)) hB (hz (σ j)) le_rfl
      _ = (s.factorial : ℝ) * B ^ (∑ j, Finsupp.degree (mon j)) := by
          simp [Fintype.card_perm, prod_pow_eq_pow_sum]
  have hB0 : 0 < B := by linarith
  have hfac : (0 : ℝ) < s.factorial := mod_cast Nat.factorial_pos s
  have hlog := Real.log_le_log (abs_pos.mpr (mod_cast hne)) hdet_le
  rw [Real.log_mul hfac.ne' (pow_pos hB0 _).ne', Real.log_pow] at hlog
  simpa only [Nat.cast_sum] using hlog

theorem exists_affine_congruence_auxiliary_of_gap {n N t M : ℕ} (hN : 0 < N)
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H) (hcoeff : CoefficientHeightLE f H)
    (mon : Fin N → (Fin (n + 2) →₀ ℕ)) (hmon : Function.Injective mon)
    (hstd : ∀ j, mon j ∈ Ideal.standardExponents
      (Ideal.span {map (Int.castRingHom ℚ) f}) MonomialOrder.degLex)
    (hdegree : ∀ j, Finsupp.degree (mon j) ≤ M)
    {B : ℝ} {x : Fin t → IntPoint (n + 2)} (hxB : IsBoxZeroFamily f B x)
    (P : Finset ℕ) (a : ℕ → IntPoint (n + 2)) (hres : IsSmoothResidueFamily f P a x)
    (hgap : Real.log (N.factorial : ℝ) +
      (∑ j, ((Finsupp.degree (mon j) : ℕ) : ℝ)) * Real.log B <
      affineCongruenceDeterminantLower n f.totalDegree N H (∑ p ∈ P, Real.log p)) :
    ∃ g : MvPolynomial (Fin (n + 2)) ℤ, g ≠ 0 ∧
      ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g ∧
      g.totalDegree ≤ M ∧ ∀ i, eval (x i) g = 0 := by
  classical
  have hdet (b : Fin N → Fin t) : (evaluationMatrix mon (x ∘ b)).det = 0 := by
    by_contra hne
    let G : Fin N → MvPolynomial (Fin (n + 2)) ℤ := fun j => monomial (mon j) 1
    have hG (j) : (G j).totalDegree ≤ M := (totalDegree_monomial_le _ _).trans (hdegree j)
    have hmat : (Matrix.of fun i j => eval ((x ∘ b) i) (G j)) = evaluationMatrix mon (x ∘ b) := by
      ext i j; simp only [Matrix.of_apply, G, eval_monomial, one_mul]; rfl
    have hrows : LinearIndependent ℚ
        ((Matrix.of fun i j => eval ((x ∘ b) i) (G j)).map ((↑) : ℤ → ℚ)).row := by
      rw [hmat, Matrix.linearIndependent_row_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
        isUnit_iff_ne_zero]
      change ((Int.castRingHom ℚ).mapMatrix (evaluationMatrix mon (x ∘ b))).det ≠ 0
      rw [← RingHom.map_det]; change ((evaluationMatrix mon (x ∘ b)).det : ℚ) ≠ 0
      exact_mod_cast hne
    obtain ⟨bad, hbad, hbound⟩ := exists_affine_congruence_determinant_log_lower hN f hir hd
      G hG (x ∘ b) (fun i => hxB.eval_eq_zero (b i)) hrows P a
      ⟨hres.prime, hres.eval_eq_zero, hres.smooth, fun p hp i j => hres.dvd_sub p hp (b i) j⟩
    let F := scaledHomogenize f.totalDegree 1 f
    have hf0 : f ≠ 0 := ne_zero_of_irreducible_map hir
    have hFdeg : F.totalDegree = f.totalDegree :=
      (scaledHomogenize_homogeneous 1 f le_rfl).totalDegree (scaledHomogenize_ne_zero _ one_ne_zero hf0)
    have hFht : (integerCoefficientHeight F : ℝ) ≤ H := by
      rw [show F = scaledHomogenize f.totalDegree 1 f from rfl, integerCoefficientHeight_scaledHomogenize_one]
      exact integerCoefficientHeight_le f (by linarith) hcoeff
    have hc := hypersurface_and_congruence_prime_charge F
      ((unscaledHomogenize_absolute_irreducible_iff f hf0).mpr hir) (hFdeg ▸ hd) H hH
      (fun e => (coefficient_abs_le_integerCoefficientHeight F e).trans hFht) bad P
      (fun p hp => by simpa only [hFdeg] using (hbad p).mp hp) hres.prime
    rw [hFdeg] at hc
    have hlo : affineCongruenceDeterminantLower n f.totalDegree N H (∑ p ∈ P, Real.log p) ≤
        Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval ((x ∘ b) i) (G j))) := by
      refine le_trans (add_le_add (mul_le_mul_of_nonneg_left ?_ (by positivity)) le_rfl) hbound
      nlinarith [mul_le_mul_of_nonneg_left hc (show 0 ≤ (n + 1 : ℝ) by positivity)]
    rw [hmat, square_minorGcd_eq_abs_det, Int.cast_abs] at hlo
    exact (not_lt_of_ge (hlo.trans (weighted_evaluation_det_log_bound mon (x ∘ b)
      hxB.one_le_radius (fun i j => hxB.abs_le (b i) j) hne))) hgap
  let A := evaluationMatrix mon x
  obtain ⟨r, b, _, hli, hspan, _⟩ := exists_independent_spanning_rows (A.map ((↑) : ℤ → ℚ))
  have hrN : r < N := by
    by_contra hn
    obtain rfl : r = N := by omega
    have hnonzero := ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_row_iff_isUnit.mp hli)).ne_zero
    refine hnonzero ?_
    have heA : (A.map ((↑) : ℤ → ℚ)).submatrix b id =
        (Int.castRingHom ℚ).mapMatrix (evaluationMatrix mon (x ∘ b)) := by ext; rfl
    rw [heA, ← RingHom.map_det, hdet b, map_zero]
  obtain ⟨v, hv, hAv, _⟩ := Int.Matrix.exists_ne_zero_mulVec_eq_zero_iSup_abs_le_det_rpow
    (evaluationMatrix mon (x ∘ b)) hli (by simpa using hrN)
  let g := polynomialOfCoefficients mon v
  have hg0 : g ≠ 0 := polynomialOfCoefficients_ne_zero mon hmon hv
  have hgQ : map (Int.castRingHom ℚ) g ≠ 0 := fun h =>
    hg0 ((map_injective (Int.castRingHom ℚ) Int.cast_injective) (by simpa using h))
  have hgstd : map (Int.castRingHom ℚ) g ∈
      restrictSupport ℚ (Ideal.standardExponents
        (Ideal.span {map (Int.castRingHom ℚ) f}) MonomialOrder.degLex) := fun m hm => by
    by_contra hbad
    have hne (j : Fin N) : mon j ≠ m := fun he => hbad (he ▸ hstd j)
    exact (mem_support_iff.mp hm) (by
      simp [g, polynomialOfCoefficients, coeff_monomial, hne])
  refine ⟨g, hg0, fun hdvd => hgQ (Ideal.eq_zero_of_mem_restrictSupport_standardExponents _
    MonomialOrder.degLex hgstd (Ideal.mem_span_singleton.mpr hdvd)),
    totalDegree_polynomialOfCoefficients_le mon v hdegree, fun i =>
      vanishes_of_evaluation_row_mem_span mon (x ∘ b) v hAv _
        (hspan ▸ Submodule.subset_span ⟨i, rfl⟩)⟩

end
end CCDN
