module

public import CCDN.Algebra.HomogeneousSlice
public import CCDN.AuxiliaryPolynomial.Nonmultiple
public import CCDN.Height.IntegerCoefficientHeight
import ArithmeticHeights.BombieriVaaler
import CCDN.Algebra.HomogeneousEvaluation
import CCDN.Algebra.HomogeneousMonomials
import CCDN.Algebra.HomogeneousRank
import CCDN.Algebra.PrimitiveNormalization
import CCDN.Algebra.RowSelection
import CCDN.AuxiliaryPolynomial.CoefficientBound
import CCDN.Determinant.HomogeneousDeterminantComparison

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

lemma integerCoefficientHeight_scaledHomogenize_one {n : ℕ} (d : ℕ)
    (f : MvPolynomial (Fin n) ℤ) :
    integerCoefficientHeight (scaledHomogenize d 1 f) = integerCoefficientHeight f := by
  classical
  have hupper : (integerCoefficientHeight (scaledHomogenize d 1 f) : ℝ) ≤
      integerCoefficientHeight f := by
    refine integerCoefficientHeight_le _ (Nat.cast_nonneg _) fun m => ?_
    by_cases hm : ∃ k, homogenizedExponent d k = m
    · obtain ⟨k, rfl⟩ := hm
      simpa only [scaledHomogenize_coefficient, one_pow, one_mul] using
        coefficient_abs_le_integerCoefficientHeight f k
    · have hz : (scaledHomogenize d 1 f).coeff m = 0 := by
        simp only [scaledHomogenize, coeff_sum]
        exact Finset.sum_eq_zero fun k _ => by
          simp only [coeff_monomial, ite_eq_right fun h => hm ⟨k, h⟩]
      simp [hz]
  have hlower : (integerCoefficientHeight f : ℝ) ≤
      integerCoefficientHeight (scaledHomogenize d 1 f) :=
    integerCoefficientHeight_le _ (Nat.cast_nonneg _) fun m => by
      simpa only [scaledHomogenize_coefficient, one_pow, one_mul] using
        coefficient_abs_le_integerCoefficientHeight (scaledHomogenize d 1 f)
          (homogenizedExponent d m)
  exact_mod_cast le_antisymm hupper hlower

private lemma homogeneous_no_auxiliary_coefficient_height {n d t : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    (z : Fin t → IntPoint (n + 1)) (hz : ∀ i, eval (z i) f = 0)
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i, InBox (z i) B)
    (hrel : ∀ g : MvPolynomial (Fin (n + 1)) ℤ, g.IsHomogeneous d →
      (∀ i, eval (z i) g = 0) → f ∣ g) :
    Real.log (integerCoefficientHeight f : ℝ) ≤
      ((n + d).choose d : ℝ) * Real.log ((n + d).choose d) +
        ((n + d).choose d : ℝ) * d * Real.log B := by
  classical
  obtain ⟨s, a, ha, hli, hspan, hs⟩ :=
    homogeneous_independent_evaluation_rows f hf hf0 le_rfl z hz
  let mon := homogeneousMonomials n d
  let A := evaluationMatrix mon (z ∘ a)
  let N := (n + d).choose d
  obtain ⟨v, hv, hAv, hsmall⟩ :=
    Int.Matrix.exists_ne_zero_mulVec_eq_zero_iSup_abs_le_det_rpow A hli (by simpa using hs)
  simp only [Fintype.card_fin] at hsmall
  let g := polynomialOfCoefficients mon v
  have hg0 : g ≠ 0 := polynomialOfCoefficients_ne_zero mon (homogeneousMonomials_injective n d) hv
  have hgh : g.IsHomogeneous d := polynomialOfCoefficients_homogeneous n d v
  have hgz (i) : eval (z i) g = 0 :=
    vanishes_of_evaluation_row_mem_span mon (z ∘ a) v hAv (z i)
      (hspan ▸ Submodule.subset_span ⟨i, rfl⟩)
  have hD1 : (1 : ℝ) ≤ (Int.Matrix.minorGcd A : ℝ) := mod_cast Int.Matrix.one_le_minorGcd hli
  have hD0 : (0 : ℝ) < (Int.Matrix.minorGcd A : ℝ) := by linarith
  let R := (Real.sqrt (((A * Aᵀ).det : ℤ) : ℝ) / (Int.Matrix.minorGcd A : ℝ)) ^ (((N : ℝ) - s)⁻¹)
  have hR0 : 0 ≤ R := Real.rpow_nonneg (div_nonneg (Real.sqrt_nonneg _) hD0.le) _
  have hc : CoefficientHeightLE g R :=
    abs_coefficient_polynomialOfCoefficients_le mon (homogeneousMonomials_injective n d) v hR0
      fun j => (show |(v j : ℝ)| ≤ ((⨆ k, |v k| : ℤ) : ℝ) from
        mod_cast le_ciSup (Set.finite_range fun k => |v k|).bddAbove j).trans hsmall
  obtain ⟨q, hfq⟩ := hrel g hgh hgz
  have hq0 : q ≠ 0 := fun h => hg0 (by simp [hfq, h])
  have hqdeg : q.totalDegree = 0 := by
    have hh := totalDegree_mul_of_isDomain hf0 hq0
    rw [← hfq, hf.totalDegree hf0, hgh.totalDegree hg0] at hh; omega
  have hqC := totalDegree_eq_zero_iff_eq_C.mp hqdeg
  have hqc0 : q.coeff 0 ≠ 0 := fun h => hq0 (by simpa [h] using hqC)
  have hHb : (integerCoefficientHeight f : ℝ) ≤ R := integerCoefficientHeight_le f hR0 fun m =>
    (integer_scalar_factor_coefficient_bound hqc0
      ((hfq.trans (congrArg (f * ·) hqC)).trans (mul_comm _ _)) m).trans (hc m)
  have hH1 : (1 : ℝ) ≤ integerCoefficientHeight f := mod_cast integerCoefficientHeight_pos f hf0
  let H := (integerCoefficientHeight f : ℝ)
  have hNs : (1 : ℝ) ≤ (N : ℝ) - s := by
    have : (s : ℝ) + 1 ≤ N := mod_cast hs; linarith
  obtain ⟨hGram, _⟩ := log_gcd_le_of_coefficient_bound (by linarith : 0 < H) hD0 (by linarith) hHb
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le s) hs
  have harch := evaluation_log_gram_le hN mon (z ∘ a) hB (fun i j => hbox (a i) j)
    (fun j => (homogeneousMonomials_degree n d j).le) hGram
  have hlogfact : Real.log (s.factorial : ℝ) ≤ (s : ℝ) * Real.log (N : ℝ) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (mod_cast Nat.factorial_pos s)
      (mod_cast (Nat.factorial_le_pow s).trans (Nat.pow_le_pow_left hs.le s))
  have hsN : (s : ℝ) ≤ N := mod_cast hs.le
  nlinarith [mul_le_mul_of_nonneg_right hNs (Real.log_nonneg hH1),
    Real.log_nonneg hD1,
    mul_le_mul_of_nonneg_right hsN (Real.log_nonneg (mod_cast hN : (1 : ℝ) ≤ N)),
    mul_le_mul_of_nonneg_right hsN (mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (Real.log_nonneg hB))]

theorem affine_coefficient_height_dichotomy {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hf0 : f ≠ 0) (hprim : PrimitiveIntegerPolynomial f)
    {B : ℝ} (hB : 1 ≤ B) :
    Real.log (integerCoefficientHeight f : ℝ) ≤
      ((n + f.totalDegree).choose f.totalDegree : ℝ) *
        Real.log ((n + f.totalDegree).choose f.totalDegree) +
      ((n + f.totalDegree).choose f.totalDegree : ℝ) * f.totalDegree * Real.log B ∨
    ∃ g, IsBoxAuxiliary f g B ∧ g.totalDegree ≤ f.totalDegree := by
  classical
  let d := f.totalDegree
  let F := scaledHomogenize d 1 f
  have hFhom : F.IsHomogeneous d := scaledHomogenize_homogeneous 1 f le_rfl
  have hF0 : F ≠ 0 := scaledHomogenize_ne_zero d one_ne_zero hf0
  let S := (integerBox n B).filter fun x => eval x f = 0
  let e := (Fintype.equivFin S).symm
  let z : Fin (Fintype.card S) → IntPoint (n + 1) := fun i => Fin.cons 1 (e i).val
  have hz (i) : eval (z i) F = 0 := by
    rw [scaledHomogenize_eval 1 f le_rfl, (Finset.mem_filter.mp (e i).property).2, mul_zero]
  have hbox (i) : InBox (z i) B := Fin.cases (by simpa [z] using hB)
    (mem_integerBox.mp (Finset.mem_filter.mp (e i).property).1)
  by_cases hrel : ∀ G : MvPolynomial (Fin (n + 1)) ℤ, G.IsHomogeneous d →
      (∀ i, eval (z i) G = 0) → F ∣ G
  · left
    simpa only [F, integerCoefficientHeight_scaledHomogenize_one] using
      homogeneous_no_auxiliary_coefficient_height F hFhom hF0 z hz hB hbox hrel
  · right
    push Not at hrel
    obtain ⟨G, hGhom, hGz, hGnd⟩ := hrel
    let g := homogeneousSlice n 1 G
    have hslice : homogeneousSlice n 1 F = f := by
      simp [F, d, homogeneousSlice_scaledHomogenize 1 f le_rfl]
    have hFprim : PrimitiveIntegerPolynomial F := fun c hc =>
      hprim c fun m => by simpa [F, scaledHomogenize_coefficient] using hc (homogenizedExponent d m)
    have hndQ := rational_homogeneousSlice_not_dvd one_ne_zero hFhom hF0 hGhom hFprim
      (by rw [hslice]) hGnd
    rw [hslice] at hndQ
    have hgnd : ¬ f ∣ g := fun h => hndQ (map_dvd (map (Int.castRingHom ℚ)) h)
    refine ⟨g, ⟨fun h => hgnd (h ▸ dvd_zero _), hgnd, fun x hx hxf => ?_⟩,
      homogeneousSlice_degree_le 1 hGhom⟩
    obtain ⟨i, hi⟩ := e.surjective ⟨x, Finset.mem_filter.mpr ⟨mem_integerBox.mpr hx, hxf⟩⟩
    have hh : eval (Fin.cons 1 (e i).val) G = 0 := hGz i
    rw [hi] at hh
    simpa only [g, homogeneousSlice_eval] using hh

end
end CCDN
