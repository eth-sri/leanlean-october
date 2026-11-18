module

public import CCDN.Algebra.CharZeroOrGT
public import CCDN.AuxiliaryPolynomial.HypersurfaceAffineCoordinates
public import CCDN.ForMathlib.Matrix
public import CCDN.Noether.GenericPlaneIrreducibility
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CCDN.Algebra.AffineLineLeading
import CCDN.Determinant.GenericPlaneMinor
import CCDN.Determinant.HypersurfaceSmoothPoint
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.PDeriv

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private lemma hypersurfaceAffineCoordinates_top_coefficient {K σ : Type*} [Field K]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K) :
    (optionEquivLeft K σ (hypersurfaceAffineCoordinates a b hb f)).coeff f.totalDegree =
      C (eval b (homogeneousComponent f.totalDegree f)) := by
  have htd := hypersurfaceAffineCoordinates_totalDegree_le a b hb f
  have hconst : (optionEquivLeft K σ (hypersurfaceAffineCoordinates a b hb f)).coeff f.totalDegree =
      C (eval (0 : σ → K)
        ((optionEquivLeft K σ (hypersurfaceAffineCoordinates a b hb f)).coeff f.totalDegree)) := by
    by_cases h : f.totalDegree ≤ (hypersurfaceAffineCoordinates a b hb f).totalDegree
    · have ht := totalDegree_coeff_optionEquivLeft_add_le K σ _ f.totalDegree h
      simpa only [eval_zero, constantCoeff_eq] using
        totalDegree_eq_zero_iff_eq_C.mp (by omega : _ = 0)
    · have hn : (optionEquivLeft K σ (hypersurfaceAffineCoordinates a b hb f)).natDegree <
          f.totalDegree := by
        rw [natDegree_optionEquivLeft]
        exact (degreeOf_le_totalDegree _ none).trans_lt (by omega)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn, map_zero, map_zero]
  rw [hconst]; congr 1
  let φ := (Polynomial.mapRingHom (eval (0 : σ → K))).comp
    ((optionEquivLeft K σ).toRingHom.comp (hypersurfaceAffineCoordinates a b hb).toRingHom)
  have he : φ = affineLinePolynomial a b := MvPolynomial.ringHom_ext
    (fun r => by
      change Polynomial.map _ (optionEquivLeft K σ (hypersurfaceAffineCoordinates a b hb (C r))) = _
      rw [show hypersurfaceAffineCoordinates a b hb (C r) = C r from
        (hypersurfaceAffineCoordinates a b hb).commutes r]
      simp [affineLinePolynomial])
    (fun i => by
      change Polynomial.map _ (optionEquivLeft K σ (hypersurfaceAffineCoordinates a b hb (X i))) = _
      rw [hypersurfaceAffineCoordinates_X]; cases i <;> simp [affineLinePolynomial])
  have h : (Polynomial.map (eval (0 : σ → K))
      (optionEquivLeft K σ (hypersurfaceAffineCoordinates a b hb f))).coeff f.totalDegree =
      (affineLinePolynomial a b f).coeff f.totalDegree :=
    congrArg (fun q : Polynomial K => q.coeff f.totalDegree) (RingHom.congr_fun he f)
  rwa [Polynomial.coeff_map, affineLinePolynomial_top_coefficient a b f _ le_rfl] at h

private lemma hypersurfaceAffineCoordinates_full_outer_degree {K σ : Type*} [Field K]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K)
    (hdir : eval b (homogeneousComponent f.totalDegree f) ≠ 0) :
    (optionEquivLeft K σ (hypersurfaceAffineCoordinates a b hb f)).natDegree = f.totalDegree := by
  refine le_antisymm ?_ (Polynomial.le_natDegree_of_ne_zero ?_)
  · rw [natDegree_optionEquivLeft]
    exact (degreeOf_le_totalDegree _ none).trans (hypersurfaceAffineCoordinates_totalDegree_le a b hb f)
  · rw [hypersurfaceAffineCoordinates_top_coefficient]
    exact (map_ne_zero_iff _ (C_injective σ K)).mpr hdir

def normalizedHypersurfaceCoordinates {K σ : Type*} [Field K]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K) :
    MvPolynomial (Option σ) K :=
  C (eval b (homogeneousComponent f.totalDegree f))⁻¹ * hypersurfaceAffineCoordinates a b hb f

lemma normalizedHypersurfaceCoordinates_monic {K σ : Type*} [Field K]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K)
    (hdir : eval b (homogeneousComponent f.totalDegree f) ≠ 0) :
    (optionEquivLeft K σ (normalizedHypersurfaceCoordinates a b hb f)).Monic := by
  unfold normalizedHypersurfaceCoordinates
  rw [map_mul, optionEquivLeft_C]
  apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [Polynomial.leadingCoeff, hypersurfaceAffineCoordinates_full_outer_degree a b hb f hdir,
    hypersurfaceAffineCoordinates_top_coefficient, ← map_mul, inv_mul_cancel₀ hdir, map_one]

theorem exists_positioned_genericPlane_minor
    {K σ : Type*} [Field K] [IsAlgClosed K] [Fintype σ]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hpos : 0 < f.totalDegree) (hchar : CharZeroOrGT K (2 * f.totalDegree ^ 2)) :
    ∃ (a b : Option σ → K) (hb : b none ≠ 0),
      eval b (homogeneousComponent f.totalDegree f) ≠ 0 ∧
      (closedFormCoefficientMatrix f.totalDegree
        (genericPlanePolynomial (normalizedHypersurfaceCoordinates a b hb f))).HasNonzeroMinor
          (2 * f.totalDegree ^ 2 - 1) := by
  classical
  obtain ⟨a, j, ha, hj⟩ := exists_smooth_hypersurface_point_of_degree_lt_char f hf hpos
    (hchar.mono (by nlinarith [Nat.le_mul_self f.totalDegree]))
  let H := homogeneousComponent f.totalDegree f
  let T : MvPolynomial (Option σ) K := ∑ i, C (eval a (pderiv i f)) * X i
  have hT : T ≠ 0 := fun h => hj <| by
    have hc := congrArg (fun g : MvPolynomial (Option σ) K => g.coeff (Finsupp.single j 1)) h
    cases j <;> simpa [T, coeff_C_mul, coeff_X, Finsupp.single_eq_single_iff] using hc
  have hprod : H * T * X none ≠ 0 :=
    mul_ne_zero (mul_ne_zero (homogeneousComponent_totalDegree_ne_zero hf.ne_zero) hT)
      (X_ne_zero none)
  have hhom : (H * T * X none).IsHomogeneous (f.totalDegree + 1 + 1) :=
    ((homogeneousComponent_isHomogeneous _ _).mul
      (IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X _ i)).mul (isHomogeneous_X K none)
  obtain ⟨b, hbprod⟩ : ∃ b : Option σ → K, eval b (H * T * X none) ≠ 0 := by
    by_contra! hn; exact hprod (hhom.eq_zero_of_forall_eval_eq_zero hn)
  rw [map_mul, map_mul, eval_X] at hbprod
  have hb : b none ≠ 0 := right_ne_zero_of_mul hbprod
  have hdir : eval b H ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hbprod)
  have ht : (∑ i, eval a (pderiv i f) * b i) ≠ 0 := by
    simpa [T] using right_ne_zero_of_mul (left_ne_zero_of_mul hbprod)
  have hu : IsUnit (C (eval b H)⁻¹ : MvPolynomial (Option σ) K) :=
    (isUnit_iff_ne_zero.mpr (inv_ne_zero hdir)).map C
  refine ⟨a, b, hb, hdir, exists_genericPlane_minor f.totalDegree hpos _ ?_
    (normalizedHypersurfaceCoordinates_monic a b hb f hdir) ?_ ?_ hchar ?_ ?_⟩
  · exact (irreducible_isUnit_mul hu).mpr
      ((MulEquiv.irreducible_iff (f := hypersurfaceAffineCoordinates a b hb)).mpr hf)
  · unfold normalizedHypersurfaceCoordinates
    rw [map_mul, optionEquivLeft_C,
      Polynomial.natDegree_C_mul_of_isUnit ((isUnit_iff_ne_zero.mpr (inv_ne_zero hdir)).map C)]
    exact hypersurfaceAffineCoordinates_full_outer_degree a b hb f hdir
  · exact (totalDegree_mul _ _).trans
      (by rw [totalDegree_C, zero_add]; exact hypersurfaceAffineCoordinates_totalDegree_le a b hb f)
  · rw [normalizedHypersurfaceCoordinates, map_mul, hypersurfaceAffineCoordinates_eval_zero, ha,
      mul_zero]
  · rw [normalizedHypersurfaceCoordinates, pderiv_C_mul, map_mul, eval_C,
      hypersurfaceAffineCoordinates_partial_zero]
    exact mul_ne_zero (inv_ne_zero hdir) ht

end
end CCDN
