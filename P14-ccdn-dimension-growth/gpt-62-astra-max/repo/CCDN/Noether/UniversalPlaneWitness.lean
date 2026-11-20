/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.AffineLineLeading
public import CCDN.Algebra.CharZeroOrGT
public import CCDN.Noether.UniversalPlane
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CCDN.Determinant.ClosedFormIntegerMinor
import CCDN.Determinant.UniversalPlaneMinor
import CCDN.ForMathlib.MvPolynomial
import CCDN.Noether.ClosedFormParameterDegree
import CCDN.Noether.ShearNormalization

/-!
A nonzero universal minor of cubic parameter degree, over the original coefficient field; the
nonvanishing proof descends from an algebraic closure. The leading coefficient of a universal
plane section, evaluated by the highest homogeneous form in the first direction, detects loss of
the full outer degree.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

section

variable {K L σ : Type*} [CommRing K] [CommRing L] (φ : K →+* L) (f : MvPolynomial σ K)

private lemma universalPlaneMap_map :
    universalPlaneMap L σ (MvPolynomial.map φ f) =
      MvPolynomial.map (MvPolynomial.map φ) (universalPlaneMap K σ f) := by
  have he : (universalPlaneMap L σ).toRingHom.comp (MvPolynomial.map φ) =
      (MvPolynomial.map (MvPolynomial.map φ)).comp (universalPlaneMap K σ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    simp
    · simp [universalPlaneMap]
  exact RingHom.congr_fun he f

/-- The universal plane restriction commutes with applying a coefficient ring homomorphism. -/
lemma universalPlanePolynomial_map :
    universalPlanePolynomial (MvPolynomial.map φ f) =
      bivariateMap (MvPolynomial.map φ) (universalPlanePolynomial f) := by
  simp [universalPlanePolynomial, universalPlaneMap_map, bivariatePolynomialEquiv_map]

end

/-- A geometrically irreducible equation yields a nonzero polynomial
in the full affine-plane parameter ring, of degree at most (2*d^2-1)*d.
There are no smoothness or positioning hypotheses on the input equation. -/
theorem exists_universalPlane_minor_degree
    {K σ : Type*} [Field K] [Fintype σ]
    (f : MvPolynomial (Option σ) K)
    (hf : Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpos : 0 < f.totalDegree) (hchar : CharZeroOrGT K (2 * f.totalDegree ^ 2)) :
    ∃ (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
      (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree),
      ((closedFormCoefficientMatrix f.totalDegree
        (universalPlanePolynomial f)).submatrix rows cols).det ≠ 0 ∧
      (((closedFormCoefficientMatrix f.totalDegree
        (universalPlanePolynomial f)).submatrix rows cols).det).totalDegree ≤
          (2 * f.totalDegree ^ 2 - 1) * f.totalDegree := by
  let φ := algebraMap K (AlgebraicClosure K)
  have ht : (MvPolynomial.map φ f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective φ.injective _
  have hex := exists_universalPlane_minor
    _ hf (ht ▸ hpos) (ht ▸ hchar.map φ)
  rw [ht] at hex
  obtain ⟨rows, cols, hdet⟩ := hex
  refine ⟨rows, cols, ?_, ?_⟩
  · intro he
    rw [universalPlanePolynomial_map, ← closedForm_minor_map, he, map_zero] at hdet
    exact hdet rfl
  solve_by_elim [closedForm_minor_parameterDegree, universalPlanePolynomial_coefficient_degree]

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

section

variable {K σ : Type*} [CommRing K] (a b c : σ → K) (f : MvPolynomial σ K)

private lemma universalPlanePolynomial_specialize_axis :
    Polynomial.map (Polynomial.evalRingHom 0)
      (bivariateMap (planeParameterEval (RingHom.id K) a b c) (universalPlanePolynomial f)) =
      affineLinePolynomial a b f := by
  rw [universalPlanePolynomial_specialize]
  have he : (Polynomial.mapRingHom (Polynomial.evalRingHom (0 : K))).comp
      ((bivariatePolynomialEquiv K).toRingHom.comp
        (eval₂Hom (C.comp (RingHom.id K))
          (fun i => C (a i) + C (b i) * X 0 + C (c i) * X 1))) = affineLinePolynomial a b := by
    apply MvPolynomial.ringHom_ext
    · simp [affineLinePolynomial, bivariatePolynomialEquiv_C]
    · simp [affineLinePolynomial, bivariatePolynomialEquiv_C,
        bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one]
  exact RingHom.congr_fun he f

/-- The coefficient of x^d y^0, as a polynomial in all plane parameters. -/
def universalPlaneLeading :
    MvPolynomial (PlaneParameters σ) K :=
  ((universalPlanePolynomial f).coeff f.totalDegree).coeff 0

private lemma universalPlaneLeading_specialize :
    planeParameterEval (RingHom.id K) a b c (universalPlaneLeading f) =
      eval b (homogeneousComponent f.totalDegree f) := by
  have h := congrArg (fun q : Polynomial K => q.coeff f.totalDegree)
    (universalPlanePolynomial_specialize_axis a b c f)
  rw [Polynomial.coeff_map, affineLinePolynomial_top_coefficient a b f _ le_rfl] at h
  change Polynomial.eval 0 _ = _ at h
  rw [← Polynomial.coeff_zero_eq_eval_zero, bivariateMap_coeff] at h
  exact h

end

variable {K L σ : Type*} [Field K]

private lemma universalPlaneLeading_map [Field L]
    (φ : K →+* L) (f : MvPolynomial σ K) :
    universalPlaneLeading (MvPolynomial.map φ f) =
      MvPolynomial.map φ (universalPlaneLeading f) := by
  have ht : (MvPolynomial.map φ f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective φ.injective _
  simp_rw [universalPlaneLeading, ht, universalPlanePolynomial_map, bivariateMap_coeff]

/-- Over an algebraically closed field, irreducibility and the characteristic bound
suffice for the leading polynomial to be nonzero. -/
theorem universalPlaneLeading_ne_zero_of_irreducible [IsAlgClosed K] [Fintype σ]
    (f : MvPolynomial (Option σ) K) (hf : Irreducible f) (hpos : 0 < f.totalDegree)
    (hchar : CharZeroOrGT K f.totalDegree) :
    universalPlaneLeading f ≠ 0 := by
  obtain ⟨a, b, _, hdir, _⟩ := exists_monic_smooth_hypersurface_coordinates f hf hpos hchar
  intro hz
  apply hdir
  rw [← universalPlaneLeading_specialize a b 0, hz, map_zero]

/-- Geometric irreducibility and the characteristic bound suffice for the
leading polynomial to be nonzero. -/
theorem universalPlaneLeading_ne_zero [Fintype σ]
    (f : MvPolynomial (Option σ) K)
    (hf : Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpos : 0 < f.totalDegree) (hchar : CharZeroOrGT K f.totalDegree) :
    universalPlaneLeading f ≠ 0 := by
  let φ := algebraMap K (AlgebraicClosure K)
  have ht : (MvPolynomial.map φ f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective φ.injective _
  have hn := universalPlaneLeading_ne_zero_of_irreducible _ hf (ht ▸ hpos)
    (ht ▸ hchar.map φ)
  rw [universalPlaneLeading_map] at hn
  grind

end
end CCDN
