/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.ForMathlib.IntegerPolynomialL1
import CCDN.ForMathlib.Matrix
import CCDN.Noether.AmbientNoetherForms
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CCDN.Determinant.GenericPlaneEulerMinorCharZero
import CCDN.Determinant.UniversalPlaneMinor
import CCDN.Noether.AmbientNoetherHeight
import CCDN.Noether.AmbientNoetherVanishing
import CCDN.Noether.EulerPairSpecialization
import Mathlib.Data.Sym.Card

/-!
A finite family of universal integer Noether forms, with the exact
degree and coefficient bound of CCDN Theorem 3.2.2.

Characteristic-zero nonvanishing of the ambient integer
coefficient forms, descended from the algebraic closure.

Every absolutely irreducible characteristic-zero hypersurface of degree
d at least two gives a nonzero Euler minor of order d²−1 in the universal
affine-plane parameter ring.
-/

namespace CCDN
noncomputable section
open MvPolynomial

section
variable {R : Type*} [CommRing R] (u : R)

lemma eulerClosedFormCoefficientMatrix_smul
    (k : ℕ) (f : Polynomial (Polynomial R)) :
    eulerClosedFormCoefficientMatrix k (u • f) = u • eulerClosedFormCoefficientMatrix k f := by
  ext row col
  change eulerCoefficientEntryLinear k row col (u • f) =
    u • eulerCoefficientEntryLinear k row col f
  exact map_smul _ _ _

lemma eulerClosedForm_minor_smul
    (k r : ℕ) (f : Polynomial (Polynomial R))
    (a : Fin r → ℕ × ℕ) (c : Fin r → EulerColumns k) :
    ((eulerClosedFormCoefficientMatrix k (u • f)).submatrix a c).det =
      u ^ r * ((eulerClosedFormCoefficientMatrix k f).submatrix a c).det := by
  rw [eulerClosedFormCoefficientMatrix_smul]
  change (u • (eulerClosedFormCoefficientMatrix k f).submatrix a c).det = _
  rw [Matrix.det_smul, Fintype.card_fin]

end

/-- The universal affine-plane family has a nonzero determinant of
the precise Noether order. -/
theorem exists_universalPlane_euler_minor_charZero
    {K σ : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Fintype σ]
    (k : ℕ) (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hd : f.totalDegree = k + 2) :
    (eulerClosedFormCoefficientMatrix k (universalPlanePolynomial f)).HasNonzeroMinor
      ((k + 2) ^ 2 - 1) := by
  obtain ⟨a, b, hb, rows, cols, hdet⟩ : ∃ (a b : Option σ → K) (hb : b none ≠ 0),
      (eulerClosedFormCoefficientMatrix k
        (genericPlanePolynomial (normalizedHypersurfaceCoordinates a b hb f))).HasNonzeroMinor
          ((k + 2) ^ 2 - 1) := by
    obtain ⟨a, b, hb, -, hg⟩ :=
      exists_monic_smooth_hypersurface_coordinates f hf (by omega) (.of_charZero _)
    exact ⟨a, b, hb, exists_genericPlane_euler_minor_charZero k _ hg.irreducible hg.monic
      (hd ▸ hg.natDegree_eq) hg.eval_zero hg.pderiv_ne_zero⟩
  let R := MvPolynomial σ K
  let F := FractionRing R
  let φ : R →+* F := algebraMap R F
  have hne :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hdet
  rw [eulerClosedForm_minor_map, normalized_genericPlane_universal_specialization,
    eulerClosedForm_minor_smul, ← eulerClosedForm_minor_map] at hne
  refine ⟨rows, cols, ?_⟩
  intro he
  exact hne (by simp_all)

section
variable (σ : Type*) [Fintype σ] [DecidableEq σ]

lemma finite_homogeneous_coefficientL1_bounded
    (r H : ℕ) :
    {f : MvPolynomial σ ℤ | f.IsHomogeneous r ∧ l1Norm f ≤ H}.Finite := by
  let C := ↥(Finset.Icc (-(H : ℤ)) H)
  let F : (Sym σ r → C) → MvPolynomial σ ℤ :=
    fun c => ∑ i, monomial (homogeneousCoefficientExponent σ r i) (c i).val
  apply (Set.finite_range F).subset
  intro f hf
  let c : Sym σ r → C := fun i => ⟨f.coeff (homogeneousCoefficientExponent σ r i), by
    have hh := (show (f.coeff (homogeneousCoefficientExponent σ r i)).natAbs ≤ l1Norm f by
        by_cases hm : (homogeneousCoefficientExponent σ r i) ∈ f.support
        · exact Finset.single_le_sum (fun j _ => Nat.zero_le (f.coeff j).natAbs) hm
        · grind).trans hf.2
    grind⟩
  refine ⟨c, ?_⟩
  exact homogeneousCoefficientData_reconstruct r f hf.1

/-- The finite collection of universal Noether forms of degree `k + 2` in the variables `σ`: the
extracted plane-parameter coefficients of all Euler minors of the universal plane restriction of
the universal homogeneous form. -/
def universalNoetherForms (k : ℕ) :
    Finset (MvPolynomial (Sym σ (k + 2)) ℤ) :=
  (show {f | ∃ rows cols m, f = ambientNoetherForm σ k rows cols m}.Finite by
      apply (finite_homogeneous_coefficientL1_bounded (Sym σ (k + 2))
        ((k + 2) ^ 2 - 1)
        ((k + 2) ^ (3 * (k + 2) ^ 2 - 3) *
          (Fintype.card (Sym σ (k + 2)) * 3 ^ (k + 2)) ^ ((k + 2) ^ 2 - 1))).subset
      rintro f ⟨rows,cols,m,rfl⟩
      exact ⟨ambientNoetherForm_homogeneous σ k rows cols m,
        (l1Norm_coeff_le_l1Norm_sumAlgEquiv_symm _ _).trans (show l1Norm ((sumAlgEquiv ℤ (PlaneParameters σ) (Sym σ (k + 2))).symm
              (ambientNoetherParameterMinor σ k rows cols)) ≤
              (k + 2) ^ (3 * (k + 2) ^ 2 - 3) *
                (Fintype.card (Sym σ (k + 2)) * 3 ^ (k + 2)) ^ ((k + 2) ^ 2 - 1) by
            let r := (k + 2) ^ 2 - 1
            let N := Fintype.card (Sym σ (k + 2))
            let φ := (sumAlgEquiv ℤ (PlaneParameters σ) (Sym σ (k + 2))).symm.toRingHom
            change l1Norm (φ
              (((eulerClosedFormCoefficientMatrix k
                (universalPlanePolynomial (universalHomogeneousForm σ (k + 2))))).submatrix
                  rows cols).det) ≤ _
            rw [RingHom.map_det]
            have hdet := l1Norm_det_le _ (N * ((k + 2) * 3 ^ (k + 2)))
              (fun i j => ambientEulerEntry_flatten_l1_le σ k (rows i) (cols j))
            rw [Fintype.card_fin] at hdet
            apply hdet.trans
            have he : 3 * r = 3 * (k + 2) ^ 2 - 3 := by grind
            calc
              r.factorial * (N * ((k + 2) * 3 ^ (k + 2))) ^ r =
                  (r.factorial * (k + 2) ^ r) * (N * 3 ^ (k + 2)) ^ r := by
                rw [show N * ((k + 2) * 3 ^ (k + 2)) = (k + 2) * (N * 3 ^ (k + 2)) by ring,
                  mul_pow]
                ring
              _ ≤ (k + 2) ^ (3 * r) * (N * 3 ^ (k + 2)) ^ r :=
                Nat.mul_le_mul_right _ (factorial_mul_degree_pow_le (k + 2) r (by grind))
              _ = _ := by grind)⟩).toFinset

end

section
variable {σ : Type*} [Fintype σ] [DecidableEq σ] (k : ℕ)

lemma mem_universalNoetherForms
    (f : MvPolynomial (Sym σ (k + 2)) ℤ) :
    f ∈ universalNoetherForms σ k ↔ ∃ rows cols m, f = ambientNoetherForm σ k rows cols m := by
  exact Set.Finite.mem_toFinset _

/-- Every universal Noether form is homogeneous of degree `(k + 2) ^ 2 - 1`. -/
theorem universalNoetherForms_homogeneous
    (g : MvPolynomial (Sym σ (k + 2)) ℤ)
    (hg : g ∈ universalNoetherForms σ k) :
    g.IsHomogeneous ((k + 2) ^ 2 - 1) := by
  obtain ⟨rows,cols,m,rfl⟩ := (mem_universalNoetherForms k g).mp hg
  exact ambientNoetherForm_homogeneous σ k rows cols m

end

variable {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ] (k : ℕ)

/-- In characteristic zero, an absolutely irreducible homogeneous equation of degree `k + 2`
makes at least one universal Noether form nonzero. -/
theorem universalNoetherForms_nonvanishing [CharZero K]
    (f : MvPolynomial (Option σ) K) (hf : f.IsHomogeneous (k + 2))
    (hir : Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f)) :
    ∃ g ∈ universalNoetherForms (Option σ) k,
      homogeneousCoefficientSpecialization (k + 2) f g ≠ 0 := by
  let φ := algebraMap K (AlgebraicClosure K)
  obtain ⟨rows, cols, hdet⟩ := exists_universalPlane_euler_minor_charZero
    k (MvPolynomial.map φ f) hir ((hf.map φ).totalDegree hir.ne_zero)
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hdet
  refine ⟨_, (mem_universalNoetherForms _ _).mpr ⟨rows, cols, m, rfl⟩, fun hz => hm ?_⟩
  rw [universalPlanePolynomial_map, ← eulerClosedForm_minor_map, coeff_map,
    ← ambientNoetherForm_specialize k f hf rows cols m, hz, map_zero]

