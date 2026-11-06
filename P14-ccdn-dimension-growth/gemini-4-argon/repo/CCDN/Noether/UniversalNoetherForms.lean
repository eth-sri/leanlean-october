/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ForMathlib.IntegerPolynomialL1
public import CCDN.ForMathlib.Matrix
public import CCDN.Noether.AmbientNoetherForms
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
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

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- For fixed `σ` and `k`, there are only finitely many ambient Noether forms. -/
lemma finite_ambientNoetherForms (σ : Type*) [Fintype σ] [DecidableEq σ] (k : ℕ) :
    {f | ∃ rows cols m, f = ambientNoetherForm σ k rows cols m}.Finite := by
  classical
  let r := (k + 2) ^ 2 - 1
  let H := (k + 2) ^ (3 * (k + 2) ^ 2 - 3) * (Fintype.card (Sym σ (k + 2)) * 3 ^ (k + 2)) ^ r
  let C := ↥(Finset.Icc (-(H : ℤ)) (H : ℤ))
  let F : (Sym (Sym σ (k + 2)) r → C) → MvPolynomial (Sym σ (k + 2)) ℤ :=
    fun c => ∑ i, monomial (homogeneousCoefficientExponent (Sym σ (k + 2)) r i) (c i).val
  apply (Set.finite_range F).subset
  rintro f ⟨rows, cols, m, rfl⟩
  have hf := ambientNoetherForm_homogeneous σ k rows cols m
  have hl1 := ambientNoetherForm_coefficientL1_le σ k rows cols m
  refine ⟨fun i => ⟨_, Finset.mem_Icc.mpr (abs_le.mp ?_)⟩,
    homogeneousCoefficientData_reconstruct r _ hf⟩
  rw [← Int.natCast_natAbs]
  exact_mod_cast (natAbs_coeff_le_l1Norm _ _).trans hl1

/-- The finite collection of universal Noether forms of degree `k + 2` in the variables `σ`: the
extracted plane-parameter coefficients of all Euler minors of the universal plane restriction of
the universal homogeneous form. -/
def universalNoetherForms (σ : Type*) [Fintype σ] [DecidableEq σ] (k : ℕ) :
    Finset (MvPolynomial (Sym σ (k + 2)) ℤ) :=
  (finite_ambientNoetherForms σ k).toFinset

/-- Every universal Noether form is homogeneous of degree `(k + 2) ^ 2 - 1`. -/
theorem universalNoetherForms_homogeneous {σ : Type*} [Fintype σ] [DecidableEq σ]
    (k : ℕ) (g : MvPolynomial (Sym σ (k + 2)) ℤ)
    (hg : g ∈ universalNoetherForms σ k) :
    g.IsHomogeneous ((k + 2) ^ 2 - 1) := by
  obtain ⟨rows, cols, m, rfl⟩ := (Set.Finite.mem_toFinset _).mp hg
  exact ambientNoetherForm_homogeneous σ k rows cols m

/-- Every universal Noether form vanishes on a geometrically reducible homogeneous equation of
degree `k + 2`, over an arbitrary field, with no characteristic assumption. -/
theorem universalNoetherForms_vanish {K σ : Type*} [Field K]
    [Fintype σ] [DecidableEq σ]
    (k : ℕ) (f : MvPolynomial σ K) (hf : f.IsHomogeneous (k + 2))
    (hred : ¬Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (g : MvPolynomial (Sym σ (k + 2)) ℤ)
    (hg : g ∈ universalNoetherForms σ k) :
    homogeneousCoefficientSpecialization (k + 2) f g = 0 := by
  obtain ⟨rows, cols, m, rfl⟩ := (Set.Finite.mem_toFinset _).mp hg
  exact ambientNoetherForm_eq_zero_of_not_absolutely_irreducible k f hf hred rows cols m

/-- In characteristic zero, an absolutely irreducible homogeneous equation of degree `k + 2`
makes at least one universal Noether form nonzero. -/
theorem universalNoetherForms_nonvanishing {K σ : Type*} [Field K] [CharZero K]
    [Fintype σ] [DecidableEq σ]
    (k : ℕ) (f : MvPolynomial (Option σ) K) (hf : f.IsHomogeneous (k + 2))
    (hir : Irreducible (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f)) :
    ∃ g ∈ universalNoetherForms (Option σ) k,
      homogeneousCoefficientSpecialization (k + 2) f g ≠ 0 := by
  let φ := algebraMap K (AlgebraicClosure K)
  let fbar := MvPolynomial.map φ f
  obtain ⟨a, b, hb, _, rows, cols, hdet⟩ :=
    exists_positioned_genericPlane_euler_minor_charZero k fbar hir ((hf.map φ).totalDegree hir.ne_zero)
  let R := MvPolynomial σ (AlgebraicClosure K)
  let F := FractionRing R
  have hne : algebraMap R F (((eulerClosedFormCoefficientMatrix k
      (genericPlanePolynomial (normalizedHypersurfaceCoordinates a b hb fbar))).submatrix
        rows cols).det) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hdet
  have hsmul (u : F) (r : ℕ) (P : Polynomial (Polynomial F))
      (ar : Fin r → ℕ × ℕ) (cr : Fin r → EulerColumns k) :
      ((eulerClosedFormCoefficientMatrix k (u • P)).submatrix ar cr).det =
        u ^ r * ((eulerClosedFormCoefficientMatrix k P).submatrix ar cr).det := by
    rw [show eulerClosedFormCoefficientMatrix k (u • P) =
      u • eulerClosedFormCoefficientMatrix k P from
      Matrix.ext fun row col => map_smul (eulerCoefficientEntryLinear k row col) u P]
    change (u • (eulerClosedFormCoefficientMatrix k P).submatrix ar cr).det = _
    rw [Matrix.det_smul, Fintype.card_fin]
  rw [eulerClosedForm_minor_map, normalized_genericPlane_universal_specialization,
    hsmul, ← eulerClosedForm_minor_map] at hne
  have hdet' : ((eulerClosedFormCoefficientMatrix k (universalPlanePolynomial fbar)).submatrix
      rows cols).det ≠ 0 := fun he => hne (by rw [he, map_zero, mul_zero])
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hdet'
  refine ⟨_, (Set.Finite.mem_toFinset _).mpr ⟨rows, cols, m, rfl⟩, fun hz => hm ?_⟩
  rw [← ambientEuler_minor_map φ k f rows cols, coeff_map,
    ← ambientNoetherForm_specialize k f hf rows cols m, hz, map_zero]

end
end CCDN
