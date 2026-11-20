module

public import QPBT.Games.MeasurementMap
public import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities.PositiveGram.Completion
public import QPBT.Games.Sandwich.Support
public import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkCore

/-! # State-dependent Schmidt mirrors

This module constructs the opposite-register mirror used in the one-sided
pasting argument. The auxiliary construction uses the spectral theorem and
orthonormal completion, including zero Schmidt coefficients.

## References

`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`, `lem:pasting`;
`docs/paper-gaps/qpbt_pasting-product-error.tex`, issue Dengnifer/MIPStarRE-QPBT-bak#201. The
Schmidt-mirror
argument is a formalization auxiliary, not an additional paper hypothesis.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum
open MIPStarRE.LDT.MakingMeasurementsProjective

/-- The paired-entry estimate for the Schmidt-mirror construction. For nonnegative
Schmidt coefficients, the squared commutator entry is bounded by the two
intertwining errors. This is a Lean-only auxiliary, not a source assertion.
See the one-sided proof in `docs/paper-gaps/qpbt_pasting-product-error.tex`,
issue Dengnifer/MIPStarRE-QPBT-bak#201. The matrix estimate is proved in this module. -/
theorem schmidt_pair_mirror_estimate (left right : ℝ) (hleft : 0 ≤ left)
    (hright : 0 ≤ right) (entry target : ℂ) :
    (left - right) ^ 2 * Complex.normSq target ≤
      Complex.normSq ((right : ℂ) * entry - (left : ℂ) * target) +
      Complex.normSq ((left : ℂ) * entry - (right : ℂ) * target) := by
  have hidentity :
      Complex.normSq ((right : ℂ) * entry - (left : ℂ) * target) +
        Complex.normSq ((left : ℂ) * entry - (right : ℂ) * target) -
        (left - right) ^ 2 * Complex.normSq target =
      (left - right) ^ 2 * Complex.normSq entry +
        2 * left * right * Complex.normSq (entry - target) := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  have hnonneg : 0 ≤ (left - right) ^ 2 * Complex.normSq entry +
      2 * left * right * Complex.normSq (entry - target) :=
    add_nonneg (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hleft) hright)
        (Complex.normSq_nonneg _))
  linarith

structure SchmidtData {ι : Type*} [Fintype ι] [DecidableEq ι] (coeff : Op ι) where
  left : Matrix.unitaryGroup ι ℂ
  right : Matrix.unitaryGroup ι ℂ
  values : ι → ℝ
  nonneg : ∀ i, 0 ≤ values i
  factorization : coeff = (left : Op ι) * Matrix.diagonal (fun i => (values i : ℂ)) *
    (right : Op ι)ᴴ

section

variable {ι : Type*} [Fintype ι]
include ι

/-- Complete the positive singular directions to Schmidt coordinates, leaving
zero singular values in the diagonal. -/
noncomputable def schmidtData [DecidableEq ι]
    (coeff : Op ι) : SchmidtData coeff := by
  classical
  let gram := coeffᴴ * coeff
  let hermitian := Matrix.isHermitian_conjTranspose_mul_self coeff
  let completion := exists_unitaryGroup_with_positive_gram_spectrum_rows
    coeff gram hermitian rfl (Function.Embedding.subtype _)
  let rows := Classical.choose completion
  have hrows := Classical.choose_spec completion
  have htranspose : (rows : Op ι)ᵀ * ((rows : Op ι)ᵀ)ᴴ = 1 := by
    rw [show ((rows : Op ι)ᵀ)ᴴ = ((rows : Op ι)ᴴ)ᵀ from rfl,
      ← Matrix.transpose_mul,
      show (rows : Op ι)ᴴ * (rows : Op ι) = 1 from Unitary.coe_star_mul_self rows,
      Matrix.transpose_one]
  let left : Matrix.unitaryGroup ι ℂ :=
    ⟨(rows : Op ι)ᵀ, Matrix.mem_unitaryGroup_iff.mpr htranspose⟩
  let right := hermitian.eigenvectorUnitary
  let values := fun index => Real.sqrt (hermitian.eigenvalues index)
  have hcolumns : coeff * (right : Op ι) =
      (left : Op ι) * Matrix.diagonal (fun index => (values index : ℂ)) := by
    ext row col
    rw [Matrix.mul_diagonal]
    have himage : (coeff * (right : Op ι)) row col =
        (Matrix.toEuclideanLin coeff (hermitian.eigenvectorBasis col)) row := by
      simp [Matrix.mul_apply, right, Matrix.IsHermitian.eigenvectorUnitary_apply,
        Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
    rw [himage]
    by_cases hpositive : 0 < hermitian.eigenvalues col
    · have hrow := hrows ⟨col, hpositive⟩ row
      have hvalue : (values col : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr hpositive).ne'
      change (rows : Op ι) col row =
        ((1 / values col : ℝ) : ℂ) *
          (Matrix.toEuclideanLin coeff (hermitian.eigenvectorBasis col)) row at hrow
      change _ = (rows : Op ι) col row * (values col : ℂ)
      rw [hrow]
      push_cast
      field_simp
    · have hzero :=
        matrix_image_eq_zero_of_nonpositive_gram_eigenvalue
          coeff gram hermitian (Matrix.posSemidef_conjTranspose_mul_self coeff) rfl col hpositive
      have hvalue : values col = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hpositive)
      rw [hzero, hvalue]
      simp
  refine ⟨left, right, values, fun index => Real.sqrt_nonneg _, ?_⟩
  calc
    coeff = coeff * (right : Op ι) * (right : Op ι)ᴴ := by
      rw [Matrix.mul_assoc,
        show (right : Op ι) * (right : Op ι)ᴴ = 1 from Unitary.coe_mul_star_self right,
        Matrix.mul_one]
    _ = _ := by rw [hcolumns]

private noncomputable def entryMass (coeff : Op ι) : ℝ :=
  ∑ row, ∑ col, Complex.normSq (coeff row col)

section

variable [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (A : Op ι)
include U A

private theorem unitary_cancel : (U : Op ι) * ((U : Op ι)ᴴ * A) = A := by
  have h : (U : Op ι) * (U : Op ι)ᴴ = 1 := Unitary.coe_mul_star_self U
  rw [← mul_assoc, h, one_mul]

private theorem unitary_cancel_adjoint : (U : Op ι)ᴴ * ((U : Op ι) * A) = A := by
  simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    using unitary_cancel (star U) A

end

/-- Summing the paired-entry estimate gives the Schmidt commutator bound in
diagonal coordinates. The coefficients may vanish and neither Hermitian
operator is required to be projective. -/
private theorem schmidt_diagonal_mirror_estimate [DecidableEq ι]
    (values : ι → ℝ) (hvalues : ∀ index, 0 ≤ values index)
    (alice bob : Op ι) (halice : alice.IsHermitian) (hbob : bob.IsHermitian) :
    entryMass (bob * Matrix.diagonal (fun i => (values i : ℂ)) -
      Matrix.diagonal (fun i => (values i : ℂ)) * bob) ≤
      2 * entryMass (alice * Matrix.diagonal (fun i => (values i : ℂ)) -
        Matrix.diagonal (fun i => (values i : ℂ)) * bob) := by
  have hpoint (row col : ι) :
      Complex.normSq (bob row col * (values col : ℂ) - (values row : ℂ) * bob row col) ≤
        Complex.normSq (alice row col * (values col : ℂ) -
          (values row : ℂ) * bob row col) +
        Complex.normSq (alice col row * (values row : ℂ) -
          (values col : ℂ) * bob col row) := by
    have hpair := schmidt_pair_mirror_estimate (values row) (values col)
      (hvalues row) (hvalues col) (alice row col) (bob row col)
    have hleft : Complex.normSq
        (bob row col * (values col : ℂ) - (values row : ℂ) * bob row col) =
        (values row - values col) ^ 2 * Complex.normSq (bob row col) := by
      simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
      ring
    have hright : Complex.normSq
        (alice col row * (values row : ℂ) - (values col : ℂ) * bob col row) =
        Complex.normSq ((values row : ℂ) * alice row col -
          (values col : ℂ) * bob row col) := by
      rw [← Complex.normSq_conj
        (alice col row * (values row : ℂ) - (values col : ℂ) * bob col row)]
      have ha : (starRingEnd ℂ) (alice col row) = alice row col := halice.apply row col
      have hb : (starRingEnd ℂ) (bob col row) = bob row col := hbob.apply row col
      simp only [map_sub, map_mul, Complex.conj_ofReal, ha, hb, mul_comm]
    rw [hleft, hright]
    simpa only [mul_comm] using hpair
  simp only [entryMass, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hsum := Finset.sum_le_sum fun row (_ : row ∈ (Finset.univ : Finset ι)) =>
    Finset.sum_le_sum fun col (_ : col ∈ (Finset.univ : Finset ι)) => hpoint row col
  simp only [Finset.sum_add_distrib] at hsum
  conv at hsum =>
    rhs; arg 2; rw [Finset.sum_comm]
  linarith

private theorem schmidt_entry_mass_eq_trace (coeff : Op ι) :
    entryMass coeff = (coeff * coeffᴴ).trace.re := by
  simp [entryMass, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.normSq_apply, Complex.mul_re]

private theorem schmidt_entry_mass_unitary [DecidableEq ι]
    (left right : Matrix.unitaryGroup ι ℂ) (coeff : Op ι) :
    entryMass ((left : Op ι) * coeff * (right : Op ι)ᴴ) = entryMass coeff := by
  rw [schmidt_entry_mass_eq_trace, schmidt_entry_mass_eq_trace]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, unitary_cancel_adjoint]
  rw [← Matrix.mul_assoc coeff, ← Matrix.mul_assoc (left : Op ι), Matrix.trace_mul_cycle]
  simp only [← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self, one_mul]

end

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section

variable (ψ : EuclideanSpace ℂ (ι × ι))
include ψ

/-- The coefficient matrix of a bipartite vector in the fixed computational
bases. This is a representation adapter, not a change of state. -/
def schmidtCoefficientMatrix : Op ι :=
  Matrix.of fun row col => ψ (row, col)

/-- The unitary identifying the transposed Bob coordinates with the Alice
Schmidt coordinates. Zero Schmidt directions use the orthonormal completion. -/
noncomputable def schmidtMirrorUnitary :
    Matrix.unitaryGroup ι ℂ :=
  let s := schmidtData (schmidtCoefficientMatrix ψ)
  s.left * star s.right

/-- The state-dependent opposite-register mirror, a linear map on Bob
operators. It reverses multiplication because it includes a transpose. -/
noncomputable def schmidtMirror : Op ι →ₗ[ℂ] Op ι where
  toFun bob := (schmidtMirrorUnitary ψ : Op ι) * bobᵀ * (schmidtMirrorUnitary ψ : Op ι)ᴴ
  map_add' first second := by simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' scalar bob := by
    simp [Matrix.transpose_smul]

/-- Vectorizing a left/right operator difference gives its coefficient-matrix
intertwining error, with the Hilbert norm rather than the function supremum norm. -/
private theorem schmidt_action_norm_sq (alice bob : Op ι) :
    ‖applyOperatorToState (heteroKron alice 1) ψ -
      applyOperatorToState (heteroKron 1 bob) ψ‖ ^ 2 =
      entryMass (alice * schmidtCoefficientMatrix ψ - schmidtCoefficientMatrix ψ * bobᵀ) := by
  rw [PiLp.norm_sq_eq_of_L2, entryMass]
  simp only [Complex.sq_norm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro col _
  congr 1
  simp [applyOperatorToState, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, heteroKron, Matrix.kronecker,
    Fintype.sum_prod_type, Matrix.mul_apply, schmidtCoefficientMatrix,
    Matrix.one_apply, ite_mul, mul_ite, mul_comm]

/-- Mirrors preserve the identity and therefore completeness of a measurement. -/
theorem schmidtMirror_one :
    schmidtMirror ψ 1 = 1 := by
  change (schmidtMirrorUnitary ψ : Op ι) * (1 : Op ι)ᵀ *
    (schmidtMirrorUnitary ψ : Op ι)ᴴ = 1
  rw [Matrix.transpose_one, Matrix.mul_one]
  exact Unitary.coe_mul_star_self _

/-- Multiplication is reversed by the Schmidt mirror. -/
theorem schmidtMirror_mul (first second : Op ι) :
    schmidtMirror ψ (first * second) = schmidtMirror ψ second * schmidtMirror ψ first := by
  have hunitary : (schmidtMirrorUnitary ψ : Op ι)ᴴ *
      (schmidtMirrorUnitary ψ : Op ι) = 1 := Unitary.coe_star_mul_self _
  change _ * (first * second)ᵀ * _ = (_ * secondᵀ * _) * (_ * firstᵀ * _)
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  grind only

/-- The transpose and unitary conjugation preserve positivity of effects. -/
theorem schmidtMirror_posSemidef (bob : Op ι)
    (hbob : bob.PosSemidef) : (schmidtMirror ψ bob).PosSemidef := by
  have hpositive := hbob.transpose.conjTranspose_mul_mul_same (schmidtMirrorUnitary ψ : Op ι)ᴴ
  simp_all [schmidtMirror, LinearMap.coe_mk, AddHom.coe_mk, Matrix.conjTranspose_conjTranspose]

/-- The state-dependent Schmidt mirror is within twice any Hermitian
opposite-register prediction error, in squared Hilbert norm. This is the
dimension-independent estimate of the one-sided pasting argument in issue
Dengnifer/MIPStarRE-QPBT-bak#201.
Neither the state nor its reduced density operator is assumed faithful. -/
theorem schmidtMirror_norm_sq_le
    (alice bob : Op ι) (halice : alice.IsHermitian) (hbob : bob.IsHermitian) :
    ‖applyOperatorToState (heteroKron (schmidtMirror ψ bob) 1) ψ -
      applyOperatorToState (heteroKron 1 bob) ψ‖ ^ 2 ≤
      2 * ‖applyOperatorToState (heteroKron alice 1) ψ -
        applyOperatorToState (heteroKron 1 bob) ψ‖ ^ 2 := by
  let s := schmidtData (schmidtCoefficientMatrix ψ)
  let D : Op ι := Matrix.diagonal (fun i => (s.values i : ℂ))
  let lift (A : Op ι) := (s.left : Op ι)ᴴ * A * (s.left : Op ι)
  let B := (s.right : Op ι)ᴴ * bobᵀ * (s.right : Op ι)
  have hm : lift (schmidtMirror ψ bob) = B := by
    have hU : (s.left : Op ι)ᴴ * (s.left : Op ι) = 1 := Unitary.coe_star_mul_self _
    dsimp only [s] at hU
    simp [lift, schmidtMirror, schmidtMirrorUnitary, s, B, Matrix.star_eq_conjTranspose,
      Matrix.mul_assoc, unitary_cancel, unitary_cancel_adjoint, hU]
  have hV : (s.right : Op ι) * (s.right : Op ι)ᴴ = 1 := Unitary.coe_mul_star_self _
  have hd (A : Op ι) : A * schmidtCoefficientMatrix ψ - schmidtCoefficientMatrix ψ * bobᵀ =
      (s.left : Op ι) * (lift A * D - D * B) * (s.right : Op ι)ᴴ := by
    conv_lhs => rw [s.factorization]
    simp only [lift, D, B, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, unitary_cancel, hV, mul_one]
  rw [schmidt_action_norm_sq, schmidt_action_norm_sq, hd, hd, hm,
    schmidt_entry_mass_unitary, schmidt_entry_mass_unitary]
  exact schmidt_diagonal_mirror_estimate s.values s.nonneg (lift alice) B
    (Matrix.isHermitian_conjTranspose_mul_mul _ halice)
    (Matrix.isHermitian_conjTranspose_mul_mul _ hbob.transpose)

end

section

variable {α : Type*} [Fintype α]
    (ψ : EuclideanSpace ℂ (ι × ι)) (measurement : Measurement α ι)

/-- Applying the fixed Schmidt mirror to every effect produces an actual
measurement; no normalization or completion of its effects is required. -/
noncomputable def schmidtMirrorMeasurement : Measurement α ι :=
  measurement.mapEffects (schmidtMirror ψ).toAddMonoidHom (schmidtMirror_one ψ)
    (fun {_} h => Matrix.nonneg_iff_posSemidef.mpr
      (schmidtMirror_posSemidef ψ _ (Matrix.nonneg_iff_posSemidef.mp h)))

/-- Mirroring commutes with coarse-graining along any evaluation map. -/
theorem schmidtMirrorMeasurement_postprocess {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (ψ : EuclideanSpace ℂ (ι × ι))
    (measurement : Measurement α ι) (evaluation : α → β) :
    (schmidtMirrorMeasurement ψ measurement).postprocess evaluation =
      schmidtMirrorMeasurement ψ (measurement.postprocess evaluation) :=
  measurement.mapEffects_postprocess (schmidtMirror ψ).toAddMonoidHom _ _ evaluation

/-- A projective measurement has a projective Schmidt mirror. -/
theorem schmidtMirrorMeasurement_isProjective
    (hprojective : MIPStarRE.QPBT.Measurement.IsProjective measurement) :
    MIPStarRE.QPBT.Measurement.IsProjective (schmidtMirrorMeasurement ψ measurement) :=
  MIPStarRE.QPBT.Measurement.mapEffects_isProjective measurement hprojective _ _ _
    (fun A => schmidtMirror_mul ψ A A)

end

end MIPStarRE.QPBT
