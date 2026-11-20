module

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
theorem schmidt_pair_mirror_estimate {left right : ℝ} (hleft : 0 ≤ left)
    (hright : 0 ≤ right) (entry target : ℂ) :
    (left - right) ^ 2 * Complex.normSq target ≤
      Complex.normSq ((right : ℂ) * entry - (left : ℂ) * target) +
      Complex.normSq ((left : ℂ) * entry - (right : ℂ) * target) := by
  have hidentity :
      Complex.normSq (right * entry - left * target) +
        Complex.normSq (left * entry - right * target) -
        (left - right) ^ 2 * Complex.normSq target =
      (left - right) ^ 2 * Complex.normSq entry +
        2 * left * right * Complex.normSq (entry - target) := by
    simp [Complex.normSq_apply]
    ring
  have hnonneg : 0 ≤ (left - right) ^ 2 * Complex.normSq entry +
      2 * left * right * Complex.normSq (entry - target) :=
    add_nonneg (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hleft) hright)
        (Complex.normSq_nonneg _))
  linarith

section

variable {ι : Type*} [Fintype ι]

/-- A square matrix admits Schmidt coordinates, including its zero singular
values. This specializes the existing positive-Gram orthonormal completion
to equal row and column index types; no invertibility is assumed. -/
theorem exists_schmidt_coordinates [DecidableEq ι]
    (coeff : Op ι) :
    ∃ (left right : Matrix.unitaryGroup ι ℂ) (values : ι → ℝ),
      (∀ index, 0 ≤ values index) ∧
      coeff = (left : Op ι) * Matrix.diagonal (fun index => (values index : ℂ)) *
        (right : Op ι)ᴴ := by
  classical
  let gram := coeffᴴ * coeff
  let hermitian := Matrix.isHermitian_conjTranspose_mul_self coeff
  obtain ⟨rows, hrows⟩ :=
    exists_unitaryGroup_with_positive_gram_spectrum_rows
      coeff gram hermitian rfl (Function.Embedding.subtype _)
  have htranspose : rowsᵀ * ((rows : Op ι)ᵀ)ᴴ = 1 := by
    simp [show ((rows : Op ι)ᵀ)ᴴ = ((rows : Op ι)ᴴ)ᵀ from rfl, ← Matrix.transpose_mul, show (rows : Op ι)ᴴ * (rows : Op ι) = 1 from Unitary.coe_star_mul_self rows]
  let left : Matrix.unitaryGroup ι ℂ :=
    ⟨rowsᵀ, Matrix.mem_unitaryGroup_iff.mpr htranspose⟩
  let right := hermitian.eigenvectorUnitary
  let values := fun index => Real.sqrt (hermitian.eigenvalues index)
  have hcolumns : coeff * right =
      left * Matrix.diagonal (fun index => (values index : ℂ)) := by
    ext row col
    simp
    have himage : (coeff * right) row col =
        (Matrix.toEuclideanLin coeff (hermitian.eigenvectorBasis col)) row := by
      simp [Matrix.mul_apply, right, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
    rw [himage]
    by_cases hpositive : 0 < hermitian.eigenvalues col
    · have hrow := hrows ⟨col, hpositive⟩ row
      have hvalue : (values col) ≠ 0 := by
        positivity
      change rows col row =
        (1 / values col : ℝ) *
          (Matrix.toEuclideanLin coeff (hermitian.eigenvectorBasis col)) row at hrow
      change _ = rows col row * (values col)
      rw [hrow]
      push_cast
      field_simp
    · have hvalue : values col = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hpositive)
      rw [(matrix_image_eq_zero_of_nonpositive_gram_eigenvalue
          coeff gram hermitian (Matrix.posSemidef_conjTranspose_mul_self coeff) rfl col hpositive), hvalue]
      simp
  refine ⟨left, right, values, fun index => Real.sqrt_nonneg _, ?_⟩
  calc
    coeff = coeff * right * (right : Op ι)ᴴ := by
      simp [Matrix.mul_assoc, show (right : Op ι) * (right : Op ι)ᴴ = 1 from Unitary.coe_mul_star_self right]
    _ = _ := by rw [hcolumns]

/-- Summing the paired-entry estimate gives the Schmidt commutator bound in
diagonal coordinates. The coefficients may vanish and neither Hermitian
operator is required to be projective. -/
theorem schmidt_diagonal_mirror_estimate [DecidableEq ι]
    (values : ι → ℝ) (hvalues : ∀ index, 0 ≤ values index)
    (alice bob : Op ι) (halice : alice.IsHermitian) (hbob : bob.IsHermitian) :
    (∑ row, ∑ col, Complex.normSq
      ((bob * Matrix.diagonal (fun index => (values index : ℂ)) -
        Matrix.diagonal (fun index => (values index : ℂ)) * bob) row col)) ≤
      2 * ∑ row, ∑ col, Complex.normSq
        ((alice * Matrix.diagonal (fun index => (values index : ℂ)) -
          Matrix.diagonal (fun index => (values index : ℂ)) * bob) row col) := by
  have hpoint (row col : ι) :
      Complex.normSq (bob row col * (values col) - (values row) * bob row col) ≤
        Complex.normSq (alice row col * (values col) -
          (values row) * bob row col) +
        Complex.normSq (alice col row * (values row) -
          (values col) * bob col row) := by
    have hleft : Complex.normSq
        (bob row col * (values col) - (values row) * bob row col) =
        (values row - values col) ^ 2 * Complex.normSq (bob row col) := by
      simp [Complex.normSq_apply]
      ring
    have hright : Complex.normSq
        (alice col row * (values row) - (values col) * bob col row) =
        Complex.normSq ((values row) * alice row col -
          (values col) * bob row col) := by
      rw [← Complex.normSq_conj]
      have ha : (starRingEnd ℂ) _ = alice row col := halice.apply row col
      have hb : (starRingEnd ℂ) _ = bob row col := hbob.apply row col
      simp [map_mul, Complex.conj_ofReal, ha, hb, mul_comm]
    simp [*]
    simpa only [mul_comm] using (schmidt_pair_mirror_estimate
      (hvalues row) (hvalues col) (alice row col) (bob row col))
  simp
  have hsum := Finset.sum_le_sum fun row (_ : row ∈ Finset.univ) =>
    Finset.sum_le_sum fun col (_ : col ∈ Finset.univ) => hpoint row col
  simp only [Finset.sum_add_distrib] at hsum
  have hswap : (∑ row : ι, ∑ col : ι, Complex.normSq
      (alice col row * (values row) - (values col) * bob col row)) =
      ∑ row : ι, ∑ col : ι, Complex.normSq
        (alice row col * (values col) - (values row) * bob row col) :=
    Finset.sum_comm
  linarith

private theorem schmidt_entry_mass_eq_trace (coeff : Op ι) :
    (∑ row, ∑ col, Complex.normSq (coeff row col)) = (coeff * coeffᴴ).trace.re := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.normSq_apply, Complex.mul_re]

private theorem schmidt_entry_mass_unitary [DecidableEq ι]
    (left right : Matrix.unitaryGroup ι ℂ) (coeff : Op ι) :
    (∑ row, ∑ col, Complex.normSq (((left : Op ι) * coeff * (right : Op ι)ᴴ) row col)) =
      ∑ row, ∑ col, Complex.normSq (coeff row col) := by
  rw [schmidt_entry_mass_eq_trace, schmidt_entry_mass_eq_trace]
  have hright : rightᴴ * (right : Op ι) = 1 := Unitary.coe_star_mul_self right
  have hleft : leftᴴ * (left : Op ι) = 1 := Unitary.coe_star_mul_self left
  have hprod : (left * coeff * (right : Op ι)ᴴ) *
      ((left : Op ι) * coeff * (right : Op ι)ᴴ)ᴴ =
      left * (coeff * coeffᴴ) * (left : Op ι)ᴴ := by
    simp [Matrix.mul_assoc]
    simp [← Matrix.mul_assoc, hright, Matrix.one_mul]
  rw [hprod, Matrix.trace_mul_cycle, hleft, Matrix.one_mul]

end

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section

variable (ψ : EuclideanSpace ℂ (ι × ι))

/-- The coefficient matrix of a bipartite vector in the fixed computational
bases. This is a representation adapter, not a change of state. -/
def schmidtCoefficientMatrix : Op ι :=
  Matrix.of fun row col => ψ (row, col)

/-- Schmidt coordinates chosen from the proved square-matrix decomposition.
The choice is made once for the state and is independent of all measurements. -/
noncomputable def schmidtCoordinates :
    Matrix.unitaryGroup ι ℂ × Matrix.unitaryGroup ι ℂ × (ι → ℝ) :=
  let existence := exists_schmidt_coordinates (schmidtCoefficientMatrix ψ)
  ⟨Classical.choose existence, Classical.choose (Classical.choose_spec existence),
    Classical.choose (Classical.choose_spec (Classical.choose_spec existence))⟩

/-- The chosen coordinates reconstruct the coefficient matrix with nonnegative
Schmidt coefficients. In particular, this includes nonfaithful reduced states. -/
theorem schmidtCoordinates_spec :
    (∀ index, 0 ≤ (schmidtCoordinates ψ).2.2 index) ∧
      schmidtCoefficientMatrix ψ = ((schmidtCoordinates ψ).1 : Op ι) *
        Matrix.diagonal (fun index => ((schmidtCoordinates ψ).2.2 index : ℂ)) *
          ((schmidtCoordinates ψ).2.1 : Op ι)ᴴ :=
  Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (exists_schmidt_coordinates (schmidtCoefficientMatrix ψ))))

/-- The unitary identifying the transposed Bob coordinates with the Alice
Schmidt coordinates. Zero Schmidt directions use the orthonormal completion. -/
noncomputable def schmidtMirrorUnitary :
    Matrix.unitaryGroup ι ℂ :=
  (schmidtCoordinates ψ).1 * star (schmidtCoordinates ψ).2.1

/-- The state-dependent opposite-register mirror, a linear map on Bob
operators. It reverses multiplication because it includes a transpose. -/
noncomputable def schmidtMirror : Op ι →ₗ[ℂ] Op ι where
  toFun bob := (schmidtMirrorUnitary ψ : Op ι) * bobᵀ * (schmidtMirrorUnitary ψ : Op ι)ᴴ
  map_add' first second := by simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' scalar bob := by
    simp [Matrix.transpose_smul]

/-- Vectorizing a left/right operator difference gives its coefficient-matrix
intertwining error, with the Hilbert norm rather than the function supremum norm. -/
theorem schmidt_action_norm_sq (alice bob : Op ι) :
    ‖applyOperatorToState (heteroKron alice 1) ψ -
      applyOperatorToState (heteroKron 1 bob) ψ‖ ^ 2 =
      ∑ row, ∑ col, Complex.normSq
        ((alice * schmidtCoefficientMatrix ψ - schmidtCoefficientMatrix ψ * bobᵀ) row col) := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Complex.sq_norm, Fintype.sum_prod_type]
  simp [applyOperatorToState, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, heteroKron, Matrix.kronecker,
    Fintype.sum_prod_type, Matrix.mul_apply, schmidtCoefficientMatrix,
    Matrix.one_apply, ite_mul, mul_ite, mul_comm]

/-- Mirrors preserve the identity and therefore completeness of a measurement. -/
theorem schmidtMirror_one :
    schmidtMirror ψ 1 = 1 := by
  change (schmidtMirrorUnitary ψ : Op ι) * 1ᵀ *
    (schmidtMirrorUnitary ψ)ᴴ = 1
  simp
  exact Unitary.coe_mul_star_self _

/-- Multiplication is reversed by the Schmidt mirror. -/
theorem schmidtMirror_mul (first second : Op ι) :
    schmidtMirror ψ (first * second) = schmidtMirror ψ second * schmidtMirror ψ first := by
  have hunitary : (schmidtMirrorUnitary ψ)ᴴ *
      (schmidtMirrorUnitary ψ : Op ι) = 1 := Unitary.coe_star_mul_self _
  change _ * _ᵀ * _ = (_ * secondᵀ * _) * (_ * firstᵀ * _)
  simp [Matrix.mul_assoc]
  simp [← Matrix.mul_assoc, hunitary, Matrix.one_mul]

/-- The mirror preserves adjoints, in addition to reversing products. -/
theorem schmidtMirror_adjoint (bob : Op ι) :
    schmidtMirror ψ bobᴴ = (schmidtMirror ψ bob)ᴴ := by
  change _ * bobᴴᵀ * _ = (_ * bobᵀ * _)ᴴ
  simp [Matrix.mul_assoc]
  rfl

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
  let left := (schmidtCoordinates ψ).1
  let right := (schmidtCoordinates ψ).2.1
  let values := (schmidtCoordinates ψ).2.2
  let diagonal := Matrix.diagonal (fun index => (values index : ℂ))
  let alice' := leftᴴ * alice * (left : Op ι)
  let bob' := rightᴴ * bobᵀ * (right : Op ι)
  have hvalues := (schmidtCoordinates_spec ψ).1
  have hfactor : schmidtCoefficientMatrix ψ =
      left * diagonal * (right : Op ι)ᴴ := (schmidtCoordinates_spec ψ).2
  have hmirror : schmidtMirror ψ bob = left * bob' * (left : Op ι)ᴴ := by
    simp [schmidtMirror, schmidtMirrorUnitary, left, right, bob', Matrix.mul_assoc,
      Matrix.star_eq_conjTranspose]
  have hbob' : bob'.IsHermitian := by
    change _ = _
    simp [Matrix.conjTranspose_conjTranspose, hbob.transpose.eq, bob', Matrix.mul_assoc]
  have hleft : left * (left : Op ι)ᴴ = 1 := Unitary.coe_mul_star_self left
  have hleft' : leftᴴ * (left : Op ι) = 1 := Unitary.coe_star_mul_self left
  have hright : right * (right : Op ι)ᴴ = 1 := Unitary.coe_mul_star_self right
  have hcancel (middle : Op ι) : left * ((left : Op ι)ᴴ * middle) = middle := by
    simp [← Matrix.mul_assoc, hleft]
  have hcancel' (middle : Op ι) : leftᴴ * ((left : Op ι) * middle) = middle := by
    simp [← Matrix.mul_assoc, hleft']
  have hmirrordiff : schmidtMirror ψ bob * schmidtCoefficientMatrix ψ -
      schmidtCoefficientMatrix ψ * bobᵀ =
      left * (bob' * diagonal - diagonal * bob') * (right : Op ι)ᴴ := by
    simp_all
    simp only [bob', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hcancel', hright,
      Matrix.mul_one]
  have halicediff : alice * schmidtCoefficientMatrix ψ - schmidtCoefficientMatrix ψ * bobᵀ =
      left * (alice' * diagonal - diagonal * bob') * (right : Op ι)ᴴ := by
    simp [hfactor, alice', bob', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hcancel, hright, Matrix.mul_one]
  rw [schmidt_action_norm_sq, schmidt_action_norm_sq, hmirrordiff, halicediff,
    schmidt_entry_mass_unitary, schmidt_entry_mass_unitary]
  refine schmidt_diagonal_mirror_estimate values hvalues alice' bob' ?_ hbob'
  change _ᴴ = _
  simp [Matrix.conjTranspose_conjTranspose, halice.eq, alice', Matrix.mul_assoc]

end

/-- Applying the fixed Schmidt mirror to every effect produces an actual
measurement; no normalization or completion of its effects is required. -/
noncomputable def schmidtMirrorMeasurement {α : Type*} [Fintype α]
    (ψ : EuclideanSpace ℂ (ι × ι)) (measurement : Measurement α ι) : Measurement α ι :=
  Measurement.ofSumEqOne (fun answer => schmidtMirror ψ (measurement.effect answer))
    (fun answer => Matrix.nonneg_iff_posSemidef.mpr
      ((by
         have hpositive := (Matrix.nonneg_iff_posSemidef.mp (measurement.pos answer)).transpose.conjTranspose_mul_mul_same (schmidtMirrorUnitary ψ : Op _)ᴴ
         simpa only [schmidtMirror, LinearMap.coe_mk, AddHom.coe_mk,
           Matrix.conjTranspose_conjTranspose] using hpositive)))
    (by rw [← map_sum, measurement.sum_eq_one, schmidtMirror_one])

/-- Mirroring commutes with coarse-graining along any evaluation map. -/
theorem schmidtMirrorMeasurement_postprocess {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (ψ : EuclideanSpace ℂ (ι × ι))
    (measurement : Measurement α ι) (evaluation : α → β) (answer : β) :
    ((schmidtMirrorMeasurement ψ measurement).postprocess evaluation).effect answer =
      schmidtMirror ψ ((measurement.postprocess evaluation).effect answer) := by
  change (∑ original ∈ _,
      schmidtMirror ψ (measurement.effect original)) =
    schmidtMirror ψ (∑ original ∈ Finset.univ.filter
      (fun original => evaluation original = answer), measurement.effect original)
  simp

/-- A projective measurement has a projective Schmidt mirror. -/
theorem schmidtMirrorMeasurement_isProjective {α : Type*} [Fintype α]
    (ψ : EuclideanSpace ℂ (ι × ι)) (measurement : Measurement α ι)
    (hprojective : MIPStarRE.QPBT.Measurement.IsProjective measurement) :
    MIPStarRE.QPBT.Measurement.IsProjective (schmidtMirrorMeasurement ψ measurement) := by
  intro answer
  change IsProj (schmidtMirror ψ _)
  constructor
  · change _ = _
    rw [← schmidtMirror_mul, (hprojective answer).isIdempotentElem.eq]
  · change _ᴴ = _
    rw [← schmidtMirror_adjoint,
      (hprojective answer).isSelfAdjoint.isHermitian.eq]

end MIPStarRE.QPBT
