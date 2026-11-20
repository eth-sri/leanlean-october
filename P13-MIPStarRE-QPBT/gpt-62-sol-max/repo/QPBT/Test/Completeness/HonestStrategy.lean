module

public import QPBT.Algebra.PauliTheorems
public import QPBT.Games.DistanceTheorems.TensorSupport
public import QPBT.Observables.ExpandedCommutation
public import QPBT.Observables.LineMeasurement.Restriction
public import QPBT.Algebra.Pauli
public import QPBT.Test.MagicSquareTheorems.Basic
public import QPBT.Test.MagicSquareTheorems.PerfectStrategy
public import QPBT.Test.MagicSquareTheorems.Rigidity.Relations
public import QPBT.Test.MagicSquareTheorems.Rigidity.Dilation
public import QPBT.Test.MagicSquareTheorems.Rigidity.Anticommutation
public import QPBT.Test.MagicSquareTheorems.Rigidity.Transfer
public import QPBT.Test.MagicSquareTheorems.PerfectStrategy.Observables
public import QPBT.Test.MagicSquareTheorems.Rigidity.Consistency
public import QPBT.Test.MagicSquareTheorems.Rigidity.GroundSlice
public import QPBT.Test.MagicSquareTheorems.Rigidity.Marginals
public import QPBT.Test.PauliBasisTest

/-!
# The honest Pauli basis measurements of the completeness proof

This module builds the measurements used by the honest strategy of
`lem:pauli-completeness`: the generalized Pauli basis measurement in a fixed
basis `W`, and its coarse-graining by the binary trace
`h ↦ tr(g_h(u_W) r_W)` which the source calls `A` (for `W = X`) and `B`
(for `W = Z`).  The main results are the observable identity

  `A_0 - A_1 = τ^W(ind_m(u_W) r_W)`

of `eq:finally-got-an-observable`, and the resulting commutation law

  `𝒪_A 𝒪_B = (-1)^γ 𝒪_B 𝒪_A`

with `γ` the phase bit `eq:gamma-value`.  When `γ ≠ 0` the two observables
anticommute, so `thm:ms-from-ac` produces the Magic Square part of the honest
strategy.

## References

The construction is the strategy displayed in the proof of
`lem:pauli-completeness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1237-1360`;
blueprint `lem:pauli-completeness`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

variable {K ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K]
  [Fintype ι] [DecidableEq ι]

/-! ### The generalized Pauli basis measurement -/

/-- Every generalized Pauli projector is a nonnegative operator.  The
positive semidefiniteness it repackages is `posSemidef_pauliProj`, blueprint
`def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1101-1122`. -/
theorem pauliProj_nonneg (W : PauliKind) (e : ι → K) : 0 ≤ pauliProj W e :=
  Matrix.nonneg_iff_posSemidef.mpr (posSemidef_pauliProj W e)

/-- Every generalized Pauli projector is Hermitian. -/
theorem pauliProj_conjTranspose (W : PauliKind) (e : ι → K) :
    (pauliProj W e)ᴴ = pauliProj W e :=
  (posSemidef_pauliProj W e).isHermitian.eq

/-- The generalized Pauli basis measurement in basis `W`: the projective
measurement whose outcomes are the labels of blueprint `def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1101-1122`. -/
noncomputable def pauliBasisMeasurement (W : PauliKind) :
    Measurement (ι → K) (ι → K) :=
  Measurement.ofSumEqOne (pauliProj W) (pauliProj_nonneg W) (sum_pauliProj_eq_one W)

/-! ### Symmetry and Hermiticity of the generalized Pauli observables -/

/-- Generalized Pauli observables are symmetric matrices in the computational
basis.  Symmetry is what makes the honest measurements consistent on the EPR
state used by `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1237-1360`. -/
theorem tauObservable_transpose (W : PauliKind) (a : ι → K) :
    (tauObservable W a)ᵀ = tauObservable W a := by
  rw [tauObservable_eq_sum_pauliProj]
  simp [Matrix.transpose_sum, Matrix.transpose_smul, pauliProj_transpose]

/-! ### Orthogonality of the generalized Pauli projectors

The generalized Pauli projectors in a fixed basis are pairwise orthogonal, so
every coarse-graining of a Pauli basis measurement is again projective.  This is
the projectivity used throughout the honest strategy of `lem:pauli-completeness`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1370`.
-/

/-- Every generalized Pauli projector is a projector. -/
theorem pauliProj_isProj (W : PauliKind) (e : ι → K) : IsProj (pauliProj W e) := by
  refine isStarProjection_iff'.2 ⟨?_, ?_⟩
  · simpa using pauliProj_mul_pauliProj W e e
  · rw [Matrix.star_eq_conjTranspose, pauliProj_conjTranspose]

/-! ### The honest Pair/W measurements

For an ambient question `ω = (u_X, u_Z, r_X, r_Z)` the honest player measures
the Pauli register in basis `W` and reports the binary trace
`tr(g_h(u_W) r_W)` of the resulting label.  These are the measurements `A` and
`B` of the proof of `lem:pauli-completeness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1277-1286`.
-/

/-- The binary trace bit `tr(g_h(u) r)` reported by the honest Pair/W
measurement on the Pauli label `h`.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1277-1286`. -/
noncomputable def pauliTraceBit (P : AdmissibleParams)
    (u : PauliPoint P) (r : PauliScalar P) (h : PauliRegister P) : ZMod 2 :=
  fixedBinTrace P.model (lowDegreeEnc h u * r)

/-- The honest Pair/W measurement `τ^W_{[tr(g_·(u) r) = β]}` of the proof of
`lem:pauli-completeness`: the generalized Pauli basis measurement coarse-grained
by the trace bit.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1277-1286`,
blueprint `lem:pauli-completeness`. -/
noncomputable def pauliTraceMeasurement (P : AdmissibleParams) (W : PauliKind)
    (u : PauliPoint P) (r : PauliScalar P) :
    Measurement (ZMod 2) (PauliRegister P) :=
  (pauliBasisMeasurement W).postprocess (pauliTraceBit P u r)

/-- The trace measurement at the basis-selected blocks of a joint query. -/
noncomputable abbrev pauliTraceReadout (P : AdmissibleParams) (W : PauliKind) (z : PauliSpace P) :=
  pauliTraceMeasurement P W (pauliPointBlock W z) (pauliTraceFactor W z)

section

variable (P : AdmissibleParams) (W : PauliKind)
    (u : PauliPoint P) (r : PauliScalar P)
include P W u r

/-- Equation `eq:finally-got-an-observable`: the observable of the honest
Pair/W measurement is the generalized Pauli observable at the label
`ind_m(u) r`.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1300-1315`. -/
theorem obsOf_pauliTraceMeasurement :
    obsOf (pauliTraceMeasurement P W u r) =
      tauObservable W (r • indicatorVec u) := by
  rw [← sum_phaseSign_smul_effect_eq_obsOf, pauliTraceMeasurement,
    Measurement.sum_smul_postprocess, tauObservable_eq_sum_pauliProj]
  refine Finset.sum_congr rfl fun h _ => ?_
  change phaseSign (fixedBinTrace P.model (lowDegreeEnc h u * r)) • pauliProj W h = _
  rw [lowDegreeEnc_eq_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm (indicatorVec u),
    mul_comm r]
  rfl

/-- Each effect of the honest Pair/W measurement is the spectral projector of
its observable, so the measurement is projective; part of the projectivity
assertion of the honest strategy in the proof of `lem:pauli-completeness`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1370`. -/
theorem pauliTraceMeasurement_effect_eq_reflectionEffect (b : ZMod 2) :
    (pauliTraceMeasurement P W u r).effect b =
      reflectionEffect (tauObservable W (r • indicatorVec u)) b := by
  rw [← obsOf_pauliTraceMeasurement, reflectionEffect_obsOf_measurement]

/-- The honest Pair/W measurement is projective, as asserted for the honest
strategy in the proof of `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1370`. -/
theorem pauliTraceMeasurement_projective :
    MIPStarRE.QPBT.Measurement.IsProjective (pauliTraceMeasurement P W u r) := by
  intro b
  rw [pauliTraceMeasurement_effect_eq_reflectionEffect]
  exact reflectionMeasurement_projective (tauObservable W (r • indicatorVec u))
    (tauObservable_conjTranspose W _) (tauObservable_sq W _) b

/-- The effects of the honest Pair/W measurement are symmetric matrices. -/
theorem pauliTraceMeasurement_effect_transpose (b : ZMod 2) :
    ((pauliTraceMeasurement P W u r).effect b)ᵀ =
      (pauliTraceMeasurement P W u r).effect b := by
  rw [pauliTraceMeasurement_effect_eq_reflectionEffect]
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · simp only [reflectionEffect, if_pos]
    rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_one,
      tauObservable_transpose]
  · simp only [reflectionEffect, if_neg one_ne_zero]
    rw [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_one,
      tauObservable_transpose]

end

/-! ### Honest line measurements -/

/-- Restrict a multivariate polynomial to an axis-parallel line, retaining the
coefficients through degree `d`.  This is the degree-`d` answer used for the
axis-line clause of `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1263-1273`. -/
noncomputable def restrictToAxisLine (L : LdParams) (line : LineDesc L)
    (g : MvPolynomial (Fin L.m) (ScalarQ L)) : DegPoly L L.d :=
  fun i => (polynomialOnLine L line g).coeff i.val

/-- The coefficient-list restriction to an axis line evaluates to the original
low-degree encoding at every point of that line. -/
theorem evalCoefficient_restrictToAxisLine_lowDegreeEncoding
    (L : LdParams) (line : LineDesc L) (hline : line.kind = .axis)
    (h : Cube L.m → ScalarQ L) (t : ScalarQ L) :
    evalCoefficient (restrictToAxisLine L line (lowDegreeEncoding h)) t =
      MvPolynomial.eval (line.base + t • line.direction) (lowDegreeEncoding h) := by
  calc
    evalCoefficient (restrictToAxisLine L line (lowDegreeEncoding h)) t =
        Polynomial.eval t (polynomialOnLine L line (lowDegreeEncoding h)) := by
      unfold evalCoefficient restrictToAxisLine
      rw [Polynomial.eval_eq_sum_range'
        (Nat.lt_succ_of_le
          ((polynomialOnLine_lowDegreeEncoding_natDegree_le_one_of_axis
            L line hline h).trans L.hd)) t]
      exact Fin.sum_univ_eq_sum_range
        (fun i => (polynomialOnLine L line (lowDegreeEncoding h)).coeff i * t ^ i)
        (L.d + 1)
    _ = _ := eval_polynomialOnLine L line (lowDegreeEncoding h) t

/-! ### The commutation law of the honest pair -/

/-- The commutation law `𝒪_A 𝒪_B = (-1)^γ 𝒪_B 𝒪_A` of the proof of
`lem:pauli-completeness`, with `γ` the phase bit `eq:gamma-value`.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1316-1330`. -/
theorem obsOf_pauliTraceMeasurement_mul_comm (P : AdmissibleParams) (z : PauliSpace P) :
    obsOf (pauliTraceReadout P .X z) *
        obsOf (pauliTraceReadout P .Z z) =
      phaseSign (pauliPairGamma P z) •
        (obsOf (pauliTraceReadout P .Z z) *
          obsOf (pauliTraceReadout P .X z)) := by
  rw [obsOf_pauliTraceMeasurement, obsOf_pauliTraceMeasurement, tauObservable_X_mul_Z]
  rfl

/-- If the phase bit `γ` of `eq:gamma-value` is nonzero, the two honest Pair/W
observables anticommute.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1316-1330`. -/
theorem obsOf_pauliTraceMeasurement_anticommute (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0) :
    obsOf (pauliTraceReadout P .X z) *
        obsOf (pauliTraceReadout P .Z z) =
      -(obsOf (pauliTraceReadout P .Z z) *
        obsOf (pauliTraceReadout P .X z)) := by
  rw [obsOf_pauliTraceMeasurement_mul_comm]
  simp_all [phaseSign]

/-! ### The pointwise Magic Square measurement -/

section

variable (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0)
include P z hgamma

/-- The nine cell measurements obtained from the anticommuting Pair/X and
Pair/Z observables at a question with nonzero phase bit. -/
noncomputable def pauliMagicCellMeasurement :
    Fin 9 → Measurement (ZMod 2) (PauliRegister P × ZMod 2) :=
  let A := pauliTraceReadout P .X z
  let B := pauliTraceReadout P .Z z
  msCellMeasurement (obsOf A) (obsOf B)
    (obsOf_conjTranspose A (pauliTraceMeasurement_projective P .X _ _))
    (obsOf_conjTranspose B (pauliTraceMeasurement_projective P .Z _ _))
    (obsOf_sq A (pauliTraceMeasurement_projective P .X _ _))
    (obsOf_sq B (pauliTraceMeasurement_projective P .Z _ _))
    (obsOf_pauliTraceMeasurement_anticommute P z hgamma)

/-- Every Pauli-induced Magic Square cell measurement is projective. -/
theorem pauliMagicCellMeasurement_projective (j : Fin 9) :
    MIPStarRE.QPBT.Measurement.IsProjective
      (pauliMagicCellMeasurement P z hgamma j) := by
  simp [pauliMagicCellMeasurement]
  exact msCellMeasurement_projective _ _
    (obsOf_conjTranspose _ (pauliTraceMeasurement_projective P .X _ _))
    (obsOf_conjTranspose _ (pauliTraceMeasurement_projective P .Z _ _))
    (obsOf_sq _ (pauliTraceMeasurement_projective P .X _ _))
    (obsOf_sq _ (pauliTraceMeasurement_projective P .Z _ _))
    (obsOf_pauliTraceMeasurement_anticommute P z hgamma) j

/-- Cell effects belonging to one Magic Square constraint commute. -/
theorem pauliMagicCellMeasurement_commute
    (i : Fin 6) (k l : Fin 3) (a b : ZMod 2) :
    Commute
      ((pauliMagicCellMeasurement P z hgamma (msConstraintVars i k)).effect a)
      ((pauliMagicCellMeasurement P z hgamma (msConstraintVars i l)).effect b) := by
  simp [pauliMagicCellMeasurement]
  exact reflectionEffect_commute
    (msConstraintObservable_commute _ _
      (obsOf_pauliTraceMeasurement_anticommute P z hgamma) i k l) a b

/-- The Magic Square measurement family used at a Pauli question with nonzero
phase bit. -/
noncomputable def pauliMagicMeasurement :
    MsType → Measurement MsAnswer (PauliRegister P × ZMod 2) :=
  msStrategyMeasurement (pauliMagicCellMeasurement P z hgamma)
    (pauliMagicCellMeasurement_projective P z hgamma)
    (pauliMagicCellMeasurement_commute P z hgamma)

/-- The Pauli-induced Magic Square measurement is projective. -/
theorem pauliMagicMeasurement_projective (x : MsType) :
    MIPStarRE.QPBT.Measurement.IsProjective
      (pauliMagicMeasurement P z hgamma x) := msStrategyMeasurement_projective _ _ _ x

/-- Every effect of the Pauli-induced Magic Square measurement is symmetric. -/
theorem pauliMagicMeasurement_effect_transpose
    (x : MsType) (a : MsAnswer) :
    ((pauliMagicMeasurement P z hgamma x).effect a)ᵀ =
      (pauliMagicMeasurement P z hgamma x).effect a := by
  apply msStrategyMeasurement_effect_transpose
  intro j b
  simp [pauliMagicCellMeasurement]
  apply msCellMeasurement_transpose
  · rw [obsOf_pauliTraceMeasurement]
    exact tauObservable_transpose _ _
  · rw [obsOf_pauliTraceMeasurement]
    exact tauObservable_transpose _ _

/-- The Pauli-induced Magic Square measurements commute on an incident
constraint-variable pair. -/
theorem pauliMagicMeasurement_incident_commute
    (i : Fin 6) (k : Fin 3) (a b : MsAnswer) :
    Commute ((pauliMagicMeasurement P z hgamma (.constraint i)).effect a)
      ((pauliMagicMeasurement P z hgamma
        (.var (msConstraintVars i k))).effect b) := msStrategyMeasurement_incident_commute _ _ _ i k a b

/-- The distinguished variable effects of the Pauli-induced Magic Square
measurement are the tensor placements of the Pair/X and Pair/Z effects. -/
theorem pauliMagicMeasurement_var_effect (b : ZMod 2) :
    (pauliMagicMeasurement P z hgamma (.var 0)).effect (.bit b) =
        heteroKron
          ((pauliTraceReadout P .X z).effect b)
          (1 : Op (ZMod 2)) ∧
      (pauliMagicMeasurement P z hgamma (.var 4)).effect (.bit b) =
        heteroKron
          ((pauliTraceReadout P .Z z).effect b)
          (1 : Op (ZMod 2)) := by
  constructor
  · unfold pauliMagicMeasurement
    rw [msStrategyMeasurement_var_bit]
    change reflectionEffect
        (heteroKron
          (obsOf (pauliTraceReadout P .X z))
          (1 : Op (ZMod 2))) b = _
    rw [← MagicSquareRigidity.reflectionEffect_heteroKron_left,
      reflectionEffect_obsOf_measurement]
  · unfold pauliMagicMeasurement
    rw [msStrategyMeasurement_var_bit]
    change reflectionEffect
        (heteroKron
          (obsOf (pauliTraceReadout P .Z z))
          (1 : Op (ZMod 2))) b = _
    rw [← MagicSquareRigidity.reflectionEffect_heteroKron_left,
      reflectionEffect_obsOf_measurement]

end

/-! ### The Pair measurement in the case `γ = 0`

If the phase bit vanishes, the two honest Pair/W measurements commute and their
product is the Pair measurement `E^{Pair,ω}_{β_X, β_Z} = A_{β_X} B_{β_Z}` of
Equation `eq:pair-definition` in the proof of `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1331-1344`.
-/

section

variable (P : AdmissibleParams)
    (z : PauliSpace P)
include P z

/-- If the phase bit `γ` of `eq:gamma-value` vanishes, the two honest Pair/W
observables commute.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1316-1330`. -/
theorem obsOf_pauliTraceMeasurement_commute (hgamma : pauliPairGamma P z = 0) :
    Commute (obsOf (pauliTraceReadout P .X z))
      (obsOf (pauliTraceReadout P .Z z)) := by
  rw [commute_iff_eq, obsOf_pauliTraceMeasurement_mul_comm, hgamma]
  simp [phaseSign]

/-- If the phase bit `γ` vanishes, the effects of the two honest Pair/W
measurements commute; this is the commutation assertion of the honest strategy
in the case `γ = 0`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1374-1382`. -/
theorem pauliTraceMeasurement_effect_commute (hgamma : pauliPairGamma P z = 0) (a b : ZMod 2) :
    Commute ((pauliTraceReadout P .X z).effect a)
      ((pauliTraceReadout P .Z z).effect b) := by
  have hOO :
      Commute (tauObservable PauliKind.X (pauliRXBlock z • indicatorVec (pauliXBlock z)))
        (tauObservable PauliKind.Z (pauliRZBlock z • indicatorVec (pauliZBlock z))) := by
    rw [← obsOf_pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z),
      ← obsOf_pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)]
    exact obsOf_pauliTraceMeasurement_commute P z hgamma
  rw [pauliTraceMeasurement_effect_eq_reflectionEffect,
    pauliTraceMeasurement_effect_eq_reflectionEffect]
  exact reflectionEffect_commute hOO a b

/-- The Pair effect `E^{Pair,ω}_{β_X, β_Z} = A_{β_X} B_{β_Z}` of Equation
`eq:pair-definition`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1331-1339`. -/
noncomputable def pauliPairEffect
    (β : ZMod 2 × ZMod 2) : Op (PauliRegister P) :=
  (pauliTraceReadout P .X z).effect β.1 *
    (pauliTraceReadout P .Z z).effect β.2

/-- For `γ = 0` the Pair effects are projectors, being products of commuting
projectors.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1331-1344`. -/
theorem pauliPairEffect_isProj
    (hgamma : pauliPairGamma P z = 0) (β : ZMod 2 × ZMod 2) :
    IsProj (pauliPairEffect P z β) :=
  IsStarProjection.mul (pauliTraceMeasurement_projective P .X _ _ β.1)
    (pauliTraceMeasurement_projective P .Z _ _ β.2)
    (pauliTraceMeasurement_effect_commute P z hgamma β.1 β.2)

/-- The Pair effects sum to the identity. -/
theorem sum_pauliPairEffect :
    ∑ β : ZMod 2 × ZMod 2, pauliPairEffect P z β = 1 := by
  rw [Fintype.sum_prod_type]
  simp [pauliPairEffect, ← Finset.mul_sum, (pauliTraceReadout P .X z).sum_eq_one,
    (pauliTraceReadout P .Z z).sum_eq_one]

/-- The Pair measurement of Equation `eq:pair-definition` in the case `γ = 0`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1331-1344`,
blueprint `lem:pauli-completeness`. -/
noncomputable def pauliPairMeasurement
    (hgamma : pauliPairGamma P z = 0) : Measurement (ZMod 2 × ZMod 2) (PauliRegister P) :=
  Measurement.ofSumEqOne (pauliPairEffect P z)
    (fun β => (pauliPairEffect_isProj P z hgamma β).nonneg) (sum_pauliPairEffect P z)

/-- The Pair measurement is projective. -/
theorem pauliPairMeasurement_projective
    (hgamma : pauliPairGamma P z = 0) :
    MIPStarRE.QPBT.Measurement.IsProjective (pauliPairMeasurement P z hgamma) :=
  pauliPairEffect_isProj P z hgamma

end

end

end MIPStarRE.QPBT
