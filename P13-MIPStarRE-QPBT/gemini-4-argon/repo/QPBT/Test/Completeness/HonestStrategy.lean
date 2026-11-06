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
public import QPBT.Test.MagicSquareTheorems.Rigidity.IdealTarget
public import QPBT.Test.MagicSquareTheorems.Rigidity.JointState
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

omit [Fintype K] in
/-- Generalized Pauli observables are symmetric matrices in the computational
basis.  Symmetry is what makes the honest measurements consistent on the EPR
state used by `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1237-1360`. -/
theorem tauObservable_transpose (W : PauliKind) (a : ι → K) :
    (tauObservable W a)ᵀ = tauObservable W a := by
  haveI : CharP K 2 := (Algebra.charP_iff (ZMod 2) K 2).mp (ZMod.charP 2)
  have hswap : ∀ x y c : K, (x = y + c) ↔ (y = x + c) := by
    intro x y c
    constructor
    · rintro rfl
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rintro rfl
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  ext x y
  rw [Matrix.transpose_apply]
  cases W with
  | X =>
      refine Finset.prod_congr rfl fun i _ => ?_
      change (if y i = x i + a i then (1 : ℂ) else 0) = if x i = y i + a i then 1 else 0
      by_cases h : x i = y i + a i
      · rw [if_pos h, if_pos ((hswap _ _ _).mp h)]
      · rw [if_neg h, if_neg (fun hc => h ((hswap _ _ _).mp hc))]
  | Z =>
      refine Finset.prod_congr rfl fun i _ => ?_
      change (if y i = x i then phaseSign (binTrace K (a i * x i)) else 0) =
        if x i = y i then phaseSign (binTrace K (a i * y i)) else 0
      by_cases h : x i = y i
      · rw [h]
      · rw [if_neg h, if_neg (fun hc => h hc.symm)]

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

/-- Every coarse-graining of a generalized Pauli basis measurement is
projective.  This is the projectivity of the honest Point, Line and Pauli
measurements in the proof of `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1370`. -/
theorem pauliBasisMeasurement_postprocess_projective {β : Type*} [Fintype β]
    [DecidableEq β] (W : PauliKind) (g : (ι → K) → β) :
    MIPStarRE.QPBT.Measurement.IsProjective ((pauliBasisMeasurement W).postprocess g) :=
  SandwichProduct.postprocess_isProjective (pauliBasisMeasurement W)
    (fun e => pauliProj_isProj W e) g

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
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) (h : PauliRegister P) : ZMod 2 :=
  fixedBinTrace P.model (lowDegreeEnc h u * r)

/-- The honest Pair/W measurement `τ^W_{[tr(g_·(u) r) = β]}` of the proof of
`lem:pauli-completeness`: the generalized Pauli basis measurement coarse-grained
by the trace bit.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1277-1286`,
blueprint `lem:pauli-completeness`. -/
noncomputable def pauliTraceMeasurement (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) :
    Measurement (ZMod 2) (PauliRegister P) :=
  (pauliBasisMeasurement W).postprocess (pauliTraceBit P u r)

/-- The effect of the honest Pair/`W` measurement at the bit `β` is the sum of
the generalized Pauli projectors over the labels whose trace bit equals `β`,
which is the coarse-grained projector `τ^W_{[tr(g_·(u) r) = β]}` of the paper. -/
theorem pauliTraceMeasurement_effect (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) (b : ZMod 2) :
    (pauliTraceMeasurement P W u r).effect b =
      ∑ h ∈ Finset.univ.filter (fun h : PauliRegister P => pauliTraceBit P u r h = b),
        pauliProj W h := rfl

/-- Equation `eq:finally-got-an-observable`: the observable of the honest
Pair/W measurement is the generalized Pauli observable at the label
`ind_m(u) r`.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1300-1315`. -/
theorem obsOf_pauliTraceMeasurement (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) :
    obsOf (pauliTraceMeasurement P W u r) =
      tauObservable W (r • indicatorVec u) := by
  classical
  rw [obsOf, pauliTraceMeasurement_effect, pauliTraceMeasurement_effect,
    tauObservable_eq_sum_pauliProj, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hp : binTrace (PauliScalar P) (dotProduct (r • indicatorVec u) e) =
      pauliTraceBit P u r e := by
    congr 1
    rw [lowDegreeEnc_eq_dotProduct]
    simp only [dotProduct, Finset.sum_mul, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hp]
  rcases zmod_two_eq_zero_or_one (pauliTraceBit P u r e) with h | h <;>
    simp [h, phaseSign]

theorem pauliTraceMeasurement_effect_eq_reflectionEffect (P : AdmissibleParams)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) (r : PauliScalar P) (b : ZMod 2) :
    (pauliTraceMeasurement P W u r).effect b =
      reflectionEffect (tauObservable W (r • indicatorVec u)) b := by
  rw [← obsOf_pauliTraceMeasurement, reflectionEffect_obsOf_measurement]

theorem pauliTraceMeasurement_projective (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) :
    MIPStarRE.QPBT.Measurement.IsProjective (pauliTraceMeasurement P W u r) := by
  intro b
  rw [pauliTraceMeasurement_effect_eq_reflectionEffect]
  exact reflectionMeasurement_projective (tauObservable W (r • indicatorVec u))
    (tauObservable_conjTranspose W _) (tauObservable_sq W _) b

theorem pauliTraceMeasurement_effect_transpose (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) (b : ZMod 2) :
    ((pauliTraceMeasurement P W u r).effect b)ᵀ =
      (pauliTraceMeasurement P W u r).effect b := by
  rw [pauliTraceMeasurement_effect_eq_reflectionEffect]
  rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
    simp [reflectionEffect, Matrix.transpose_smul, Matrix.transpose_add,
      Matrix.transpose_sub, tauObservable_transpose]

/-! ### The honest Point/W measurements -/

noncomputable def pauliPointMeasurement (P : AdmissibleParams) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) : Measurement (PauliScalar P) (PauliRegister P) :=
  (pauliBasisMeasurement W).postprocess (fun h => lowDegreeEnc h u)

/-! ### Honest line measurements -/

noncomputable def restrictToAxisLine (L : LdParams) (line : LineDesc L)
    (g : MvPolynomial (Fin L.m) (ScalarQ L)) : DegPoly L L.d :=
  fun i => (polynomialOnLine L line g).coeff i.val

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

noncomputable def pauliALineMeasurement (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    Measurement (Fin (P.d + 1) → PauliScalar P) (PauliRegister P) :=
    (pauliBasisMeasurement W).postprocess fun h =>
    restrictToAxisLine P.toLdParams
      (aLineDescOf P.toLdParams
        (ldALineCL P.toLdParams (pauliToLd P W z))) (lowDegreeEncoding h)

noncomputable def pauliDLineMeasurement (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    Measurement (Fin (P.m * P.d + 1) → PauliScalar P) (PauliRegister P) :=
    (pauliBasisMeasurement W).postprocess fun h =>
    restrictToLine P.toLdParams
      (dLineDescOf P.toLdParams
        (ldDLineCL P.toLdParams (pauliToLd P W z))) (lowDegreeEncoding h)

/-! ### The commutation law of the honest pair -/

theorem obsOf_pauliTraceMeasurement_mul_comm (P : AdmissibleParams) (z : PauliSpace P) :
    obsOf (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)) *
        obsOf (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)) =
      phaseSign (pauliPairGamma P z) •
        (obsOf (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)) *
          obsOf (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z))) := by
  rw [obsOf_pauliTraceMeasurement, obsOf_pauliTraceMeasurement, tauObservable_X_mul_Z]; rfl

theorem obsOf_pauliTraceMeasurement_anticommute (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0) :
    obsOf (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)) *
        obsOf (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)) =
      -(obsOf (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)) *
        obsOf (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z))) := by
  rw [obsOf_pauliTraceMeasurement_mul_comm]
  rcases zmod_two_eq_zero_or_one (pauliPairGamma P z) with h | h
  · exact absurd h hgamma
  · rw [h]; simp [phaseSign]

/-! ### The pointwise Magic Square measurement -/

noncomputable def pauliMagicCellMeasurement (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0) :
    Fin 9 → Measurement (ZMod 2) (PauliRegister P × ZMod 2) :=
  let A := pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)
  let B := pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)
  msCellMeasurement (obsOf A) (obsOf B)
    (obsOf_conjTranspose A (pauliTraceMeasurement_projective P .X _ _))
    (obsOf_conjTranspose B (pauliTraceMeasurement_projective P .Z _ _))
    (obsOf_sq A (pauliTraceMeasurement_projective P .X _ _))
    (obsOf_sq B (pauliTraceMeasurement_projective P .Z _ _))
    (obsOf_pauliTraceMeasurement_anticommute P z hgamma)

theorem pauliMagicCellMeasurement_projective (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0) (j : Fin 9) :
    MIPStarRE.QPBT.Measurement.IsProjective
      (pauliMagicCellMeasurement P z hgamma j) :=
  msCellMeasurement_projective _ _
    (obsOf_conjTranspose _ (pauliTraceMeasurement_projective P .X _ _))
    (obsOf_conjTranspose _ (pauliTraceMeasurement_projective P .Z _ _))
    (obsOf_sq _ (pauliTraceMeasurement_projective P .X _ _))
    (obsOf_sq _ (pauliTraceMeasurement_projective P .Z _ _))
    (obsOf_pauliTraceMeasurement_anticommute P z hgamma) j

theorem pauliMagicCellMeasurement_commute (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0)
    (i : Fin 6) (k l : Fin 3) (a b : ZMod 2) :
    Commute
      ((pauliMagicCellMeasurement P z hgamma (msConstraintVars i k)).effect a)
      ((pauliMagicCellMeasurement P z hgamma (msConstraintVars i l)).effect b) :=
  reflectionEffect_commute
    (msConstraintObservable_commute _ _
      (obsOf_sq _ (pauliTraceMeasurement_projective P .X _ _))
      (obsOf_sq _ (pauliTraceMeasurement_projective P .Z _ _))
      (obsOf_pauliTraceMeasurement_anticommute P z hgamma) i k l) a b

noncomputable def pauliMagicMeasurement (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0) :
    MsType → Measurement MsAnswer (PauliRegister P × ZMod 2) :=
  msStrategyMeasurement (pauliMagicCellMeasurement P z hgamma)
    (pauliMagicCellMeasurement_projective P z hgamma)
    (pauliMagicCellMeasurement_commute P z hgamma)

theorem pauliMagicMeasurement_projective (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0) (x : MsType) :
    MIPStarRE.QPBT.Measurement.IsProjective
      (pauliMagicMeasurement P z hgamma x) :=
  msStrategyMeasurement_projective _ _ _ x

theorem pauliMagicMeasurement_effect_transpose (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0)
    (x : MsType) (a : MsAnswer) :
    ((pauliMagicMeasurement P z hgamma x).effect a)ᵀ =
      (pauliMagicMeasurement P z hgamma x).effect a := by
  apply msStrategyMeasurement_effect_transpose
  intro j b
  simp only [pauliMagicCellMeasurement]
  apply msCellMeasurement_transpose <;> {
    rw [obsOf_pauliTraceMeasurement]; exact tauObservable_transpose _ _ }

theorem pauliMagicMeasurement_incident_commute (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0)
    (i : Fin 6) (k : Fin 3) (a b : MsAnswer) :
    Commute ((pauliMagicMeasurement P z hgamma (.constraint i)).effect a)
      ((pauliMagicMeasurement P z hgamma
        (.var (msConstraintVars i k))).effect b) :=
  msStrategyMeasurement_incident_commute _ _ _ i k a b

theorem pauliMagicMeasurement_var_effect (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0) (b : ZMod 2) :
    (pauliMagicMeasurement P z hgamma (.var 0)).effect (.bit b) =
        heteroKron
          ((pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)).effect b)
          (1 : Op (ZMod 2)) ∧
      (pauliMagicMeasurement P z hgamma (.var 4)).effect (.bit b) =
        heteroKron
          ((pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)).effect b)
          (1 : Op (ZMod 2)) := by
  constructor <;> {
    unfold pauliMagicMeasurement
    rw [msStrategyMeasurement_var_bit]
    change reflectionEffect (heteroKron (obsOf _) (1 : Op (ZMod 2))) b = _
    rw [← MagicSquareRigidity.reflectionEffect_heteroKron_left,
      reflectionEffect_obsOf_measurement] }

/-! ### The Pair measurement in the case `γ = 0` -/

theorem obsOf_pauliTraceMeasurement_commute (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z = 0) :
    Commute (obsOf (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)))
      (obsOf (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z))) := by
  rw [commute_iff_eq, obsOf_pauliTraceMeasurement_mul_comm, hgamma]; simp [phaseSign]

theorem pauliTraceMeasurement_effect_commute (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z = 0) (a b : ZMod 2) :
    Commute ((pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)).effect a)
      ((pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)).effect b) := by
  rw [pauliTraceMeasurement_effect_eq_reflectionEffect,
    pauliTraceMeasurement_effect_eq_reflectionEffect]
  refine reflectionEffect_commute ?_ a b
  rw [← obsOf_pauliTraceMeasurement, ← obsOf_pauliTraceMeasurement]
  exact obsOf_pauliTraceMeasurement_commute P z hgamma

noncomputable def pauliPairEffect (P : AdmissibleParams) (z : PauliSpace P)
    (β : ZMod 2 × ZMod 2) : Op (PauliRegister P) :=
  (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)).effect β.1 *
    (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)).effect β.2

theorem pauliPairEffect_isProj (P : AdmissibleParams) (z : PauliSpace P)
    (hgamma : pauliPairGamma P z = 0) (β : ZMod 2 × ZMod 2) :
    IsProj (pauliPairEffect P z β) :=
  IsStarProjection.mul (pauliTraceMeasurement_projective P .X _ _ β.1)
    (pauliTraceMeasurement_projective P .Z _ _ β.2)
    (pauliTraceMeasurement_effect_commute P z hgamma β.1 β.2)

theorem sum_pauliPairEffect (P : AdmissibleParams) (z : PauliSpace P) :
    ∑ β : ZMod 2 × ZMod 2, pauliPairEffect P z β = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [pauliPairEffect, ← Finset.mul_sum,
    (pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)).sum_eq_one,
    mul_one, (pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z)).sum_eq_one]

/-- The Pair measurement of Equation `eq:pair-definition` in the case `γ = 0`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1331-1344`,
blueprint `lem:pauli-completeness`. -/
noncomputable def pauliPairMeasurement (P : AdmissibleParams) (z : PauliSpace P)
    (hgamma : pauliPairGamma P z = 0) : Measurement (ZMod 2 × ZMod 2) (PauliRegister P) :=
  Measurement.ofSumEqOne (pauliPairEffect P z)
    (fun β => (pauliPairEffect_isProj P z hgamma β).nonneg) (sum_pauliPairEffect P z)

/-- The Pair measurement is projective. -/
theorem pauliPairMeasurement_projective (P : AdmissibleParams) (z : PauliSpace P)
    (hgamma : pauliPairGamma P z = 0) :
    MIPStarRE.QPBT.Measurement.IsProjective (pauliPairMeasurement P z hgamma) :=
  pauliPairEffect_isProj P z hgamma

end

end MIPStarRE.QPBT
