module

public import QPBT.Observables.ExpandedCommutation
public import QPBT.Observables.LineMeasurement.Restriction
public import QPBT.Test.MagicSquareTheorems.PerfectStrategy
public import QPBT.Test.MagicSquareTheorems.Rigidity.Marginals

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

section

variable (W : PauliKind)

/-- Every generalized Pauli projector is a nonnegative operator.  The
positive semidefiniteness it repackages is `posSemidef_pauliProj`, blueprint
`def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1101-1122`. -/
theorem pauliProj_nonneg (e : ι → K) : 0 ≤ pauliProj W e :=
  Matrix.nonneg_iff_posSemidef.mpr (posSemidef_pauliProj W e)

/-- The generalized Pauli basis measurement in basis `W`: the projective
measurement whose outcomes are the labels of blueprint `def:generalized-pauli`, paper origin
`references/qpbt-paper/04_preliminaries.tex:1101-1122`. -/
noncomputable def pauliBasisMeasurement :
    Measurement (ι → K) (ι → K) :=
  Measurement.ofSumEqOne (pauliProj W) (pauliProj_nonneg W) (sum_pauliProj_eq_one W)

/-! ### Symmetry and Hermiticity of the generalized Pauli observables -/

omit [Fintype K] in
/-- Generalized Pauli observables are symmetric matrices in the computational
basis.  Symmetry is what makes the honest measurements consistent on the EPR
state used by `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1237-1360`. -/
theorem tauObservable_transpose (a : ι → K) :
    (tauObservable W a)ᵀ = tauObservable W a := by
  haveI := (Algebra.charP_iff (ZMod 2) K 2).mp (ZMod.charP 2)
  have hswap : ∀ x y c : K, (x = y + c) ↔ (y = x + c) := by
    grind
  ext x y
  cases W with
  | X =>
      refine Finset.prod_congr rfl fun i _ => ?_
      change (if y i = x i + a i then 1 else 0) = if x i = y i + a i then 1 else 0
      simp_all
  | Z =>
      refine Finset.prod_congr rfl fun i _ => ?_
      change (if y i = x i then phaseSign (binTrace K (a i * x i)) else 0) =
        if x i = y i then _ else 0
      by_cases h : x i = y i
      · rw [h]
      · grind

/-! ### Orthogonality of the generalized Pauli projectors

The generalized Pauli projectors in a fixed basis are pairwise orthogonal, so
every coarse-graining of a Pauli basis measurement is again projective.  This is
the projectivity used throughout the honest strategy of `lem:pauli-completeness`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1370`.
-/

/-- Every generalized Pauli projector is a projector. -/
theorem pauliProj_isProj (e : ι → K) : IsProj (pauliProj W e) := by
  refine isStarProjection_iff'.2 ⟨?_, ?_⟩
  · simpa using pauliProj_mul_pauliProj W e e
  · rw [Matrix.star_eq_conjTranspose, (posSemidef_pauliProj _ _).isHermitian.eq]

end

/-- Every coarse-graining of a generalized Pauli basis measurement is
projective.  This is the projectivity of the honest Point, Line and Pauli
measurements in the proof of `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1370`. -/
theorem pauliBasisMeasurement_postprocess_projective {β : Type*} [Fintype β]
    [DecidableEq β] (W : PauliKind) (g : (ι → K) → β) :
    MIPStarRE.QPBT.Measurement.IsProjective ((pauliBasisMeasurement W).postprocess g) :=
  SandwichProduct.postprocess_isProjective (pauliBasisMeasurement W)
    (pauliProj_isProj W) g

/-! ### The honest Pair/W measurements

For an ambient question `ω = (u_X, u_Z, r_X, r_Z)` the honest player measures
the Pauli register in basis `W` and reports the binary trace
`tr(g_h(u_W) r_W)` of the resulting label.  These are the measurements `A` and
`B` of the proof of `lem:pauli-completeness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1277-1286`.
-/

section

variable (P : AdmissibleParams)

variable {P} in
/-- The binary trace bit `tr(g_h(u) r)` reported by the honest Pair/W
measurement on the Pauli label `h`.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1277-1286`. -/
noncomputable def pauliTraceBit
    (u : PauliPoint P) (r : PauliScalar P) (h : PauliRegister P) : ZMod 2 :=
  fixedBinTrace P.model (lowDegreeEnc h u * r)

section

variable (W : PauliKind) (u : PauliPoint P)

section

variable (r : PauliScalar P)

variable {P} in
/-- The honest Pair/W measurement `τ^W_{[tr(g_·(u) r) = β]}` of the proof of
`lem:pauli-completeness`: the generalized Pauli basis measurement coarse-grained
by the trace bit.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1277-1286`,
blueprint `lem:pauli-completeness`. -/
noncomputable def pauliTraceMeasurement :
    Measurement (ZMod 2) (PauliRegister P) :=
  (pauliBasisMeasurement W).postprocess (pauliTraceBit u r)

/-- The effect of the honest Pair/`W` measurement at the bit `β` is the sum of
the generalized Pauli projectors over the labels whose trace bit equals `β`,
which is the coarse-grained projector `τ^W_{[tr(g_·(u) r) = β]}` of the paper. -/
theorem pauliTraceMeasurement_effect (b : ZMod 2) :
    (pauliTraceMeasurement W u r).effect b =
      ∑ h ∈ Finset.univ.filter (fun h : PauliRegister P => pauliTraceBit u r h = b),
        pauliProj W h := rfl

/-- Equation `eq:finally-got-an-observable`: the observable of the honest
Pair/W measurement is the generalized Pauli observable at the label
`ind_m(u) r`.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1300-1315`. -/
theorem obsOf_pauliTraceMeasurement :
    obsOf (pauliTraceMeasurement W u r) =
      tauObservable W (r • indicatorVec u) := by
  classical
  have hdot : ∀ e : PauliRegister P,
      dotProduct (r • indicatorVec u) e = lowDegreeEnc e u * r := by
    intro e
    rw [lowDegreeEnc_eq_dotProduct]
    simp [dotProduct, Finset.sum_mul, smul_eq_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hp : ∀ e : PauliRegister P,
      phaseSign (binTrace (PauliScalar P) (dotProduct (r • indicatorVec u) e)) =
        phaseSign (pauliTraceBit u r e) := by
    intro e
    rw [hdot]
    rfl
  rw [tauObservable_eq_sum_pauliProj,
    Finset.sum_congr rfl (fun e (_ : e ∈ Finset.univ) => by rw [hp e]),
    ← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (PauliRegister P))
      (fun e => pauliTraceBit u r e = 0)]
  have hfilter :
      (Finset.univ.filter fun e : PauliRegister P => ¬ pauliTraceBit u r e = 0) =
        Finset.univ.filter fun e : PauliRegister P => pauliTraceBit u r e = 1 := by
    ext e
    rcases zmod_two_eq_zero_or_one (pauliTraceBit u r e) with h | h <;> simp [h]
  have h0 : ∑ e ∈ Finset.univ.filter (fun e : PauliRegister P => pauliTraceBit u r e = 0),
      phaseSign (pauliTraceBit u r e) • pauliProj W e =
      (pauliTraceMeasurement W u r).effect 0 := by
    rw [pauliTraceMeasurement_effect]
    refine Finset.sum_congr rfl fun e he => ?_
    simp [phaseSign, (Finset.mem_filter.mp he).2]
  have h1 : ∑ e ∈ Finset.univ.filter (fun e : PauliRegister P => ¬ pauliTraceBit u r e = 0),
      phaseSign (pauliTraceBit u r e) • pauliProj W e =
      -(pauliTraceMeasurement W u r).effect 1 := by
    rw [hfilter, pauliTraceMeasurement_effect]
    rw [← neg_one_smul ℂ _]
    rw [← Finset.smul_sum.symm]
    exact Finset.sum_congr rfl fun e he => by
      simp_all
      norm_num [phaseSign]
  simp [h0, h1]
  rfl

/-- Each effect of the honest Pair/W measurement is the spectral projector of
its observable, so the measurement is projective; part of the projectivity
assertion of the honest strategy in the proof of `lem:pauli-completeness`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1370`. -/
theorem pauliTraceMeasurement_effect_eq_reflectionEffect (b : ZMod 2) :
    (pauliTraceMeasurement W u r).effect b =
      reflectionEffect (tauObservable W (r • indicatorVec u)) b := by
  rw [← obsOf_pauliTraceMeasurement, reflectionEffect_obsOf_measurement]

/-- The honest Pair/W measurement is projective, as asserted for the honest
strategy in the proof of `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1370`. -/
theorem pauliTraceMeasurement_projective :
    MIPStarRE.QPBT.Measurement.IsProjective (pauliTraceMeasurement W u r) := by
  intro b
  rw [pauliTraceMeasurement_effect_eq_reflectionEffect]
  exact reflectionMeasurement_projective _
    (tauObservable_conjTranspose W _) (tauObservable_sq W _) b

/-- The effects of the honest Pair/W measurement are symmetric matrices. -/
theorem pauliTraceMeasurement_effect_transpose (b : ZMod 2) :
    ((pauliTraceMeasurement W u r).effect b)ᵀ =
      (pauliTraceMeasurement W u r).effect b := by
  rw [pauliTraceMeasurement_effect_eq_reflectionEffect]
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · simp [reflectionEffect, tauObservable_transpose]
  · simp_all [reflectionEffect, tauObservable_transpose]

end

/-! ### The honest Point/W measurements -/

/-- The honest Point/W measurement: the generalized Pauli basis measurement
coarse-grained by the value `g_h(u)` of the low-degree encoding at the point
`u`.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1248-1261`. -/
noncomputable def pauliPointMeasurement : Measurement (PauliScalar P) (PauliRegister P) :=
  (pauliBasisMeasurement W).postprocess (fun h => lowDegreeEnc h u)

end

end

/-! ### Honest line measurements -/

section

variable (L : LdParams) (line : LineDesc L)

/-- Restrict a multivariate polynomial to an axis-parallel line, retaining the
coefficients through degree `d`.  This is the degree-`d` answer used for the
axis-line clause of `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1263-1273`. -/
noncomputable def restrictToAxisLine
    (g : MvPolynomial (Fin L.m) (ScalarQ L)) : DegPoly L L.d :=
  fun i => (polynomialOnLine line g).coeff i.val

/-- The coefficient-list restriction to an axis line evaluates to the original
low-degree encoding at every point of that line. -/
theorem evalCoefficient_restrictToAxisLine_lowDegreeEncoding (hline : line.kind = .axis)
    (h : Cube L.m → ScalarQ L) (t : ScalarQ L) :
    evalCoefficient (restrictToAxisLine L line (lowDegreeEncoding h)) t =
      MvPolynomial.eval (line.base + t • line.direction) (lowDegreeEncoding h) := by
  rw [← eval_polynomialOnLine line (lowDegreeEncoding h) t]
  unfold evalCoefficient restrictToAxisLine
  rw [Polynomial.eval_eq_sum_range'
    (Nat.lt_succ_of_le
      ((polynomialOnLine_lowDegreeEncoding_natDegree_le_one_of_axis
        L line hline h).trans L.hd)) t]
  exact Fin.sum_univ_eq_sum_range
    (fun i => (polynomialOnLine line (lowDegreeEncoding h)).coeff i * t ^ i)
    _

end

section

variable (P : AdmissibleParams) (W : PauliKind) (z : PauliSpace P)

/-- The honest axis-line measurement is the generalized Pauli basis
measurement coarse-grained by the degree-`d` restriction of `g_h` to the
canonical line carried by the question. -/
noncomputable def pauliALineMeasurement :
    Measurement (Fin (P.d + 1) → PauliScalar P) (PauliRegister P) :=
    (pauliBasisMeasurement W).postprocess fun h =>
    restrictToAxisLine P.toLdParams
      (aLineDescOf
        (ldALineCL P.toLdParams (pauliToLd P W z))) (lowDegreeEncoding h)

/-- The honest diagonal-line measurement is the generalized Pauli basis
measurement coarse-grained by the degree-`m d` restriction of `g_h` to the
canonical line carried by the question. -/
noncomputable def pauliDLineMeasurement :
    Measurement (Fin (P.m * P.d + 1) → PauliScalar P) (PauliRegister P) :=
    (pauliBasisMeasurement W).postprocess fun h =>
    restrictToLine
      (dLineDescOf
        (ldDLineCL P.toLdParams (pauliToLd P W z))) (lowDegreeEncoding h)

end

/-! ### The commutation law of the honest pair -/

/-- The commutation law `𝒪_A 𝒪_B = (-1)^γ 𝒪_B 𝒪_A` of the proof of
`lem:pauli-completeness`, with `γ` the phase bit `eq:gamma-value`.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1316-1330`. -/
theorem obsOf_pauliTraceMeasurement_mul_comm (P : AdmissibleParams) (z : PauliSpace P) :
    obsOf (pauliTraceMeasurement .X (pauliXBlock z) (pauliRXBlock z)) *
        obsOf (pauliTraceMeasurement .Z (pauliZBlock z) (pauliRZBlock z)) =
      phaseSign (pauliPairGamma P z) •
        (obsOf (pauliTraceMeasurement .Z (pauliZBlock z) (pauliRZBlock z)) *
          obsOf (pauliTraceMeasurement .X (pauliXBlock z) (pauliRXBlock z))) := by
  rw [obsOf_pauliTraceMeasurement, obsOf_pauliTraceMeasurement, tauObservable_X_mul_Z]
  rfl

/-- If the phase bit `γ` of `eq:gamma-value` is nonzero, the two honest Pair/W
observables anticommute.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1316-1330`. -/
theorem obsOf_pauliTraceMeasurement_anticommute {P : AdmissibleParams}
    {z : PauliSpace P} (hgamma : pauliPairGamma P z ≠ 0) :
    obsOf (pauliTraceMeasurement .X (pauliXBlock z) (pauliRXBlock z)) *
        obsOf (pauliTraceMeasurement .Z (pauliZBlock z) (pauliRZBlock z)) =
      -(obsOf (pauliTraceMeasurement .Z (pauliZBlock z) (pauliRZBlock z)) *
        obsOf (pauliTraceMeasurement .X (pauliXBlock z) (pauliRXBlock z))) := by
  rw [obsOf_pauliTraceMeasurement_mul_comm]
  rcases zmod_two_eq_zero_or_one (pauliPairGamma P z) with h | h
  · exact absurd h hgamma
  · simp [h, phaseSign]

/-! ### The pointwise Magic Square measurement -/

/-- The nine cell measurements obtained from the anticommuting Pair/X and
Pair/Z observables at a question with nonzero phase bit. -/
noncomputable def pauliMagicCellMeasurement {P : AdmissibleParams}
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0) :
    Fin 9 → Measurement (ZMod 2) (PauliRegister P × ZMod 2) :=
  let A := pauliTraceMeasurement .X (pauliXBlock z) (pauliRXBlock z)
  let B := pauliTraceMeasurement .Z (pauliZBlock z) (pauliRZBlock z)
  msCellMeasurement (obsOf A) (obsOf B)
    (obsOf_conjTranspose A (pauliTraceMeasurement_projective P .X _ _))
    (obsOf_conjTranspose B (pauliTraceMeasurement_projective P .Z _ _))
    (obsOf_sq A (pauliTraceMeasurement_projective P .X _ _))
    (obsOf_sq B (pauliTraceMeasurement_projective P .Z _ _))
    (obsOf_pauliTraceMeasurement_anticommute hgamma)

/-- Every Pauli-induced Magic Square cell measurement is projective. -/
theorem pauliMagicCellMeasurement_projective {P : AdmissibleParams}
    {z : PauliSpace P} (hgamma : pauliPairGamma P z ≠ 0) (j : Fin 9) :
    MIPStarRE.QPBT.Measurement.IsProjective
      (pauliMagicCellMeasurement z hgamma j) := by
  simp only [pauliMagicCellMeasurement]
  apply msCellMeasurement_projective

/-- Cell effects belonging to one Magic Square constraint commute. -/
theorem pauliMagicCellMeasurement_commute {P : AdmissibleParams}
    {z : PauliSpace P} (hgamma : pauliPairGamma P z ≠ 0)
    (i : Fin 6) (k l : Fin 3) (a b : ZMod 2) :
    Commute
      ((pauliMagicCellMeasurement z hgamma (msConstraintVars i k)).effect a)
      ((pauliMagicCellMeasurement z hgamma (msConstraintVars i l)).effect b) := by
  exact reflectionEffect_commute
    (msConstraintObservable_commute _ _
      (obsOf_sq _ (pauliTraceMeasurement_projective P .X _ _))
      (obsOf_sq _ (pauliTraceMeasurement_projective P .Z _ _))
      (obsOf_pauliTraceMeasurement_anticommute hgamma) i k l) a b

/-- The Magic Square measurement family used at a Pauli question with nonzero
phase bit. -/
noncomputable def pauliMagicMeasurement {P : AdmissibleParams}
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0) :
    MsType → Measurement MsAnswer (PauliRegister P × ZMod 2) :=
  msStrategyMeasurement (pauliMagicCellMeasurement z hgamma)
    (pauliMagicCellMeasurement_projective hgamma)
    (pauliMagicCellMeasurement_commute hgamma)

/-- Every effect of the Pauli-induced Magic Square measurement is symmetric. -/
theorem pauliMagicMeasurement_effect_transpose (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z ≠ 0)
    (x : MsType) (a : MsAnswer) :
    ((pauliMagicMeasurement z hgamma x).effect a)ᵀ =
      (pauliMagicMeasurement z hgamma x).effect a := by
  apply msStrategyMeasurement_effect_transpose
  simp only [pauliMagicCellMeasurement]
  apply msCellMeasurement_transpose
  · rw [obsOf_pauliTraceMeasurement]
    apply tauObservable_transpose
  · rw [obsOf_pauliTraceMeasurement]
    apply tauObservable_transpose

/-- The Pauli-induced Magic Square measurements commute on an incident
constraint-variable pair. -/
theorem pauliMagicMeasurement_incident_commute {P : AdmissibleParams}
    {z : PauliSpace P} (hgamma : pauliPairGamma P z ≠ 0)
    (i : Fin 6) (k : Fin 3) (a b : MsAnswer) :
    Commute ((pauliMagicMeasurement z hgamma (.constraint i)).effect a)
      ((pauliMagicMeasurement z hgamma
        (.var (msConstraintVars i k))).effect b) := msStrategyMeasurement_incident_commute _ _ i k a b

/-- The distinguished variable effects of the Pauli-induced Magic Square
measurement are the tensor placements of the Pair/X and Pair/Z effects. -/
theorem pauliMagicMeasurement_var_effect {P : AdmissibleParams}
    {z : PauliSpace P} (hgamma : pauliPairGamma P z ≠ 0) (b : ZMod 2) :
    (pauliMagicMeasurement z hgamma (.var 0)).effect (.bit b) =
        heteroKron
          ((pauliTraceMeasurement .X (pauliXBlock z) (pauliRXBlock z)).effect b)
          (1 : Op (ZMod 2)) ∧
      (pauliMagicMeasurement z hgamma (.var 4)).effect (.bit b) =
        heteroKron
          ((pauliTraceMeasurement .Z (pauliZBlock z) (pauliRZBlock z)).effect b)
          (1 : Op (ZMod 2)) := by
  constructor
  · unfold pauliMagicMeasurement
    rw [msStrategyMeasurement_var_bit]
    change reflectionEffect
        (heteroKron
          (obsOf (pauliTraceMeasurement .X (pauliXBlock z) (pauliRXBlock z)))
          1) b = _
    rw [← MagicSquareRigidity.reflectionEffect_heteroKron_left,
      reflectionEffect_obsOf_measurement]
  · unfold pauliMagicMeasurement
    rw [msStrategyMeasurement_var_bit]
    change reflectionEffect
        (heteroKron
          (obsOf (pauliTraceMeasurement .Z (pauliZBlock z) (pauliRZBlock z)))
          1) b = _
    rw [← MagicSquareRigidity.reflectionEffect_heteroKron_left,
      reflectionEffect_obsOf_measurement]

/-! ### The Pair measurement in the case `γ = 0`

If the phase bit vanishes, the two honest Pair/W measurements commute and their
product is the Pair measurement `E^{Pair,ω}_{β_X, β_Z} = A_{β_X} B_{β_Z}` of
Equation `eq:pair-definition` in the proof of `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1331-1344`.
-/

/-- If the phase bit `γ` of `eq:gamma-value` vanishes, the two honest Pair/W
observables commute.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1316-1330`. -/
theorem obsOf_pauliTraceMeasurement_commute (P : AdmissibleParams)
    (z : PauliSpace P) (hgamma : pauliPairGamma P z = 0) :
    Commute (obsOf (pauliTraceMeasurement .X (pauliXBlock z) (pauliRXBlock z)))
      (obsOf (pauliTraceMeasurement .Z (pauliZBlock z) (pauliRZBlock z))) := by
  simp [commute_iff_eq, obsOf_pauliTraceMeasurement_mul_comm, hgamma, phaseSign]

/-- If the phase bit `γ` vanishes, the effects of the two honest Pair/W
measurements commute; this is the commutation assertion of the honest strategy
in the case `γ = 0`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1374-1382`. -/
theorem pauliTraceMeasurement_effect_commute {P : AdmissibleParams}
    {z : PauliSpace P} (hgamma : pauliPairGamma P z = 0) (a b : ZMod 2) :
    Commute ((pauliTraceMeasurement .X (pauliXBlock z) (pauliRXBlock z)).effect a)
      ((pauliTraceMeasurement .Z (pauliZBlock z) (pauliRZBlock z)).effect b) := by
  simp [pauliTraceMeasurement_effect_eq_reflectionEffect]
  apply reflectionEffect_commute
  rw [← obsOf_pauliTraceMeasurement P .X (pauliXBlock z) (pauliRXBlock z),
    ← obsOf_pauliTraceMeasurement P .Z (pauliZBlock z) (pauliRZBlock z)]
  solve_by_elim [obsOf_pauliTraceMeasurement_commute]

/-- The Pair effect `E^{Pair,ω}_{β_X, β_Z} = A_{β_X} B_{β_Z}` of Equation
`eq:pair-definition`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1331-1339`. -/
noncomputable def pauliPairEffect {P : AdmissibleParams} (z : PauliSpace P)
    (β : ZMod 2 × ZMod 2) : Op (PauliRegister P) :=
  (pauliTraceMeasurement .X (pauliXBlock z) (pauliRXBlock z)).effect β.1 *
    (pauliTraceMeasurement .Z (pauliZBlock z) (pauliRZBlock z)).effect β.2

/-- For `γ = 0` the Pair effects are projectors, being products of commuting
projectors.  Paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1331-1344`. -/
theorem pauliPairEffect_isProj {P : AdmissibleParams} {z : PauliSpace P}
    (hgamma : pauliPairGamma P z = 0) (β : ZMod 2 × ZMod 2) :
    IsProj (pauliPairEffect z β) :=
  IsStarProjection.mul (pauliTraceMeasurement_projective P .X _ _ β.1)
    (pauliTraceMeasurement_projective P .Z _ _ β.2)
    (pauliTraceMeasurement_effect_commute hgamma β.1 β.2)

/-- The Pair effects sum to the identity. -/
theorem sum_pauliPairEffect (P : AdmissibleParams) (z : PauliSpace P) :
    ∑ β : ZMod 2 × ZMod 2, pauliPairEffect z β = 1 := by
  calc _
      = ∑ a : ZMod 2, ∑ b : ZMod 2,
          (pauliTraceMeasurement .X (pauliXBlock z) (pauliRXBlock z)).effect a *
            (pauliTraceMeasurement .Z (pauliZBlock z) (pauliRZBlock z)).effect b :=
        Fintype.sum_prod_type _
    _ = ∑ a : ZMod 2,
          (pauliTraceMeasurement .X (pauliXBlock z) (pauliRXBlock z)).effect a *
            ∑ b : ZMod 2,
              (pauliTraceMeasurement .Z (pauliZBlock z) (pauliRZBlock z)).effect b :=
        Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
    _ = 1 := by
        simp [(pauliTraceMeasurement .Z (pauliZBlock z) (pauliRZBlock z)).sum_eq_one, (pauliTraceMeasurement .X (pauliXBlock z) (pauliRXBlock z)).sum_eq_one]

/-- The Pair measurement of Equation `eq:pair-definition` in the case `γ = 0`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1331-1344`,
blueprint `lem:pauli-completeness`. -/
noncomputable def pauliPairMeasurement {P : AdmissibleParams} (z : PauliSpace P)
    (hgamma : pauliPairGamma P z = 0) : Measurement (ZMod 2 × ZMod 2) (PauliRegister P) :=
  Measurement.ofSumEqOne (pauliPairEffect z)
    (fun β => (pauliPairEffect_isProj hgamma β).nonneg) (sum_pauliPairEffect P z)

end

end MIPStarRE.QPBT
