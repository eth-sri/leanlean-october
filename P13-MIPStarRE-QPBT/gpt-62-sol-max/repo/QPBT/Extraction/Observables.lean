module

public import QPBT.Algebra.Decoding
public import QPBT.Combining.Witnesses
public import QPBT.Extraction.Defs
public import QPBT.Test.MagicSquareTheorems.Rigidity.Reflections
public import QPBT.Quantum.ControlledUnitary

/-!
# Pulled-apart Pauli observables

This module constructs the measurements and observables used to pull the two
Pauli bases onto separate registers. The construction retains the distinct
local spaces of the two players and uses the binary basis fixed in the
canonical field model.

## References

The product form and observable relations formalize blueprint
`lem:tildew-product-form`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1415-1456`.
The swap identities formalize blueprint `lem:v-swap-conjugation`, from paper
lines 1687-1713.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.LDT.Preliminaries MIPStarRE.Quantum

noncomputable section

/-! ## Pulled-apart measurements and observables -/

namespace PauliKind

/-- Select the polynomial belonging to a Pauli basis from a joint polynomial
outcome. This is the marginalization used at paper
`14_analysis_of_the_pauli_basis_test.tex:1421-1423` and blueprint
`def:s-w-marginals`. -/
def selectPoly {P : AdmissibleParams} (W : PauliKind) : PolyPair P -> Poly P
  | pair => match W with
    | .X => pair.1
    | .Z => pair.2

end PauliKind

namespace GlobalPairWitness

/-- The single-basis marginal of the global polynomial-pair measurement.
This is blueprint
`def:s-w-marginals`, paper
`14_analysis_of_the_pauli_basis_test.tex:1421-1423`. -/
noncomputable def marginalPoly {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) :
    Measurement (Poly P) (S.ExpandedLocalSpace side) :=
  (w.Smeas side).postprocess W.selectPoly

/-- Evaluating a single-basis marginal is the same finite postprocessing as
evaluating the corresponding component of the joint polynomial outcome. This
is the coarse-graining in the proof of blueprint
`lem:qld-constructing-the-paulis-helper`, paper
`14_analysis_of_the_pauli_basis_test.tex:1626-1637`. -/
theorem marginalPoly_postprocess_eval {P : AdmissibleParams} {epsilon deltaG : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
    (side : PlayerSide) (W : PauliKind) (point : PauliPoint P) :
    (w.marginalPoly side W).postprocess (fun g => evalPoly g point) =
      (w.Smeas side).postprocess (evalAt W point) := by
  rw [marginalPoly, MIPStarRE.Quantum.Measurement.postprocess_comp]
  cases W <;> rfl

/-- The single-basis marginal remains a projective measurement. This is the
projectivity assertion implicit in blueprint
`def:s-w-marginals`, paper
`14_analysis_of_the_pauli_basis_test.tex:1421-1423`. Finite postprocessing
preserves projectivity, independently of the construction of the joint
measurement. -/
theorem marginalPoly_isProjective {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) :
    Measurement.IsProjective (w.marginalPoly side W) := by
  exact SandwichProduct.postprocess_isProjective
    (w.Smeas side) (w.projective side) W.selectPoly

end GlobalPairWitness

section

variable {P : AdmissibleParams} {ε δ : ℝ}
    {S : ProjectiveSetting P ε} (w : GlobalPairWitness S δ)
    (side : PlayerSide) (W : PauliKind) (u : PauliRegister P)
include P ε δ S w side W u

/-- The pulled-apart measurement subtracts the Pauli dot product from the
polynomial marginal's decoded label. -/
noncomputable def tildeMMeasurement :
    Measurement (PauliScalar P) (ExtractionBlock P (S.LocalSpace side)) :=
  (tensorMeasurement (w.marginalPoly side W) (pauliRegisterMeas W)).postprocess
    (fun gh => dotProduct (decodeFq gh.1) u - dotProduct gh.2 u)

/-- The effect of the pulled-apart measurement. -/
noncomputable abbrev tildeM (a : PauliScalar P) :=
  (tildeMMeasurement w side W u).effect a

/-- The pulled-apart effect expressed using dot-product projectors. -/
theorem tildeM_eq_sum (a : PauliScalar P) :
    tildeM w side W u a = ∑ g : Poly P, heteroKron ((w.marginalPoly side W).effect g)
      (tauDotProj W u (dotProduct (decodeFq g) u - a)) := by
  classical
  have hlabel (g : Poly P) (h : PauliRegister P) :
      dotProduct (decodeFq g) u - dotProduct h u = a ↔
        dotProduct h u = dotProduct (decodeFq g) u - a := by
    constructor <;> intro heq <;> linear_combination -heq
  simp only [tildeM, tildeMMeasurement, Measurement.postprocess_effect, Finset.sum_filter,
    Fintype.sum_prod_type, tensorMeasurement, Measurement.ofSumEqOne, pauliRegisterMeas,
    tauDotProj, bracketOp, DistanceCalculus.heteroKron_finset_sum_right, hlabel]
  simp_rw [apply_ite, heteroKron_zero_right]

end

section

variable {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide) (W : PauliKind) (u : PauliRegister P)
    (j : Fin P.model.basisDim)
include P epsilon delta S w side W u j

/-- The binary observable obtained from the trace coarse-graining of `tildeM`.
This is Equation `eq:def-tildewj` in blueprint
`def:tilde-w-observables`, paper
`14_analysis_of_the_pauli_basis_test.tex:1437-1442`. -/
noncomputable def tildeObs : Op (ExtractionBlock P (S.LocalSpace side)) :=
  ∑ a : PauliScalar P,
    phaseSign (fixedBinTrace P.model (P.model.basis j * a)) •
      tildeM w side W u a

/-- Product form of the pulled-apart observable, Equation
`eq:tildewj-product-form` of `lem:tildew-product-form`. Blueprint
`lem:tildew-product-form`; paper
`14_analysis_of_the_pauli_basis_test.tex:1442-1450`. The finite Fourier
regrouping uses `tauObservable_eq_sum_pauliProj` and the definitions of both
marginalizations, independently of dot-product projectivity or consistency
estimates. -/
theorem tildeObs_eq_heteroKron :
    tildeObs w side W u j =
      heteroKron
        (∑ pair : PolyPair P,
          phaseSign (fixedBinTrace P.model
            (P.model.basis j * dotProduct (decodeFq (W.selectPoly pair)) u)) •
            (w.Smeas side).effect pair)
        (tauObservable W (P.model.basis j • u)) := by
  classical
  let c := P.model.basis j
  let χ (a : PauliScalar P) := phaseSign (fixedBinTrace P.model (c * a))
  have hsub (a b : PauliScalar P) : χ (a - b) = χ a * χ b := by
    dsimp only [χ]
    rw [mul_sub, fixedBinTrace, map_sub]
    have h (x y : ZMod 2) : phaseSign (x - y) = phaseSign x * phaseSign y := by
      rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two, phaseSign_add]
    exact h _ _
  have hdot (h : PauliRegister P) :
      phaseSign (binTrace (PauliScalar P) (dotProduct (c • u) h)) = χ (dotProduct h u) := by
    simp [χ, fixedBinTrace, smul_dotProduct, smul_eq_mul, dotProduct_comm u h]
  have hMarg := Measurement.sum_smul_postprocess (w.Smeas side) W.selectPoly
    (fun g => χ (dotProduct (decodeFq g) u))
  change (∑ a, χ a • (tildeMMeasurement w side W u).effect a) =
    heteroKron (∑ pair, χ (dotProduct (decodeFq (W.selectPoly pair)) u) • (w.Smeas side).effect pair)
      (tauObservable W (c • u))
  rw [← hMarg, tildeMMeasurement, Measurement.sum_smul_postprocess, Fintype.sum_prod_type,
    tauObservable_eq_sum_pauliProj]
  simp only [DistanceCalculus.heteroKron_finset_sum_left, DistanceCalculus.heteroKron_finset_sum_right,
    hdot, tensorMeasurement, Measurement.ofSumEqOne, pauliRegisterMeas, hsub]
  rw [Finset.sum_comm]
  simp only [GlobalPairWitness.marginalPoly, heteroKron, Matrix.kronecker, Matrix.smul_kronecker,
    Matrix.kronecker_smul, smul_smul, mul_comm]

end

/-! ## Swap conjugation -/

/-- Each crossed Pauli product is unitary, by the two involution identities
used at paper `14_analysis_of_the_pauli_basis_test.tex:1687-1699`. -/
private theorem swapPauli_mul_conjTranspose {P : AdmissibleParams}
    (pair : PolyPair P) :
    (tauObservable .X (decodeFq pair.2) * tauObservable .Z (decodeFq pair.1)) *
        (tauObservable .X (decodeFq pair.2) * tauObservable .Z (decodeFq pair.1))ᴴ = 1 := by
  rw [Matrix.conjTranspose_mul, tauObservable_conjTranspose,
    tauObservable_conjTranspose, ← Matrix.mul_assoc,
    Matrix.mul_assoc (tauObservable .X (decodeFq pair.2)), tauObservable_sq,
    Matrix.mul_one, tauObservable_sq]

section

variable {P : AdmissibleParams}
    (pair : PolyPair P) (W : PauliKind)
include P pair W

/-- The crossed Pauli factors acquire the phase determined by the selected
polynomial. This is the commutation identity used at paper
`14_analysis_of_the_pauli_basis_test.tex:1701-1713`. -/
private theorem swapPauli_mul_tauObservable (u : PauliRegister P) :
    (tauObservable .X (decodeFq pair.2) * tauObservable .Z (decodeFq pair.1)) *
        tauObservable W u =
      phaseSign (fixedBinTrace P.model
        (dotProduct (decodeFq (W.selectPoly pair)) u)) •
        (tauObservable W u *
          (tauObservable .X (decodeFq pair.2) * tauObservable .Z (decodeFq pair.1))) := by
  cases W with
  | X =>
      have hcomm : tauObservable .X (decodeFq pair.2) * tauObservable .X u =
          tauObservable .X u * tauObservable .X (decodeFq pair.2) := by
        rw [tauObservable_mul, tauObservable_mul, add_comm]
      have hcross := congrArg
        (fun A : Op (PauliRegister P) =>
          phaseSign (binTrace (PauliScalar P) (dotProduct u (decodeFq pair.1))) • A)
        (tauObservable_X_mul_Z u (decodeFq pair.1))
      simp only [smul_smul, phaseSign_mul_self, one_smul] at hcross
      simp only [PauliKind.selectPoly, fixedBinTrace]
      rw [dotProduct_comm (decodeFq pair.1) u]
      calc
        _ = tauObservable .X (decodeFq pair.2) *
            (tauObservable .Z (decodeFq pair.1) * tauObservable .X u) :=
          Matrix.mul_assoc _ _ _
        _ = _ := by
          rw [← hcross, Matrix.mul_smul, ← Matrix.mul_assoc, hcomm, Matrix.mul_assoc]
  | Z =>
      have hcomm : tauObservable .Z (decodeFq pair.1) * tauObservable .Z u =
          tauObservable .Z u * tauObservable .Z (decodeFq pair.1) := by
        rw [tauObservable_mul, tauObservable_mul, add_comm]
      simp only [PauliKind.selectPoly, fixedBinTrace]
      calc
        _ = tauObservable .X (decodeFq pair.2) *
            (tauObservable .Z (decodeFq pair.1) * tauObservable .Z u) :=
          Matrix.mul_assoc _ _ _
        _ = _ := by
          rw [hcomm, ← Matrix.mul_assoc, tauObservable_X_mul_Z,
            Matrix.smul_mul, Matrix.mul_assoc]

/-- Conjugating a Pauli observable by the crossed Pauli factors multiplies it
by the selected binary phase, as in paper
`14_analysis_of_the_pauli_basis_test.tex:1701-1713`. -/
private theorem swapPauli_conj_tauObservable (u : PauliRegister P) :
    conjBy (tauObservable .X (decodeFq pair.2) * tauObservable .Z (decodeFq pair.1))
        (tauObservable W u) =
      phaseSign (fixedBinTrace P.model
        (dotProduct (decodeFq (W.selectPoly pair)) u)) • tauObservable W u := by
  rw [conjBy, swapPauli_mul_tauObservable, Matrix.smul_mul, Matrix.mul_assoc,
    swapPauli_mul_conjTranspose, Matrix.mul_one]

/-- Fourier inversion turns the Pauli conjugation phase into a translation of
the projector label. This is the projector identity used at paper
`14_analysis_of_the_pauli_basis_test.tex:1805-1822`. -/
private theorem swapPauli_conj_pauliProj (h : PauliRegister P) :
    conjBy (tauObservable .X (decodeFq pair.2) * tauObservable .Z (decodeFq pair.1))
        (pauliProj W h) =
      pauliProj W (h + decodeFq (W.selectPoly pair)) := by
  classical
  rw [pauliProj_eq_avg_tauObservable, conjBy, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sum, Finset.sum_mul, pauliProj_eq_avg_tauObservable]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [Matrix.mul_smul, Matrix.smul_mul]
  change _ • conjBy _ _ = _
  rw [swapPauli_conj_tauObservable, smul_smul]
  congr 1
  rw [fixedBinTrace, ← phaseSign_add, ← map_add,
    dotProduct_comm (decodeFq (W.selectPoly pair)) u, dotProduct_add]

/-- Translation of the Pauli label translates its dot-product outcome. This
is the finite reindexing in paper
`14_analysis_of_the_pauli_basis_test.tex:1805-1822`; it does not require a
polynomial to be in the image of the low-degree encoding. -/
private theorem swapPauli_conj_tauDotProj (u : PauliRegister P) (a : PauliScalar P) :
    conjBy (tauObservable .X (decodeFq pair.2) * tauObservable .Z (decodeFq pair.1))
        (tauDotProj W u a) =
      tauDotProj W u (a + dotProduct (decodeFq (W.selectPoly pair)) u) := by
  classical
  simp only [tauDotProj, bracketOp, conjBy, Matrix.mul_sum, Finset.sum_mul]
  change (∑ h ∈ Finset.univ.filter (fun h => dotProduct h u = a),
    conjBy (tauObservable .X (decodeFq pair.2) * tauObservable .Z (decodeFq pair.1))
      (pauliProj W h)) = _
  simp_rw [swapPauli_conj_pauliProj]
  apply Finset.sum_equiv (Equiv.addRight (decodeFq (W.selectPoly pair)))
  · intro h
    simp [add_dotProduct]
  · intro h _
    rfl

end

section

variable {P : AdmissibleParams} {epsilon delta : ℝ}
    {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S delta)
    (side : PlayerSide)
include P epsilon delta S w side

/-- The swap map built from the global polynomial-pair measurement, with the
crossed decoded arguments required by `def:v-swap-unitary`. Blueprint
`def:v-swap-unitary`; paper
`14_analysis_of_the_pauli_basis_test.tex:1687-1700`. -/
noncomputable def swapUnitary : Op (ExtractionBlock P (S.LocalSpace side)) :=
  ∑ pair : PolyPair P,
    heteroKron ((w.Smeas side).effect pair)
      (tauObservable .X (decodeFq pair.2) *
        tauObservable .Z (decodeFq pair.1))

/-- The swap map is a right unitary. This is the first exact unitarity
calculation of blueprint
`lem:v-swap-conjugation`, paper
`14_analysis_of_the_pauli_basis_test.tex:1687-1699`.

Projectivity and completeness of `w.Smeas side` reduce the product to its
diagonal outcomes. The two Pauli involutions then cancel in reverse order. -/
theorem swapUnitary_mul_conjTranspose :
    swapUnitary w side * (swapUnitary w side)ᴴ = 1 := by
  classical
  apply sum_heteroKron_mul_conjTranspose (w.Smeas side) (w.projective side)
  exact swapPauli_mul_conjTranspose

/-- The swap map is a left unitary. This is the reverse exact unitarity
calculation implicit in blueprint
`lem:v-swap-conjugation`, paper
`14_analysis_of_the_pauli_basis_test.tex:1687-1699`.

For finite square matrices, the right inverse identity also gives the left
inverse identity. -/
theorem conjTranspose_mul_swapUnitary :
    (swapUnitary w side)ᴴ * swapUnitary w side = 1 := mul_eq_one_comm.mp (swapUnitary_mul_conjTranspose w side)

/-- Conjugation by the swap map acts separately on each joint outcome. This
is the diagonal-projector reduction at paper
`14_analysis_of_the_pauli_basis_test.tex:1701-1713,1805-1822`. -/
private theorem swapUnitary_conj_controlled
    (R : PolyPair P → Op (PauliRegister P)) :
    conjBy (swapUnitary w side)
        (∑ pair, heteroKron ((w.Smeas side).effect pair) (R pair)) =
      ∑ pair, heteroKron ((w.Smeas side).effect pair)
        (conjBy (tauObservable .X (decodeFq pair.2) *
          tauObservable .Z (decodeFq pair.1)) (R pair)) := by
  have hself (pair : PolyPair P) :
      ((w.Smeas side).effect pair)ᴴ = (w.Smeas side).effect pair :=
    (w.projective side pair).isSelfAdjoint
  simp_all [conjBy, swapUnitary, Matrix.conjTranspose_sum, heteroKron_conjTranspose, hself, sum_heteroKron_mul_sum_heteroKron (w.Smeas side) (w.projective side)]

/-- Exact conjugation of a pulled-apart observable by the swap map. This is
Equation `eq:v-swap-obs-conjugation` in `lem:v-swap-conjugation`, blueprint
`eq:v-swap-obs-conjugation`, paper
`14_analysis_of_the_pauli_basis_test.tex:1701-1713`.

The product form and diagonal projector reduction leave two copies of the
same binary phase, whose product is one. -/
theorem swapUnitary_conj_tildeObs (W : PauliKind)
    (u : PauliRegister P) (j : Fin P.model.basisDim) :
    conjBy (swapUnitary w side) (tildeObs w side W u j) =
      heteroKron (1 : Op (S.ExpandedLocalSpace side))
        (tauObservable W (P.model.basis j • u)) := by
  classical
  rw [tildeObs_eq_heteroKron, DistanceCalculus.heteroKron_finset_sum_left]
  simp_rw [heteroKron_smul_left,
    ← heteroKron_smul_right]
  rw [swapUnitary_conj_controlled]
  have hcancel (pair : PolyPair P) :
      conjBy (tauObservable .X (decodeFq pair.2) * tauObservable .Z (decodeFq pair.1))
        (phaseSign (fixedBinTrace P.model
          (P.model.basis j * dotProduct (decodeFq (W.selectPoly pair)) u)) •
            tauObservable W (P.model.basis j • u)) =
        tauObservable W (P.model.basis j • u) := by
    rw [conjBy, Matrix.mul_smul, Matrix.smul_mul]
    change _ • conjBy _ _ = _
    rw [swapPauli_conj_tauObservable, smul_smul]
    have hdot : dotProduct (decodeFq (W.selectPoly pair)) (P.model.basis j • u) =
        P.model.basis j * dotProduct (decodeFq (W.selectPoly pair)) u := by
      rw [dotProduct_smul, smul_eq_mul]
    rw [hdot, phaseSign_mul_self, one_smul]
  simp_rw [hcancel]
  rw [← DistanceCalculus.heteroKron_finset_sum_left, (w.Smeas side).sum_eq_one]

/-- Exact conjugation of a pulled-apart point effect by the swap map. This is
Equation `eq:qld-unitary-6` in `lem:v-swap-conjugation`, blueprint
`eq:qld-unitary-6`; its calculation occurs at paper
`14_analysis_of_the_pauli_basis_test.tex:1805-1822`.

Conjugation translates each Pauli projector and its dot-product constraint.
The two copies of the decoded label cancel in characteristic two. The final
identification is the encoding identity h · ind_m(u) = g_h(u) on indicator
vectors, not an unrestricted decoder interpolation identity. -/
theorem swapUnitary_conj_tildeM (W : PauliKind)
    (u : PauliPoint P) (a : PauliScalar P) :
    conjBy (swapUnitary w side) (tildeM w side W (indicatorVec u) a) =
      heteroKron (1 : Op (S.ExpandedLocalSpace side))
        (bracketOp (pauliProj W) (fun h => lowDegreeEnc h u) a) := by
  classical
  have hM : tildeM w side W (indicatorVec u) a =
      ∑ pair : PolyPair P, heteroKron ((w.Smeas side).effect pair)
        (tauDotProj W (indicatorVec u)
          (dotProduct (decodeFq (W.selectPoly pair)) (indicatorVec u) - a)) := by
    simp only [tildeM_eq_sum, GlobalPairWitness.marginalPoly, Measurement.postprocess_effect,
      DistanceCalculus.heteroKron_finset_sum_left, Finset.sum_fiberwise_apply]
  rw [hM, swapUnitary_conj_controlled]
  simp_rw [swapPauli_conj_tauDotProj]
  have hcancel (b : PauliScalar P) : b - a + b = a := by
    letI :=
      (Algebra.charP_iff (ZMod 2) (PauliScalar P) 2).mp (ZMod.charP 2)
    rw [sub_eq_add_neg, CharTwo.neg_eq, add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  simp_rw [hcancel]
  rw [← DistanceCalculus.heteroKron_finset_sum_left, (w.Smeas side).sum_eq_one]
  congr 1
  simp only [tauDotProj, bracketOp, lowDegreeEnc_eq_dotProduct]

end

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε δ : ℝ} (S : ProjectiveSetting P ε)

/-- The simultaneous swaps on the two extraction blocks. -/
abbrev swapOperator (w : GlobalPairWitness S δ) :=
  S.placeBoth (swapUnitary w .alice) (swapUnitary w .bob)

/-- The expanded strategy state after the two swaps. -/
abbrev swappedState (w : GlobalPairWitness S δ) :=
  applyOperatorToState (S.swapOperator w) S.psiHat

/-- The total-Pauli effect after placement and conjugation by its local swap. -/
abbrev swapPauliOp (w : GlobalPairWitness S δ) (side : PlayerSide) (W : PauliKind)
    (h : PauliRegister P) : Op S.ExpandedSpace :=
  conjBy (S.placeSide side (swapUnitary w side)) (S.placePlayer side ((S.pauliMeas side W).effect h))

/-- The ideal Pauli effect on the selected extracted register. -/
abbrev idealPauliOp (side : PlayerSide) (W : PauliKind) (h : PauliRegister P) : Op S.ExpandedSpace :=
  S.placeExtractedRegister side (pauliProj W h)

/-- The squared comparison of the swapped and ideal total-Pauli effects. -/
abbrev swapPauliDistance (w : GlobalPairWitness S δ) (aux : EuclideanSpace ℂ S.ExtractionAux)
    (side : PlayerSide) (W : PauliKind) : ℝ :=
  opFamilyDistSq (uniformDistribution Unit) (fun _ => S.swapPauliOp w side W)
    (fun _ => S.idealPauliOp side W) (S.idealExpState aux)

end ProjectiveSetting

end

end MIPStarRE.QPBT
