module

public import QPBT.Algebra.PauliTheorems
public import QPBT.Observables.Defs

/-!
# Expanded registers and point measurements

This module adjoins two EPR pairs to a heterogeneous Pauli-basis-test strategy,
records the four register placements used in the analysis, and defines the
expanded point observables and measurements. Fourier inversion identifies their
effects with a convolution of projectors and proves completeness and projectivity.

## References

The constructions formalize blueprint `def:expanded-state`,
`def:expanded-observables`, `def:expanded-point-measurement`, and
`def:expanded-point-trace-projection`. Their paper source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:367-418`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open MIPStarRE.LDT.Preliminaries

noncomputable section

/-- The six registers `AA'A''BB'B''`, retaining distinct Alice and Bob local
spaces. This is the register index type of `def:expanded-state`, paper
`14_analysis_of_the_pauli_basis_test.tex:367-372`, blueprint
`def:expanded-state`. -/
abbrev SixReg (P : AdmissibleParams) (ιA ιB : Type*) :=
  (ιA × (PauliRegister P × PauliRegister P)) ×
    (ιB × (PauliRegister P × PauliRegister P))

/-- Equality of six-register indices is supplied by classical decidability for
the register type. This is the index set of blueprint
`def:expanded-state`. -/
noncomputable instance sixRegDecidableEq (P : AdmissibleParams)
    (ιA ιB : Type*) : DecidableEq (SixReg P ιA ιB) :=
  Classical.decEq _

/-- Reassociate the tensor product of the strategy state and two EPR states
directly into register order `AA'A''BB'B''` for
`eq:def-psihat`, paper `14_analysis_of_the_pauli_basis_test.tex:367-372`. -/
def sixRegShuffle (P : AdmissibleParams) (ιA ιB : Type*) :
    (((ιA × ιB) × (PauliRegister P × PauliRegister P)) ×
        (PauliRegister P × PauliRegister P)) ≃ SixReg P ιA ιB where
  toFun p := ((p.1.1.1, (p.1.2.1, p.1.2.2)),
    (p.1.1.2, (p.2.1, p.2.2)))
  invFun p := (((p.1.1, p.2.1), (p.1.2.1, p.1.2.2)),
    (p.2.2.1, p.2.2.2))
  left_inv p := by rfl
  right_inv p := by rfl

/-- The four placements `AA'`, `BA''`, `BB'`, and `AB''` used explicitly in
the chapter-14 consistency statements. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`; blueprint
`def:symmetric-equivalents`. -/
inductive Placement where
  | AA'
  | BA''
  | BB'
  | AB''


/-- The strategy-player side supplying the local Hilbert space in each of the
four register placements at paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`. -/
@[reducible] def Placement.side : Placement → PlayerSide
  | .AA' => .alice
  | .BA'' => .bob
  | .BB' => .bob
  | .AB'' => .alice

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- A strategy-local register paired with one generalized-Pauli register. This
is the operator space in `def:expanded-observables`, paper
`14_analysis_of_the_pauli_basis_test.tex:374-382`. -/
abbrev ExpandedLocalSpace (S : ProjectiveSetting P ε) (side : PlayerSide) :=
  S.LocalSpace side × PauliRegister P

/-- The strategy state tensored with EPR states on `A'A''` and `B'B''`, in the
six-register order. This is `eq:def-psihat`, paper
`14_analysis_of_the_pauli_basis_test.tex:367-372`, blueprint
`eq:def-psihat`. -/
noncomputable def psiHat (S : ProjectiveSetting P ε) :
    EuclideanSpace ℂ (SixReg P S.toStrategy.ιA S.toStrategy.ιB) := by
  exact
    reindexState (sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
      (vecTensor
        (vecTensor S.toStrategy.ψ (eprState (PauliRegister P)))
        (eprState (PauliRegister P)))

/-- Place an operator on one of `AA'`, `BA''`, `BB'`, or `AB''`, with the
identity on all remaining registers. The input local space is determined by
the placement, so no equality between the player spaces is assumed. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`; blueprint
`def:symmetric-equivalents`. -/
noncomputable def place (S : ProjectiveSetting P ε) (p : Placement)
    (O : Op (S.ExpandedLocalSpace p.side)) :
    Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB) :=
  fun i j =>
    match p with
    | .AA' =>
        O (i.1.1, i.1.2.1) (j.1.1, j.1.2.1) *
          (1 : Op (PauliRegister P)) i.1.2.2 j.1.2.2 *
          (1 : Op S.toStrategy.ιB) i.2.1 j.2.1 *
          (1 : Op (PauliRegister P)) i.2.2.1 j.2.2.1 *
          (1 : Op (PauliRegister P)) i.2.2.2 j.2.2.2
    | .BA'' =>
        (1 : Op S.toStrategy.ιA) i.1.1 j.1.1 *
          (1 : Op (PauliRegister P)) i.1.2.1 j.1.2.1 *
          O (i.2.1, i.1.2.2) (j.2.1, j.1.2.2) *
          (1 : Op (PauliRegister P)) i.2.2.1 j.2.2.1 *
          (1 : Op (PauliRegister P)) i.2.2.2 j.2.2.2
    | .BB' =>
        (1 : Op S.toStrategy.ιA) i.1.1 j.1.1 *
          (1 : Op (PauliRegister P)) i.1.2.1 j.1.2.1 *
          (1 : Op (PauliRegister P)) i.1.2.2 j.1.2.2 *
          O (i.2.1, i.2.2.1) (j.2.1, j.2.2.1) *
          (1 : Op (PauliRegister P)) i.2.2.2 j.2.2.2
    | .AB'' =>
        O (i.1.1, i.2.2.2) (j.1.1, j.2.2.2) *
          (1 : Op (PauliRegister P)) i.1.2.1 j.1.2.1 *
          (1 : Op (PauliRegister P)) i.1.2.2 j.1.2.2 *
          (1 : Op S.toStrategy.ιB) i.2.1 j.2.1 *
          (1 : Op (PauliRegister P)) i.2.2.1 j.2.2.1

/-- The expanded observable
`W^r(u) tensor tau^W(r * ind_m(u))` on a selected player side. This is
Equation `eq:lc-23`, paper `14_analysis_of_the_pauli_basis_test.tex:374-382`,
blueprint `eq:lc-23`. -/
noncomputable def expObs (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (r : PauliScalar P) (u : Fin P.m → PauliScalar P) :
    Op (S.ExpandedLocalSpace side) :=
  heteroKron (S.pointObs side W r u)
    (tauObservable W (fun h => r * indicatorVec u h))

/-- The Fourier average defining the expanded point effect. This is the first
display of `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:384-418`, blueprint
`def:expanded-point-measurement`. -/
noncomputable def expPointOp (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) (a : PauliScalar P) :
    Op (S.ExpandedLocalSpace side) :=
  averageOperatorOverDistribution (uniformDistribution (PauliScalar P)) fun r =>
    phaseSign (fixedBinTrace P.model (a * r)) • S.expObs side W r u

/-- The Pauli-register projector onto labels whose low-degree encoding has
value `a` at `u`. This is Equation `eq:qld-point-obs-def`, paper
`14_analysis_of_the_pauli_basis_test.tex:389-394`, blueprint
`eq:qld-point-obs-def`. -/
noncomputable def tauPointProj (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (a : PauliScalar P) : Op (PauliRegister P) :=
  ∑ h ∈ Finset.univ.filter (fun h : PauliRegister P =>
      dotProduct h (indicatorVec u) = a),
    pauliProj W h

/-- The point coarse-graining of the generalized Pauli projectors is symmetric.
This is the EPR-transport identity used for the perfect ancilla consistency in
item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem tauPointProj_transpose (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (a : PauliScalar P) :
    (tauPointProj W u a)ᵀ = tauPointProj W u a := by
  simp [tauPointProj, Matrix.transpose_sum, pauliProj_transpose]

/-- Pauli point projectors belonging to distinct values are orthogonal, while
each projector is idempotent. This is the ancillary product calculation in
item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem tauPointProj_mul_tauPointProj (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (a b : PauliScalar P) :
    tauPointProj W u a * tauPointProj W u b =
      if a = b then tauPointProj W u a else 0 := by
  unfold tauPointProj
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.sum_eq_single e]
    · rw [pauliProj_mul_pauliProj, if_pos rfl]
    · intro f hf hfe
      rw [pauliProj_mul_pauliProj, if_neg hfe.symm]
    simp_all
  simp_all [Finset.sum_eq_zero, pauliProj_mul_pauliProj]

/-- The phase induced by the fixed binary trace is an additive character. -/
theorem phaseSign_fixedBinTrace_mul (x y : PauliScalar P) :
    phaseSign (fixedBinTrace P.model x) * phaseSign (fixedBinTrace P.model y) =
      phaseSign (fixedBinTrace P.model (x + y)) := by
  simp [fixedBinTrace, map_add, phaseSign_add, symm]

/-- The trace phase converts addition of coefficients to multiplication. -/
theorem phaseSign_fixedBinTrace_mul_add (x y r : PauliScalar P) :
    phaseSign (fixedBinTrace P.model (x * r)) *
        phaseSign (fixedBinTrace P.model (y * r)) =
      phaseSign (fixedBinTrace P.model ((x + y) * r)) := by
  simp [add_mul, phaseSign_fixedBinTrace_mul]

/-- Orthogonality of the fixed trace character over the Pauli scalar field. -/
theorem phaseSign_fixedBinTrace_expect (c : PauliScalar P) :
    (𝔼 r : PauliScalar P, phaseSign (fixedBinTrace P.model (c * r))) =
      if c = 0 then (1 : ℂ) else 0 := by
  simpa only [fixedBinTrace, phaseSign_eq_ffChar,
    MIPStarRE.LDT.Preliminaries.ffChar_apply, mul_comm c] using
    (fourier_fact_scalar (p := 2) (F := PauliScalar P) c)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Averaging a trace phase times an operator selects the zero coefficient. -/
theorem average_phaseSign_fixedBinTrace_smul
    (c : PauliScalar P) (A : Op ι) :
    averageOperatorOverDistribution (uniformDistribution (PauliScalar P))
        (fun r => phaseSign (fixedBinTrace P.model (c * r)) • A) =
      if c = 0 then A else 0 := by
  rw [averageOperatorOverDistribution_smul_const]
  simp only [uniformDistribution, Distribution.uniformOnFinset,
    Finset.mem_univ, if_true, Finset.card_univ, ← Finset.mul_sum]
  have havg := phaseSign_fixedBinTrace_expect (P := P) c
  rw [Fintype.expect_eq_sum_div_card] at havg
  have hcoeff :
      ((1 / (Fintype.card (PauliScalar P) : ℝ) : ℝ) : ℂ) *
          (∑ r : PauliScalar P,
            phaseSign (fixedBinTrace P.model (c * r))) =
        if c = 0 then (1 : ℂ) else 0 := by
    push_cast
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using havg
  simp_all

/-- Averaging three fixed trace characters imposes the convolution constraint. -/
theorem average_three_phaseSign_fixedBinTrace_smul
    (a x y : PauliScalar P) (A : Op ι) :
    averageOperatorOverDistribution (uniformDistribution (PauliScalar P))
        (fun r => phaseSign (fixedBinTrace P.model (a * r)) •
          (phaseSign (fixedBinTrace P.model (x * r)) •
            (phaseSign (fixedBinTrace P.model (y * r)) • A))) =
      if x + y = a then A else 0 := by
  haveI : CharP (PauliScalar P) 2 :=
    (Algebra.charP_iff (ZMod 2) (PauliScalar P) 2).mp (ZMod.charP 2)
  have hzero : a + x + y = 0 ↔ x + y = a := by
    constructor
    · grind
    · grind
  calc
    averageOperatorOverDistribution (uniformDistribution (PauliScalar P))
        (fun r => phaseSign (fixedBinTrace P.model (a * r)) •
          (phaseSign (fixedBinTrace P.model (x * r)) •
            (phaseSign (fixedBinTrace P.model (y * r)) • A))) =
      averageOperatorOverDistribution (uniformDistribution (PauliScalar P))
        (fun r => phaseSign (fixedBinTrace P.model ((a + x + y) * r)) • A) := by
          grind [averageOperatorOverDistribution_congr, smul_smul, phaseSign_fixedBinTrace_mul_add]
    _ = if a + x + y = 0 then A else 0 :=
      average_phaseSign_fixedBinTrace_smul (a + x + y) A
    _ = if x + y = a then A else 0 := if_congr hzero rfl rfl

/-- A scalar in the indicator vector factors out of the dot product. -/
theorem dot_smul_indicator (r : PauliScalar P)
    (u : Fin P.m → PauliScalar P) (e : PauliRegister P) :
    dotProduct (fun h => r * indicatorVec u h) e =
      dotProduct e (indicatorVec u) * r := by
  change dotProduct (r • indicatorVec u) e = _
  rw [smul_dotProduct, dotProduct_comm, smul_eq_mul, mul_comm]

/-- Tensor products distribute over the sums in both factors. -/
theorem heteroKron_sum_sum {α β ι κ : Type*}
    [Fintype α] [Fintype β] (A : α → Op ι) (B : β → Op κ) :
    heteroKron (∑ x, A x) (∑ y, B y) =
      ∑ x, ∑ y, heteroKron (A x) (B y) := by
  rw [DistanceCalculus.heteroKron_finset_sum_left]
  exact Finset.sum_congr rfl fun x _ =>
    DistanceCalculus.heteroKron_finset_sum_right _ _ _

/-- Scalars in the two tensor factors act successively on their tensor product. -/
theorem heteroKron_smul_smul {ι κ : Type*}
    (c d : ℂ) (A : Op ι) (B : Op κ) :
    heteroKron (c • A) (d • B) = c • (d • heteroKron A B) := by
  unfold heteroKron Matrix.kronecker
  rw [Matrix.smul_kronecker, Matrix.kronecker_smul]

variable (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)

/-- The expanded point effect is the convolution of the strategy point
measurement and the Pauli-register point projection. This is the final display
of `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:395-418`. -/
theorem expPointOp_eq_convolution (a : PauliScalar P) :
    S.expPointOp side W u a =
      ∑ p ∈ Finset.univ.filter (fun p : PauliScalar P × PauliScalar P =>
          p.1 + p.2 = a),
        heteroKron ((S.pointMeas side W u).effect p.1)
          (tauPointProj W u p.2) := by
  rw [expPointOp]
  simp only [expObs, pointObs, tauObservable_eq_sum_pauliProj]
  simp_rw [dot_smul_indicator]
  calc
    averageOperatorOverDistribution (uniformDistribution (PauliScalar P))
        (fun r => phaseSign (fixedBinTrace P.model (a * r)) •
          heteroKron
            (∑ x, phaseSign (fixedBinTrace P.model (x * r)) •
              (S.pointMeas side W u).effect x)
            (∑ e, phaseSign (fixedBinTrace P.model
              (dotProduct e (indicatorVec u) * r)) • pauliProj W e)) =
      averageOperatorOverDistribution (uniformDistribution (PauliScalar P))
        (fun r => ∑ x, ∑ e,
          phaseSign (fixedBinTrace P.model (a * r)) •
            (phaseSign (fixedBinTrace P.model (x * r)) •
              (phaseSign (fixedBinTrace P.model
                (dotProduct e (indicatorVec u) * r)) •
                  heteroKron ((S.pointMeas side W u).effect x)
                    (pauliProj W e)))) := by
          simp [heteroKron_sum_sum, heteroKron_smul_smul, Finset.smul_sum]
    _ = ∑ x, ∑ e,
          if x + dotProduct e (indicatorVec u) = a then
            heteroKron ((S.pointMeas side W u).effect x) (pauliProj W e)
          else 0 := by
      simp [averageOperatorOverDistribution_sum, average_three_phaseSign_fixedBinTrace_smul]
    _ = ∑ p ∈ Finset.univ.filter (fun p : PauliScalar P × PauliScalar P =>
          p.1 + p.2 = a),
        heteroKron ((S.pointMeas side W u).effect p.1)
          (tauPointProj W u p.2) := by
      rw [Finset.sum_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x hx
      calc
        (∑ e, if x + dotProduct e (indicatorVec u) = a then
              heteroKron ((S.pointMeas side W u).effect x) (pauliProj W e)
            else 0) =
          ∑ y, ∑ e ∈ Finset.univ.filter
              (fun e : PauliRegister P => dotProduct e (indicatorVec u) = y),
            if x + dotProduct e (indicatorVec u) = a then
              heteroKron ((S.pointMeas side W u).effect x) (pauliProj W e)
            else 0 :=
          (Finset.sum_fiberwise Finset.univ
            (fun e : PauliRegister P => dotProduct e (indicatorVec u))
            (fun e => if x + dotProduct e (indicatorVec u) = a then
              heteroKron ((S.pointMeas side W u).effect x) (pauliProj W e)
            else 0)).symm
        _ = ∑ y, if x + y = a then
              heteroKron ((S.pointMeas side W u).effect x)
                (∑ e ∈ Finset.univ.filter
                  (fun e : PauliRegister P =>
                    dotProduct e (indicatorVec u) = y),
                  pauliProj W e)
            else 0 := by
          apply Finset.sum_congr rfl
          intro y hy
          by_cases hxy : x + y = a
          · rw [if_pos hxy, DistanceCalculus.heteroKron_finset_sum_right]
            apply Finset.sum_congr rfl
            simp_all
          simp_all [Finset.sum_eq_zero]

/-- Each point fiber is a sum of positive Pauli projectors. -/
theorem tauPointProj_nonneg (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (a : PauliScalar P) :
    0 ≤ tauPointProj W u a := by
  exact Finset.sum_nonneg fun e he =>
    Matrix.nonneg_iff_posSemidef.mpr (posSemidef_pauliProj W e)

/-- The point fibers partition the complete family of Pauli eigenspace projectors. -/
theorem sum_tauPointProj_eq_one (W : PauliKind)
    (u : Fin P.m → PauliScalar P) :
    ∑ a, tauPointProj W u a = 1 := by
  rw [show (∑ a, tauPointProj W u a) =
      ∑ e : PauliRegister P, pauliProj W e by
    exact Finset.sum_fiberwise Finset.univ
      (fun e : PauliRegister P => dotProduct e (indicatorVec u))
      (fun e => pauliProj W e)]
  exact sum_pauliProj_eq_one W

/-- The projective point measurement on one Pauli register obtained by
coarse-graining the generalized Pauli basis according to its value at `u`.
This is the ancillary measurement used in item 1 of `lem:qld-comm-cons`, paper
`eq:qld-point-obs-def` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:385-411`,
blueprint `def:ancillary-point-measurement`. -/
noncomputable def tauPointMeas (W : PauliKind)
    (u : Fin P.m → PauliScalar P) :
    Measurement (PauliScalar P) (PauliRegister P) :=
  Measurement.ofSumEqOne (tauPointProj W u) (by
    exact tauPointProj_nonneg W u) (by
    exact sum_tauPointProj_eq_one W u)


/-- The fine product measurement underlying the convolution definition of an
expanded point measurement. Its outcome records the strategy and Pauli point
values separately. Paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:390-411`,
blueprint `def:point-tau-measurement`. -/
noncomputable def pointTauMeas (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace side) :=
  Measurement.ofSumEqOne
    (fun p => heteroKron ((S.pointMeas side W u).effect p.1)
      ((tauPointMeas W u).effect p.2))
    (fun p => Quantum.kronecker_nonneg
      ((S.pointMeas side W u).pos p.1) ((tauPointMeas W u).pos p.2))
    (by
      rw [Fintype.sum_prod_type]
      calc
        (∑ x, ∑ y, heteroKron ((S.pointMeas side W u).effect x)
            (tauPointProj W u y)) =
            heteroKron (∑ x, (S.pointMeas side W u).effect x)
              (∑ y, tauPointProj W u y) := (heteroKron_sum_sum _ _).symm
        _ = 1 := by
          rw [(S.pointMeas side W u).sum_eq_one, sum_tauPointProj_eq_one]
          exact Matrix.one_kronecker_one)


/-- Expanded point effects are positive semidefinite. This is the positivity
obligation in `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:384-418`. -/
theorem expPointOp_nonneg (a : PauliScalar P) :
    0 ≤ S.expPointOp side W u a := by
  rw [expPointOp_eq_convolution]
  exact Finset.sum_nonneg fun p hp => Quantum.kronecker_nonneg
    ((S.pointMeas side W u).pos p.1) (tauPointProj_nonneg W u p.2)

/-- Expanded point effects sum to the identity. This is the completeness
obligation in `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:384-418`. -/
theorem expPointOp_sum_eq_one :
    ∑ a, S.expPointOp side W u a = 1 := by
  simp_rw [expPointOp_eq_convolution]
  calc
    (∑ a, ∑ p ∈ Finset.univ.filter
        (fun p : PauliScalar P × PauliScalar P => p.1 + p.2 = a),
      heteroKron ((S.pointMeas side W u).effect p.1)
        (tauPointProj W u p.2)) =
      ∑ p : PauliScalar P × PauliScalar P,
        heteroKron ((S.pointMeas side W u).effect p.1)
          (tauPointProj W u p.2) := by
      let f : PauliScalar P × PauliScalar P → PauliScalar P :=
        fun p => p.1 + p.2
      let A : PauliScalar P × PauliScalar P →
          Op (S.ExpandedLocalSpace side) := fun p =>
        heteroKron ((S.pointMeas side W u).effect p.1)
          (tauPointProj W u p.2)
      exact Finset.sum_fiberwise Finset.univ f A
    _ = heteroKron (∑ x, (S.pointMeas side W u).effect x)
        (∑ y, tauPointProj W u y) := by
      simp [Fintype.sum_prod_type, heteroKron_sum_sum, symm]
    _ = 1 := by
      rw [(S.pointMeas side W u).sum_eq_one,
        sum_tauPointProj_eq_one (P := P)]
      exact Matrix.one_kronecker_one

/-- The complete expanded point measurement on the chosen player and Pauli
register. Its effects are those of `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:384-418`, blueprint
`def:expanded-point-measurement`. -/
noncomputable def pointMeasExp (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    Measurement (PauliScalar P) (S.ExpandedLocalSpace side) :=
  Measurement.ofSumEqOne (S.expPointOp side W u)
    (S.expPointOp_nonneg side W u) (S.expPointOp_sum_eq_one side W u)

/-- The expanded point measurement is the addition postprocessing of its fine
strategy--Pauli product measurement. This is the data-processing presentation
used in item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:390-411`,
blueprint `lem:expanded-point-measurement-properties`. -/
theorem pointMeasExp_effect_eq_pointTauMeas_postprocess
    (a : PauliScalar P) :
    (S.pointMeasExp side W u).effect a =
      ((S.pointTauMeas side W u).postprocess (fun p => p.1 + p.2)).effect a :=
  expPointOp_eq_convolution S side W u a

/-- Expanded observables inherit the additive representation law. -/
theorem expObs_mul (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (r s : PauliScalar P)
    (u : Fin P.m → PauliScalar P) :
    S.expObs side W r u * S.expObs side W s u =
      S.expObs side W (r + s) u := by
  calc
    S.expObs side W r u * S.expObs side W s u =
        heteroKron
          (S.pointObs side W r u * S.pointObs side W s u)
          (tauObservable W (fun h => r * indicatorVec u h) *
            tauObservable W (fun h => s * indicatorVec u h)) := by
      exact (Matrix.mul_kronecker_mul
        (S.pointObs side W r u) (S.pointObs side W s u)
        (tauObservable W (fun h => r * indicatorVec u h))
        (tauObservable W (fun h => s * indicatorVec u h))).symm
    _ = heteroKron (S.pointObs side W (r + s) u)
        (tauObservable W ((fun h => r * indicatorVec u h) +
          (fun h => s * indicatorVec u h))) := by
      rw [pointObs_mul, tauObservable_mul]
    _ = S.expObs side W (r + s) u := by
      congr 2
      grind [Pi.add_apply]

/-- Idempotence of the expanded point effect, the idempotence half of projectivity
in `def:expanded-point-measurement`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:384-418`. -/
theorem expPointOp_mul_self (a : PauliScalar P) :
    S.expPointOp side W u a * S.expPointOp side W u a =
      S.expPointOp side W u a := by
  let D := uniformDistribution (PauliScalar P)
  let F : PauliScalar P → Op (S.ExpandedLocalSpace side) := fun r =>
    phaseSign (fixedBinTrace P.model (a * r)) • S.expObs side W r u
  calc
    averageOperatorOverDistribution D F * averageOperatorOverDistribution D F =
        averageOperatorOverDistribution D
          (fun r => F r * averageOperatorOverDistribution D F) := by
      simpa using (averageOperatorOverDistribution_mul_left_right D
        1 (averageOperatorOverDistribution D F) F).symm
    _ = averageOperatorOverDistribution D
          (fun r => averageOperatorOverDistribution D (fun s => F r * F s)) := by
      apply averageOperatorOverDistribution_congr
      intro r
      simpa using
        (averageOperatorOverDistribution_mul_left_right D (F r) 1 F).symm
    _ = averageOperatorOverDistribution D
          (fun r => averageOperatorOverDistribution D (fun s => F (r + s))) := by
      apply averageOperatorOverDistribution_congr
      intro r
      grind [Matrix.smul_mul, Matrix.mul_smul, smul_smul, expObs_mul, mul_add, phaseSign_fixedBinTrace_mul]
    _ = averageOperatorOverDistribution D
          (fun _ => averageOperatorOverDistribution D F) := by
      apply averageOperatorOverDistribution_congr
      intro r
      exact (averageOperatorOverDistribution_uniform_equiv
        ((Equiv.addLeft r).symm) F).symm
    _ = averageOperatorOverDistribution D F := by
      exact averageOperatorOverDistribution_const_of_isProbability D
        (uniformDistribution_isProbability (PauliScalar P)) _

/-- A Fourier coefficient of the expanded representation is a projection. -/
theorem expPointOp_isProj (a : PauliScalar P) : IsProj (S.expPointOp side W u a) := by
  refine isStarProjection_iff'.2 ⟨expPointOp_mul_self S side W u a, ?_⟩
  exact (Matrix.nonneg_iff_posSemidef.mp (S.expPointOp_nonneg side W u a)).isHermitian.eq

/-- The expanded point measurement is projective, as asserted after the
convolution formula in `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:395-418`. -/
theorem pointMeasExp_isProjective :
    MIPStarRE.QPBT.Measurement.IsProjective (S.pointMeasExp side W u) := by
  intro a
  change IsProj (S.expPointOp side W u a)
  simp [expPointOp_isProj]

end ProjectiveSetting

end

end MIPStarRE.QPBT
