module

public import QPBT.Algebra.PauliTheorems
public import QPBT.Observables.Defs
public import QPBT.Games.DistanceTheorems
public import Mathlib.LinearAlgebra.Matrix.Reindex

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
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-- The four placements `AA'`, `BA''`, `BB'`, and `AB''` used explicitly in
the chapter-14 consistency statements. Paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`; blueprint
`def:symmetric-equivalents`. -/
inductive Placement where
  | AA'
  | BA''
  | BB'
  | AB''
  deriving DecidableEq, Repr, Inhabited

/-- The strategy-player side supplying the local Hilbert space in each of the
four register placements at paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`. -/
@[reducible] def Placement.side : Placement → PlayerSide
  | .AA' => .alice
  | .BA'' => .bob
  | .BB' => .bob
  | .AB'' => .alice

/-- The uncrossed placements of the two players' witnesses. -/
inductive Placement.Primary : Placement → Prop
  | alice : Primary .AA'
  | bob : Primary .BB'

/-- Exchange the first two factors, leaving the unused factor alone. -/
def swapPaired {A B C : Type*} : A × (B × C) ≃ B × (A × C) where
  toFun p := (p.2.1, p.1, p.2.2)
  invFun p := (p.2.1, p.1, p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem reindexOp_trans {A B C : Type*} (e : A ≃ B) (f : B ≃ C) (M : Op C) :
    reindexOp (e.trans f) M = reindexOp e (reindexOp f M) := rfl

theorem reindexOp_swapPaired_heteroKron_one {A B C : Type*}
    [DecidableEq A] [DecidableEq C] (M : Op B) :
    reindexOp (swapPaired (A := A) (C := C)) (heteroKron M 1) =
      heteroKron (1 : Op A) (heteroKron M (1 : Op C)) := by
  ext i j
  simp [reindexOp, swapPaired, heteroKron, Matrix.kronecker, Matrix.one_apply,
    Prod.ext_iff, ite_and, mul_ite, ite_mul]
  split_ifs <;> rfl

/-- Regroup `AA'A''BB'B''` as `AA' | BA''(B'B'')`. This is the tensor
bipartition used for data processing on the `AA'`--`BA''` placement pair in
item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
def aaBaBipartition (P : AdmissibleParams) (ιA ιB : Type*) :
    SixReg P ιA ιB ≃
      (ιA × PauliRegister P) ×
        ((ιB × PauliRegister P) × (PauliRegister P × PauliRegister P)) where
  toFun p := ((p.1.1, p.1.2.1), ((p.2.1, p.1.2.2), (p.2.2.1, p.2.2.2)))
  invFun p := ((p.1.1, (p.1.2, p.2.1.2)),
    (p.2.1.1, (p.2.2.1, p.2.2.2)))
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-- Regroup `AA'A''BB'B''` as `AB'' | BB'(A'A'')`. This is the tensor
bipartition used for data processing on the `AB''`--`BB'` placement pair in
item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
def abBbBipartition (P : AdmissibleParams) (ιA ιB : Type*) :
    SixReg P ιA ιB ≃
      (ιA × PauliRegister P) ×
        ((ιB × PauliRegister P) × (PauliRegister P × PauliRegister P)) where
  toFun p := ((p.1.1, p.2.2.2), ((p.2.1, p.2.2.1), (p.1.2.1, p.1.2.2)))
  invFun p := ((p.1.1, (p.2.2.1, p.2.2.2)),
    (p.2.1.1, (p.2.1.2, p.1.2)))
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

/-- The ideal Pauli basis measurement on the ancillary register, bundled using
positivity and completeness of the existing Pauli projectors. -/
noncomputable def pauliRegisterMeas {params : AdmissibleParams} (basis : PauliKind) :
    Measurement (PauliRegister params) (PauliRegister params) :=
  Measurement.ofSumEqOne (pauliProj basis)
    (fun answer => Matrix.nonneg_iff_posSemidef.mpr (posSemidef_pauliProj basis answer))
    (sum_pauliProj_eq_one basis)

/-- The Pauli basis measurement is projective. -/
theorem pauliRegisterMeas_isProjective {P : AdmissibleParams} (W : PauliKind) :
    Measurement.IsProjective (pauliRegisterMeas (params := P) W) := by
  intro h
  change IsProj (pauliProj W h)
  exact ⟨by simp [IsIdempotentElem, pauliProj_mul_pauliProj], (posSemidef_pauliProj W h).isHermitian⟩

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- The full expanded strategy space in six-register order. -/
abbrev ExpandedSpace (S : ProjectiveSetting P ε) := SixReg P S.toStrategy.ιA S.toStrategy.ιB


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
    EuclideanSpace ℂ (S.ExpandedSpace) := by
  classical
  exact
    reindexState (sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
      (vecTensor
        (vecTensor S.toStrategy.ψ (eprState (PauliRegister P)))
        (eprState (PauliRegister P)))

/-- The other member of the directed opposite pair. -/
abbrev overlapPartner : Placement → Placement
  | .AA' => .BA''
  | .BA'' => .AA'
  | .AB'' => .BB'
  | .BB' => .AB''

/-- The remaining local registers, with the other player and its current
Pauli factor first and the unused EPR pair last. -/
abbrev SplitRest (S : ProjectiveSetting P ε) (p : Placement) :=
  S.ExpandedLocalSpace (overlapPartner p).side × (PauliRegister P × PauliRegister P)

/-- Split off the selected local factor, in the order used for its placement. -/
def placeSplit (S : ProjectiveSetting P ε) :
    (p : Placement) → S.ExpandedSpace ≃
      S.ExpandedLocalSpace p.side × S.SplitRest p
  | .AA' => aaBaBipartition P _ _
  | .BA'' => (aaBaBipartition P _ _).trans swapPaired
  | .AB'' => abBbBipartition P _ _
  | .BB' => (abBbBipartition P _ _).trans swapPaired

/-- The placement of a local operator is its tensor with the identity on
all other registers, reindexed to the six-register order. -/
def placeLinear (S : ProjectiveSetting P ε) (p : Placement) :
    Op (S.ExpandedLocalSpace p.side) →ₗ[ℂ] Op (S.ExpandedSpace) :=
  let e := (S.placeSplit p).symm
  (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap.comp
    ((Matrix.kroneckerBilinear (R := ℂ) (α := ℂ)).flip (1 : Op (S.SplitRest p)))

abbrev place (S : ProjectiveSetting P ε) (p : Placement)
    (O : Op (S.ExpandedLocalSpace p.side)) : Op (S.ExpandedSpace) :=
  S.placeLinear p O

/-- The joint quadratic form of two local effects on the expanded state. -/
abbrev placedCorrelation (S : ProjectiveSetting P ε) (p q : Placement)
    (A : Op (S.ExpandedLocalSpace p.side)) (B : Op (S.ExpandedLocalSpace q.side)) : ℝ :=
  DistanceCalculus.stateQForm S.psiHat (S.place p A * S.place q B)

theorem place_eq_reindex (S : ProjectiveSetting P ε) (p : Placement)
    (O : Op (S.ExpandedLocalSpace p.side)) :
    S.place p O = reindexOp (S.placeSplit p) (heteroKron O 1) := rfl

/-- A placement sends the local identity to the identity of the six-register
space. -/
theorem place_one (S : ProjectiveSetting P ε) (p : Placement) :
    S.place p (1 : Op (S.ExpandedLocalSpace p.side)) = 1 := by
  ext i j
  simp [place_eq_reindex, reindexOp, heteroKron, Matrix.kronecker, Matrix.one_apply,
    ← Prod.ext_iff]

/-- In the selected split the opposite operator acts on the other player and
its Pauli factor, with an identity on the unused EPR pair. -/
theorem reindexOp_placeSplit_partner (S : ProjectiveSetting P ε) (p : Placement)
    (A : Op (S.ExpandedLocalSpace (overlapPartner p).side)) :
    reindexOp (S.placeSplit p) (heteroKron 1 (heteroKron A (1 : Op (PauliRegister P × PauliRegister P)))) =
      S.place (overlapPartner p) A := by
  cases p <;> rw [place_eq_reindex] <;> simp only [overlapPartner, placeSplit]
  all_goals first
    | rw [reindexOp_trans, reindexOp_swapPaired_heteroKron_one]
    | rw [reindexOp_trans, ← reindexOp_swapPaired_heteroKron_one, ← reindexOp_trans]; rfl

/-- The expanded observable
`W^r(u) tensor tau^W(r * ind_m(u))` on a selected player side. This is
Equation `eq:lc-23`, paper `14_analysis_of_the_pauli_basis_test.tex:374-382`,
blueprint `eq:lc-23`. -/
noncomputable def expObs (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (r : PauliScalar P) (u : PauliPoint P) :
    Op (S.ExpandedLocalSpace side) :=
  heteroKron (S.pointObs side W r u)
    (tauObservable W (fun h => r * indicatorVec u h))

/-- The Fourier average defining the expanded point effect. This is the first
display of `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:384-418`, blueprint
`def:expanded-point-measurement`. -/
noncomputable def expPointOp (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (u : PauliPoint P) (a : PauliScalar P) :
    Op (S.ExpandedLocalSpace side) :=
  averageOperatorOverDistribution (uniformDistribution (PauliScalar P)) fun r =>
    phaseSign (fixedBinTrace P.model (a * r)) • S.expObs side W r u

/-- The Pauli-register projector onto labels whose low-degree encoding has
value `a` at `u`. This is Equation `eq:qld-point-obs-def`, paper
`14_analysis_of_the_pauli_basis_test.tex:389-394`, blueprint
`eq:qld-point-obs-def`. -/
noncomputable def tauPointProj (W : PauliKind)
    (u : PauliPoint P) (a : PauliScalar P) : Op (PauliRegister P) :=
  ∑ h ∈ Finset.univ.filter (fun h : PauliRegister P =>
      dotProduct h (indicatorVec u) = a),
    pauliProj W h

/-- The point coarse-graining of the generalized Pauli projectors is symmetric.
This is the EPR-transport identity used for the perfect ancilla consistency in
item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem tauPointProj_transpose (W : PauliKind)
    (u : PauliPoint P) (a : PauliScalar P) :
    (tauPointProj W u a)ᵀ = tauPointProj W u a := by
  classical
  simp only [tauPointProj, Matrix.transpose_sum, pauliProj_transpose]

/-- Pauli point projectors belonging to distinct values are orthogonal, while
each projector is idempotent. This is the ancillary product calculation in
item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem tauPointProj_mul_tauPointProj (W : PauliKind)
    (u : PauliPoint P) (a b : PauliScalar P) :
    tauPointProj W u a * tauPointProj W u b =
      if a = b then tauPointProj W u a else 0 := by
  let M := (pauliRegisterMeas (params := P) W).postprocess
    (fun h => dotProduct h (indicatorVec u))
  have hM := SandwichProduct.postprocess_isProjective _
    (pauliRegisterMeas_isProjective (P := P) W) (fun h => dotProduct h (indicatorVec u))
  change M.effect a * M.effect b = if a = b then M.effect a else 0
  split_ifs with hab
  · subst b
    exact (hM a).isIdempotentElem.eq
  · exact DistanceCalculus.projective_effect_mul_effect_eq_zero _ hM hab

/-- The phase induced by the fixed binary trace is an additive character. -/
private theorem phaseSign_fixedBinTrace_mul (x y : PauliScalar P) :
    phaseSign (fixedBinTrace P.model x) * phaseSign (fixedBinTrace P.model y) =
      phaseSign (fixedBinTrace P.model (x + y)) := by
  rw [fixedBinTrace, map_add]
  exact (phaseSign_add _ _).symm

/-- The trace phase converts addition of coefficients to multiplication. -/
private theorem phaseSign_fixedBinTrace_mul_add (x y r : PauliScalar P) :
    phaseSign (fixedBinTrace P.model (x * r)) *
        phaseSign (fixedBinTrace P.model (y * r)) =
      phaseSign (fixedBinTrace P.model ((x + y) * r)) := by
  rw [add_mul]
  exact phaseSign_fixedBinTrace_mul (x * r) (y * r)

/-- Orthogonality of the fixed trace character over the Pauli scalar field. -/
private theorem phaseSign_fixedBinTrace_expect (c : PauliScalar P) :
    (𝔼 r : PauliScalar P, phaseSign (fixedBinTrace P.model (c * r))) =
      if c = 0 then (1 : ℂ) else 0 := by
  simpa only [fixedBinTrace, phaseSign_eq_ffChar,
    MIPStarRE.LDT.Preliminaries.ffChar_apply, mul_comm c] using
    (fourier_fact_scalar (p := 2) (F := PauliScalar P) c)

/-- Averaging a trace phase times an operator selects the zero coefficient. -/
private theorem average_phaseSign_fixedBinTrace_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : PauliScalar P) (A : Op ι) :
    averageOperatorOverDistribution (uniformDistribution (PauliScalar P))
        (fun r => phaseSign (fixedBinTrace P.model (c * r)) • A) =
      if c = 0 then A else 0 := by
  classical
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
  rw [hcoeff]
  by_cases hc : c = 0 <;> simp [hc]

/-- Averaging three fixed trace characters imposes the convolution constraint. -/
private theorem average_three_phaseSign_fixedBinTrace_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a x y : PauliScalar P) (A : Op ι) :
    averageOperatorOverDistribution (uniformDistribution (PauliScalar P))
        (fun r => phaseSign (fixedBinTrace P.model (a * r)) •
          (phaseSign (fixedBinTrace P.model (x * r)) •
            (phaseSign (fixedBinTrace P.model (y * r)) • A))) =
      if x + y = a then A else 0 := by
  haveI :=
    (Algebra.charP_iff (ZMod 2) (PauliScalar P) 2).mp (ZMod.charP 2)
  have hzero : a + x + y = 0 ↔ x + y = a := by
    constructor
    · intro h
      exact (CharTwo.add_eq_zero.mp (by simpa only [add_assoc] using h)).symm
    · intro h
      rw [add_assoc]
      exact CharTwo.add_eq_zero.mpr h.symm
  calc
    _ =
      averageOperatorOverDistribution (uniformDistribution (PauliScalar P))
        (fun r => phaseSign (fixedBinTrace P.model ((a + x + y) * r)) • A) := by
          apply averageOperatorOverDistribution_congr
          intro r
          rw [smul_smul, phaseSign_fixedBinTrace_mul_add a x r, smul_smul,
            phaseSign_fixedBinTrace_mul_add (a + x) y r]
    _ = if a + x + y = 0 then A else 0 :=
      average_phaseSign_fixedBinTrace_smul (a + x + y) A
    _ = _ := if_congr hzero rfl rfl

/-- A scalar in the indicator vector factors out of the dot product. -/
private theorem dot_smul_indicator (r : PauliScalar P)
    (u : PauliPoint P) (e : PauliRegister P) :
    dotProduct (fun h => r * indicatorVec u h) e =
      dotProduct e (indicatorVec u) * r := by
  change dotProduct (r • indicatorVec u) e = _
  rw [smul_dotProduct, dotProduct_comm, smul_eq_mul, mul_comm]

/-- Tensor products distribute over the sums in both factors. -/
private theorem heteroKron_sum_sum {α β ι κ : Type*}
    [Fintype α] [Fintype β] (A : α → Op ι) (B : β → Op κ) :
    heteroKron (∑ x, A x) (∑ y, B y) =
      ∑ x, ∑ y, heteroKron (A x) (B y) := by
  rw [DistanceCalculus.heteroKron_finset_sum_left]
  exact Finset.sum_congr rfl fun x _ =>
    DistanceCalculus.heteroKron_finset_sum_right _ _ _

/-- Scalars in the two tensor factors act successively on their tensor product. -/
private theorem heteroKron_smul_smul {ι κ : Type*}
    (c d : ℂ) (A : Op ι) (B : Op κ) :
    heteroKron (c • A) (d • B) = c • (d • heteroKron A B) := by
  unfold heteroKron Matrix.kronecker
  rw [Matrix.smul_kronecker, Matrix.kronecker_smul]

/-- The expanded point effect is the convolution of the strategy point
measurement and the Pauli-register point projection. This is the final display
of `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:395-418`. -/
theorem expPointOp_eq_convolution (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : PauliPoint P)
    (a : PauliScalar P) :
    S.expPointOp side W u a =
      ∑ p ∈ Finset.univ.filter (fun p : PauliScalar P × PauliScalar P =>
          p.1 + p.2 = a),
        heteroKron ((S.pointMeas side W u).effect p.1)
          (tauPointProj W u p.2) := by
  classical
  rw [expPointOp]
  simp only [expObs, pointObs, tauObservable_eq_sum_pauliProj]
  simp_rw [dot_smul_indicator (P := P) _ u]
  simp only [heteroKron_sum_sum, heteroKron_smul_smul, Finset.smul_sum,
    averageOperatorOverDistribution_sum]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [tauPointProj, DistanceCalculus.heteroKron_finset_sum_right,
    Finset.ite_sum_zero, Finset.sum_fiberwise_apply]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun e _ =>
    average_three_phaseSign_fixedBinTrace_smul a x (dotProduct e (indicatorVec u)) _

/-- The projective point measurement on one Pauli register obtained by
coarse-graining the generalized Pauli basis according to its value at `u`.
This is the ancillary measurement used in item 1 of `lem:qld-comm-cons`, paper
`eq:qld-point-obs-def` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:385-411`,
blueprint `def:ancillary-point-measurement`. -/
noncomputable def tauPointMeas (W : PauliKind)
    (u : PauliPoint P) :
    Measurement (PauliScalar P) (PauliRegister P) :=
  (pauliRegisterMeas W).postprocess (fun h => dotProduct h (indicatorVec u))

@[simp] theorem tauPointMeas_effect (W : PauliKind) (u : PauliPoint P)
    (a : PauliScalar P) : (tauPointMeas W u).effect a = tauPointProj W u a := rfl

/-- The fine product measurement underlying the convolution definition of an
expanded point measurement. Its outcome records the strategy and Pauli point
values separately. Paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:390-411`,
blueprint `def:point-tau-measurement`. -/
noncomputable def pointTauMeas (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (u : PauliPoint P) :
    Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace side) :=
  tensorMeasurement (S.pointMeas side W u) (tauPointMeas W u)

/-- The expanded point measurement, using Fourier inversion to certify
positivity and completeness from the tensor product readout. -/
noncomputable def pointMeasExp (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (u : PauliPoint P) :
    Measurement (PauliScalar P) (S.ExpandedLocalSpace side) :=
  let M := (S.pointTauMeas side W u).postprocess (fun p => p.1 + p.2)
  Measurement.ofSumEqOne (S.expPointOp side W u)
    (fun a => by rw [expPointOp_eq_convolution]; exact M.pos a)
    (by simp_rw [expPointOp_eq_convolution]; exact M.sum_eq_one)

/-- The expanded point measurement is the addition postprocessing of its fine
strategy--Pauli product measurement. This is the data-processing presentation
used in item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:390-411`,
blueprint `lem:expanded-point-measurement-properties`. -/
theorem pointMeasExp_effect_eq_pointTauMeas_postprocess
    (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)
    (u : PauliPoint P) (a : PauliScalar P) :
    (S.pointMeasExp side W u).effect a =
      ((S.pointTauMeas side W u).postprocess (fun p => p.1 + p.2)).effect a := expPointOp_eq_convolution S side W u a

/-- The expanded point measurement is projective, as asserted after the
convolution formula in `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:395-418`. -/
theorem pointMeasExp_isProjective (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : PauliPoint P) :
    MIPStarRE.QPBT.Measurement.IsProjective (S.pointMeasExp side W u) := by
  intro a
  rw [S.pointMeasExp_effect_eq_pointTauMeas_postprocess]
  exact SandwichProduct.postprocess_isProjective _
    (tensorMeasurement_isProjective (S.pointMeas_isProjective side W u)
      (SandwichProduct.postprocess_isProjective _ (pauliRegisterMeas_isProjective W) _)) _ a

end ProjectiveSetting

end

end MIPStarRE.QPBT
