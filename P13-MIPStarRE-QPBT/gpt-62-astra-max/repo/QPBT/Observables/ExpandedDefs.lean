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

section

variable (P : AdmissibleParams) (ιA ιB : Type*)

/-- The six registers `AA'A''BB'B''`, retaining distinct Alice and Bob local
spaces. This is the register index type of `def:expanded-state`, paper
`14_analysis_of_the_pauli_basis_test.tex:367-372`, blueprint
`def:expanded-state`. -/
abbrev SixReg :=
  (ιA × (PauliRegister P × PauliRegister P)) ×
    (ιB × (PauliRegister P × PauliRegister P))

/-- Equality of six-register indices is supplied by classical decidability for
the register type. This is the index set of blueprint
`def:expanded-state`. -/
noncomputable instance sixRegDecidableEq : DecidableEq (SixReg P ιA ιB) :=
  Classical.decEq _

/-- Reassociate the tensor product of the strategy state and two EPR states
directly into register order `AA'A''BB'B''` for
`eq:def-psihat`, paper `14_analysis_of_the_pauli_basis_test.tex:367-372`. -/
def sixRegShuffle :
    (((ιA × ιB) × (PauliRegister P × PauliRegister P)) ×
        (PauliRegister P × PauliRegister P)) ≃ SixReg P ιA ιB where
  toFun p := ((p.1.1.1, (p.1.2.1, p.1.2.2)),
    (p.1.1.2, (p.2.1, p.2.2)))
  invFun p := (((p.1.1, p.2.1), (p.1.2.1, p.1.2.2)),
    (p.2.2.1, p.2.2.2))
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

end

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

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

section

variable (S : ProjectiveSetting P ε)

/-- A strategy-local register paired with one generalized-Pauli register. This
is the operator space in `def:expanded-observables`, paper
`14_analysis_of_the_pauli_basis_test.tex:374-382`. -/
abbrev ExpandedLocalSpace (side : PlayerSide) :=
  S.LocalSpace side × PauliRegister P

/-- The strategy state tensored with EPR states on `A'A''` and `B'B''`, in the
six-register order. This is `eq:def-psihat`, paper
`14_analysis_of_the_pauli_basis_test.tex:367-372`, blueprint
`eq:def-psihat`. -/
noncomputable def psiHat :
    EuclideanSpace ℂ (SixReg P S.toStrategy.ιA S.toStrategy.ιB) := by
  classical
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
noncomputable def place (p : Placement)
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
noncomputable def expObs (side : PlayerSide)
    (W : PauliKind) (r : PauliScalar P) (u : PauliPoint P) :
    Op (S.ExpandedLocalSpace side) :=
  heteroKron (S.pointObs side W r u)
    (tauObservable W (fun h => r * indicatorVec u h))

/-- The Fourier average defining the expanded point effect. This is the first
display of `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:384-418`, blueprint
`def:expanded-point-measurement`. -/
noncomputable def expPointOp (side : PlayerSide)
    (W : PauliKind) (u : PauliPoint P) (a : PauliScalar P) :
    Op (S.ExpandedLocalSpace side) :=
  averageOperatorOverDistribution (uniformDistribution (PauliScalar P)) fun r =>
    phaseSign (fixedBinTrace P.model (a * r)) • S.expObs side W r u

end

section

variable (W : PauliKind) (u : PauliPoint P)

/-- The Pauli-register projector onto labels whose low-degree encoding has
value `a` at `u`. This is Equation `eq:qld-point-obs-def`, paper
`14_analysis_of_the_pauli_basis_test.tex:389-394`, blueprint
`eq:qld-point-obs-def`. -/
noncomputable def tauPointProj (a : PauliScalar P) : Op (PauliRegister P) :=
  ∑ h ∈ Finset.univ.filter (fun h : PauliRegister P =>
      dotProduct h (indicatorVec u) = a),
    pauliProj W h

/-- The point coarse-graining of the generalized Pauli projectors is symmetric.
This is the EPR-transport identity used for the perfect ancilla consistency in
item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem tauPointProj_transpose (a : PauliScalar P) :
    (tauPointProj W u a)ᵀ = tauPointProj W u a := by
  simp [tauPointProj, Matrix.transpose_sum, pauliProj_transpose]

/-- Pauli point projectors belonging to distinct values are orthogonal, while
each projector is idempotent. This is the ancillary product calculation in
item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem tauPointProj_mul_tauPointProj (a b : PauliScalar P) :
    tauPointProj W u a * tauPointProj W u b =
      if a = b then tauPointProj W u a else 0 := by
  classical
  unfold tauPointProj
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  by_cases hab : a = b
  · subst b
    simp
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.sum_eq_single]
    · rw [pauliProj_mul_pauliProj, if_pos rfl]
    · intro f hf hfe
      rw [pauliProj_mul_pauliProj, if_neg hfe.symm]
    · grind
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro e he
    apply Finset.sum_eq_zero
    intro f hf
    rw [pauliProj_mul_pauliProj, if_neg]
    intro hef
    apply hab
    simp_all

end

/-- The phase induced by the fixed binary trace is an additive character. -/
theorem phaseSign_fixedBinTrace_mul (x y : PauliScalar P) :
    phaseSign (fixedBinTrace P.model x) * phaseSign (fixedBinTrace P.model y) =
      phaseSign (fixedBinTrace P.model (x + y)) := by
  simp [fixedBinTrace]
  exact (phaseSign_add _ _).symm

/-- The trace phase converts addition of coefficients to multiplication. -/
private theorem phaseSign_fixedBinTrace_mul_add (x y r : PauliScalar P) :
    phaseSign (fixedBinTrace P.model (x * r)) *
        phaseSign (fixedBinTrace P.model (y * r)) =
      phaseSign (fixedBinTrace P.model ((x + y) * r)) := by
  rw [add_mul]
  apply phaseSign_fixedBinTrace_mul

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Averaging a trace phase times an operator selects the zero coefficient. -/
private theorem average_phaseSign_fixedBinTrace_smul
    (c : PauliScalar P) (A : Op ι) :
    averageOperatorOverDistribution (uniformDistribution (PauliScalar P))
        (fun r => phaseSign (fixedBinTrace P.model (c * r)) • A) =
      if c = 0 then A else 0 := by
  classical
  rw [averageOperatorOverDistribution_smul_const]
  simp only [uniformDistribution, Distribution.uniformOnFinset,
    Finset.mem_univ, if_true, Finset.card_univ, ← Finset.mul_sum]
  have havg : (𝔼 r : PauliScalar _, phaseSign (fixedBinTrace P.model (c * r))) = if c = 0 then (1 : ℂ) else 0 := by
         simpa only [fixedBinTrace, phaseSign_eq_ffChar,
           MIPStarRE.LDT.Preliminaries.ffChar_apply, mul_comm] using
           (fourier_fact_scalar (p := 2) c)
  rw [Fintype.expect_eq_sum_div_card] at havg
  have hcoeff :
      (1 / (Fintype.card (PauliScalar P) : ℝ) : ℝ) *
          (∑ r : PauliScalar P,
            phaseSign (fixedBinTrace P.model (c * r))) =
        if c = 0 then 1 else 0 := by
    simpa [one_div, div_eq_mul_inv, mul_comm] using havg
  rw [hcoeff]
  simp

/-- Averaging three fixed trace characters imposes the convolution constraint. -/
private theorem average_three_phaseSign_fixedBinTrace_smul
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
    · grind
    · grind
  rw [← if_congr hzero rfl rfl]
  rw [← average_phaseSign_fixedBinTrace_smul (a + x + y) A]
  apply averageOperatorOverDistribution_congr
  intro r
  rw [smul_smul, phaseSign_fixedBinTrace_mul_add, smul_smul,
    phaseSign_fixedBinTrace_mul_add]

end

/-- A scalar in the indicator vector factors out of the dot product. -/
private theorem dot_smul_indicator (r : PauliScalar P)
    (u : PauliPoint P) (e : PauliRegister P) :
    dotProduct (fun h => r * indicatorVec u h) e =
      dotProduct e (indicatorVec u) * r := by
  change dotProduct (r • indicatorVec u) e = _
  simp [dotProduct_comm, smul_eq_mul, mul_comm]

/-- Tensor products distribute over the sums in both factors. -/
theorem heteroKron_sum_sum {α β ι κ : Type*}
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
  let effectAt := (S.pointMeas side W u).effect
  classical
  rw [expPointOp]
  simp [expObs, pointObs, tauObservable_eq_sum_pauliProj]
  simp_rw [dot_smul_indicator]
  calc
    averageOperatorOverDistribution (uniformDistribution (PauliScalar P))
        (fun r => phaseSign (fixedBinTrace P.model (a * r)) •
          heteroKron
            (∑ x, phaseSign (fixedBinTrace P.model (x * r)) •
              effectAt x)
            (∑ e, phaseSign (fixedBinTrace P.model
              (dotProduct e (indicatorVec u) * r)) • pauliProj W e)) =
      averageOperatorOverDistribution (uniformDistribution (PauliScalar P))
        (fun r => ∑ x, ∑ e,
          phaseSign (fixedBinTrace P.model (a * r)) •
            (phaseSign (fixedBinTrace P.model (x * r)) •
              (phaseSign (fixedBinTrace P.model
                (dotProduct e (indicatorVec u) * r)) •
                  heteroKron (effectAt x)
                    (pauliProj W e)))) := by
          apply averageOperatorOverDistribution_congr
          intro r
          rw [heteroKron_sum_sum]
          simp_rw [heteroKron_smul_smul, Finset.smul_sum]
    _ = ∑ x, ∑ e,
          if x + dotProduct e (indicatorVec u) = a then
            heteroKron (effectAt x) (pauliProj W e)
          else 0 := by
      simp_rw [averageOperatorOverDistribution_sum]
      simp_rw [average_three_phaseSign_fixedBinTrace_smul]
    _ = _ := by
      simp only [tauPointProj]
      rw [Finset.sum_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x hx
      refine Eq.trans ((Finset.sum_fiberwise Finset.univ
        (fun e : PauliRegister P => dotProduct e (indicatorVec u))
        (fun e => if x + dotProduct e (indicatorVec u) = a then
          heteroKron (effectAt x) (pauliProj W e)
        else 0)).symm) ?_
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hxy : x + y = a
      · rw [if_pos hxy, DistanceCalculus.heteroKron_finset_sum_right]
        apply Finset.sum_congr rfl
        aesop
      · rw [if_neg hxy]
        apply Finset.sum_eq_zero
        aesop

section

variable (W : PauliKind) (u : PauliPoint P)

/-- Each point fiber is a sum of positive Pauli projectors. -/
private theorem tauPointProj_nonneg (a : PauliScalar P) :
    0 ≤ tauPointProj W u a := by
  classical
  exact Finset.sum_nonneg fun e he =>
    Matrix.nonneg_iff_posSemidef.mpr (posSemidef_pauliProj W e)

/-- The point fibers partition the complete family of Pauli eigenspace projectors. -/
private theorem sum_tauPointProj_eq_one :
    ∑ a, tauPointProj W u a = 1 := by
  classical
  rw [show (∑ a, tauPointProj W u a) =
      _ by
    apply Finset.sum_fiberwise]
  exact sum_pauliProj_eq_one W

/-- The projective point measurement on one Pauli register obtained by
coarse-graining the generalized Pauli basis according to its value at `u`.
This is the ancillary measurement used in item 1 of `lem:qld-comm-cons`, paper
`eq:qld-point-obs-def` in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:385-411`,
blueprint `def:ancillary-point-measurement`. -/
noncomputable def tauPointMeas :
    Measurement (PauliScalar P) (PauliRegister P) :=
  Measurement.ofSumEqOne (tauPointProj W u) (by
    exact tauPointProj_nonneg W u) (by
    exact sum_tauPointProj_eq_one W u)

end

variable (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)

section

variable (u : PauliPoint P)

/-- The fine product measurement underlying the convolution definition of an
expanded point measurement. Its outcome records the strategy and Pauli point
values separately. Paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:390-411`,
blueprint `def:point-tau-measurement`. -/
noncomputable def pointTauMeas :
    Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace side) :=
  Measurement.ofSumEqOne
    (fun p => heteroKron ((S.pointMeas side W u).effect p.1)
      ((tauPointMeas W u).effect p.2))
    (fun p => Quantum.kronecker_nonneg
      ((S.pointMeas side W u).pos p.1) ((tauPointMeas W u).pos p.2))
    (by
      change ∑ p : PauliScalar P × PauliScalar P,
          heteroKron ((S.pointMeas side W u).effect p.1)
            (tauPointProj W u p.2) = 1
      rw [Fintype.sum_prod_type]
      refine Eq.trans ((heteroKron_sum_sum _ _).symm) ?_
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
  let effectAt := (S.pointMeas side W u).effect
  calc
    _ =
      ∑ p : PauliScalar P × PauliScalar P,
        heteroKron (effectAt p.1)
          (tauPointProj W u p.2) := by
      let f : PauliScalar P × PauliScalar P → PauliScalar P :=
        fun p => p.1 + p.2
      let A : PauliScalar P × PauliScalar P →
          Op (S.ExpandedLocalSpace side) := fun p =>
        heteroKron (effectAt p.1)
          (tauPointProj W u p.2)
      apply Finset.sum_fiberwise
    _ = heteroKron (∑ x, effectAt x)
        (∑ y, tauPointProj W u y) := by
      rw [Fintype.sum_prod_type]
      exact (heteroKron_sum_sum _ _).symm
    _ = 1 := by
      rw [(S.pointMeas side W u).sum_eq_one,
        sum_tauPointProj_eq_one]
      exact Matrix.one_kronecker_one

/-- The complete expanded point measurement on the chosen player and Pauli
register. Its effects are those of `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:384-418`, blueprint
`def:expanded-point-measurement`. -/
noncomputable def pointMeasExp :
    Measurement (PauliScalar P) (S.ExpandedLocalSpace side) :=
  Measurement.ofSumEqOne (S.expPointOp side W u)
    (S.expPointOp_nonneg side W u) (S.expPointOp_sum_eq_one side W u)

/-- The expanded point measurement is the addition postprocessing of its fine
strategy--Pauli product measurement. This is the data-processing presentation
used in item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:390-411`,
blueprint `lem:expanded-point-measurement-properties`. -/
theorem pointMeasExp_effect_eq_pointTauMeas_postprocess (a : PauliScalar P) :
    (S.pointMeasExp side W u).effect a =
      ((S.pointTauMeas side W u).postprocess (fun p => p.1 + p.2)).effect a := by
  apply expPointOp_eq_convolution

end

/-- Expanded observables inherit the additive representation law. -/
private theorem expObs_mul (r s : PauliScalar P)
    (u : PauliPoint P) :
    S.expObs side W r u * S.expObs side W s u =
      S.expObs side W (r + s) u := by
  calc
    _ =
        heteroKron
          (S.pointObs side W r u * S.pointObs side W s u)
          (tauObservable W (fun h => r * indicatorVec u h) *
            tauObservable W (fun h => s * indicatorVec u h)) := (Matrix.mul_kronecker_mul
        (S.pointObs side W r u) (S.pointObs side W s u)
        (tauObservable W (fun h => r * indicatorVec u h))
        (tauObservable W (fun h => s * indicatorVec u h))).symm
    _ = heteroKron (S.pointObs side W (r + s) u)
        (tauObservable W ((fun h => r * indicatorVec u h) +
          (fun h => s * indicatorVec u h))) := by
      rw [pointObs_mul, tauObservable_mul]
    _ = _ := by
      congr 2
      funext h
      simp
      ring

/-- Idempotence of the expanded point effect, the idempotence half of projectivity
in `def:expanded-point-measurement`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:384-418`. -/
private theorem expPointOp_mul_self (u : PauliPoint P)
    (a : PauliScalar P) :
    S.expPointOp side W u a * S.expPointOp side W u a =
      S.expPointOp side W u a := by
  classical
  let D := uniformDistribution (PauliScalar P)
  let F : PauliScalar P → _ := fun r =>
    phaseSign (fixedBinTrace P.model (a * r)) • S.expObs side W r u
  change averageOperatorOverDistribution D F *
      averageOperatorOverDistribution D F = _
  calc
    _ =
        _ := by
      simpa using (averageOperatorOverDistribution_mul_left_right D
        1 (averageOperatorOverDistribution D F) F).symm
    _ = _ := by
      apply averageOperatorOverDistribution_congr
      intro r
      simpa using
        (averageOperatorOverDistribution_mul_left_right D (F r) 1 F).symm
    _ = averageOperatorOverDistribution D
          (fun r => averageOperatorOverDistribution D (fun s => F (r + s))) := by
      apply averageOperatorOverDistribution_congr
      intro r
      apply averageOperatorOverDistribution_congr
      intro s
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, expObs_mul]
      congr 1
      simpa only [mul_add] using
        phaseSign_fixedBinTrace_mul (a * r) (a * s)
    _ = _ := by
      apply averageOperatorOverDistribution_congr
      intro r
      exact (averageOperatorOverDistribution_uniform_equiv
        ((Equiv.addLeft r).symm) F).symm
    _ = _ := averageOperatorOverDistribution_const_of_isProbability D
        (uniformDistribution_isProbability (PauliScalar P)) _

/-- The expanded point measurement is projective, as asserted after the
convolution formula in `def:expanded-point-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:395-418`. -/
theorem pointMeasExp_isProjective (u : PauliPoint P) :
    MIPStarRE.QPBT.Measurement.IsProjective (S.pointMeasExp side W u) := by
  intro a
  refine isStarProjection_iff'.2 ⟨expPointOp_mul_self S side W u a, ?_⟩
  exact (Matrix.nonneg_iff_posSemidef.mp (S.expPointOp_nonneg side W u a)).isHermitian.eq

end ProjectiveSetting

end

end MIPStarRE.QPBT
