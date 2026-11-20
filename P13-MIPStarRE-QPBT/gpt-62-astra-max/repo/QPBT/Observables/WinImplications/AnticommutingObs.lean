module

public import QPBT.Observables.WinImplications.CommutingObs
public import QPBT.Test.MagicSquareTheorems.Rigidity.Anticommutation
public import QPBT.Test.MagicSquareTheorems.Rigidity.AnticommutatorB

/-!
# Approximate anticommutation of the point observables on anticommuting tuples

This module carries out the anticommuting half of the proof of Equation
`eq:pts-obs-commutation` in `lem:qld-win-implications-obs`. The Magic Square
approximate anticommutation of the variable observables is read back from the
projective dilation on which it is proved, and transported to Alice's point
observables through item 7 of `lem:qld-win-implications`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-362`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reading the dilation back on the original space -/

section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The matrix of the identity isometry is the identity matrix.
Formalization-only support for `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:266-288`. -/
theorem isometryMatrix_id :
    MagicSquareRigidity.isometryMatrix
      (LinearIsometry.id (R := ℂ) (E := EuclideanSpace ℂ ι)) = 1 := by
  ext <;> simp [MagicSquareRigidity.isometryMatrix_apply, Matrix.one_apply, EuclideanSpace.equiv]

/-- Conjugation by the identity isometry is the identity. Formalization-only
support for `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:266-288`. -/
theorem conjIsometry_id (M : Op ι) :
    conjIsometry (LinearIsometry.id (R := ℂ) (E := EuclideanSpace ℂ ι)) M = M := by
  simp [MagicSquareRigidity.conjIsometry_eq, isometryMatrix_id]

end

/-- The two-sided identity isometry fixes every bipartite state.
Formalization-only support for `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:266-288`. -/
theorem isometryTensor_id {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    isometryTensor (LinearIsometry.id (R := ℂ) (E := EuclideanSpace ℂ ιA))
      (LinearIsometry.id (R := ℂ) (E := EuclideanSpace ℂ ιB)) ψ = ψ := by
  ext p
  rw [MagicSquareRigidity.isometryTensor_apply_eq, isometryMatrix_id,
    isometryMatrix_id]
  rw [show Matrix.kronecker (1 : Op ιA) (1 : Op ιB) = 1 from
    Matrix.one_kronecker_one]
  simp [Matrix.one_apply]

/-- Inflation to the ground slice is additive. Formalization-only support for
`thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:266-288`. -/
theorem naimarkInflation_add {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M N : Op ι) :
    MagicSquareRigidity.naimarkInflation (α := α) M +
        MagicSquareRigidity.naimarkInflation (α := α) N =
      MagicSquareRigidity.naimarkInflation (α := α) (M + N) := by
  ext p q
  by_cases h : p.2 = none ∧ q.2 = none <;> simp [h]

section

variable (α : Type) [Fintype α] [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
  [Fintype ιB] [DecidableEq ιB] (N : Op ιB) (ψ : EuclideanSpace ℂ (ιA × ιB))

/-- An operator inflated on the second factor acts on the dilated state exactly
as the original operator acts on the original state. Formalization-only support
for `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:266-288`. -/
theorem applyOperatorToState_heteroKron_one_naimarkInflation :
    applyOperatorToState
        (heteroKron (1 : Op (ιA × Option α))
          (MagicSquareRigidity.naimarkInflation (α := α) N))
        (MagicSquareRigidity.naimarkDilatedState α ψ) =
      MagicSquareRigidity.naimarkDilatedState α
        (applyOperatorToState (heteroKron (1 : Op ιA) N) ψ) := by
  classical
  ext p
  rw [MagicSquareRigidity.applyOperatorToState_naimarkDilatedState,
    MagicSquareRigidity.naimarkDilatedState_apply]
  obtain ⟨⟨i, oa⟩, ⟨j, ob⟩⟩ := p
  by_cases hoa : oa = none
  · by_cases hob : ob = none
    · subst hoa
      simp [heteroKron, applyOperatorToState, Matrix.mulVec, dotProduct,
        Fintype.sum_prod_type, Matrix.one_apply]
    · simp [hob, heteroKron]
  · simp [hoa, heteroKron]

end

/-! ## The Magic Square anticommutation on the undilated strategy -/

/-- Bob's Magic Square variable observables approximately anticommute on the
strategy state. This auxiliary estimate is proved on the projective dilation
and read back through the ground slice. Paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-356`,
blueprint `lem:qld-ms-anticommutator-original-state`. -/
theorem msVarObs_anticommutator_le (S : Strategy msGame) (ε : ℝ) (hε : 0 ≤ ε)
    (hwin : 1 - ε ≤ S.value) :
    ‖applyOperatorToState
        (heteroKron (1 : Op S.ιA)
          (obsOf ((S.B (.var 0)).postprocess msBitOrZero) *
              obsOf ((S.B (.var 4)).postprocess msBitOrZero) +
            obsOf ((S.B (.var 4)).postprocess msBitOrZero) *
              obsOf ((S.B (.var 0)).postprocess msBitOrZero)))
        S.ψ‖ ^ 2 ≤ 1183680 * ε := by
  let readout := (S.B (.var 0)).postprocess msBitOrZero
  classical
  set xi : EuclideanSpace ℂ
      ((S.ιA × Option MsAnswer) × (S.ιB × Option MsAnswer)) :=
    MagicSquareRigidity.naimarkDilatedState MsAnswer S.ψ with hxidef
  have hxi : ‖isometryTensor
      (LinearIsometry.id)
      (LinearIsometry.id) xi - xi‖ ≤ 0 := by
    simp [isometryTensor_id]
  have htrans := MagicSquareRigidity.ms_anticommutator_transfer_B S
    _
    _ xi ε 0 hwin hxi
  simp only [MagicSquareRigidity.conjIsometry_comp_naimarkEmbedding,
    conjIsometry_id, MagicSquareRigidity.opDistSq_uniform_unit] at htrans
  have hL : heteroKron 1
        (MagicSquareRigidity.naimarkInflation
          (obsOf readout)) *
        heteroKron 1 (MagicSquareRigidity.naimarkInflation
          (obsOf ((S.B (.var 4)).postprocess msBitOrZero))) -
      -(heteroKron 1 (MagicSquareRigidity.naimarkInflation
          (obsOf ((S.B (.var 4)).postprocess msBitOrZero))) *
        heteroKron 1 (MagicSquareRigidity.naimarkInflation
          (obsOf readout))) =
      heteroKron (1 : Op (S.ιA × Option MsAnswer))
        (MagicSquareRigidity.naimarkInflation (α := MsAnswer)
          (obsOf readout *
              obsOf ((S.B (.var 4)).postprocess msBitOrZero) +
            obsOf ((S.B (.var 4)).postprocess msBitOrZero) *
              obsOf readout)) := by
    simp [heteroKron_mul, sub_neg_eq_add, MagicSquareRigidity.naimarkInflation_mul, ← heteroKron_add_right, naimarkInflation_add]
  rw [hL, applyOperatorToState_heteroKron_one_naimarkInflation, MagicSquareRigidity.naimarkDilatedState_norm] at htrans
  have hclose := MagicSquareRigidity.msVarObsB_anticommute S ε hwin
  simp [MagicSquareRigidity.msVarObsB, MagicSquareRigidity.signObs_eq_obsOf_postprocess] at hclose
  have hnorm := hclose
  have hsq : ‖applyOperatorToState
      (heteroKron 1
          (MagicSquareRigidity.dilatedObsB S (.var 0) msBitOrZero) *
        heteroKron 1
          (MagicSquareRigidity.dilatedObsB S (.var 4) msBitOrZero) -
        -(heteroKron 1
            (MagicSquareRigidity.dilatedObsB S (.var 4) msBitOrZero) *
          heteroKron 1
            (MagicSquareRigidity.dilatedObsB S (.var 0) msBitOrZero)))
      (MagicSquareRigidity.naimarkDilatedState MsAnswer S.ψ)‖ ^ 2 ≤
        389376 * ε := by
    have hnn : 0 ≤ 624 * Real.sqrt ε := by positivity
    calc _ ≤ _ :=
          (sq_le_sq₀ (norm_nonneg _) hnn).2 hnorm
      _ = 389376 * ε := by
          rw [mul_pow, Real.sq_sqrt hε]
          ring
  linarith

section

variable (α : Type) [Fintype α] [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
  [Fintype ιB] [DecidableEq ιB] (M : Op ιA) (ψ : EuclideanSpace ℂ (ιA × ιB))

end

/-! ## Reflections and the product transfer -/

section

variable {ιA ιB : Type*}

/-- Placing an isometry on the first factor gives an isometry.
Formalization-only support for `fact:add-a-proj`, blueprint
`ch12_qpbt_games.tex:305-321`. -/
theorem heteroKron_left_isometry [DecidableEq ιA]
    [DecidableEq ιB] [Fintype ιA] [Fintype ιB] {A : Op ιA}
    (hA : Aᴴ * A = 1) :
    (heteroKron A (1 : Op ιB))ᴴ * heteroKron A 1 = 1 := by
  simp [heteroKron_conjTranspose, heteroKron_mul, hA, Matrix.conjTranspose_one, heteroKron_one_one]

/-- Placing an isometry on the second factor gives an isometry.
Formalization-only support for `fact:add-a-proj`, blueprint
`ch12_qpbt_games.tex:305-321`. -/
theorem heteroKron_right_isometry [DecidableEq ιA]
    [DecidableEq ιB] [Fintype ιA] [Fintype ιB] (B : Op ιB)
    (hB : Bᴴ * B = 1) :
    (heteroKron (1 : Op ιA) B)ᴴ * heteroKron 1 B = 1 := by
  simp [heteroKron_conjTranspose, heteroKron_mul, hB, Matrix.conjTranspose_one, heteroKron_one_one]

end

/-- The observable of a binary projective measurement is a reflection.
Formalization-only support for `lem:povm-to-obs`, blueprint
`ch14_qpbt_observables.tex:365-382`. -/
theorem obsOf_conjTranspose_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement (ZMod 2) ι)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    (obsOf M)ᴴ * obsOf M = 1 := by
  have h01 : M.effect 0 * M.effect 1 = 0 :=
    DistanceCalculus.projective_effect_mul_effect_eq_zero M hM (by decide)
  have h10 : M.effect 1 * M.effect 0 = 0 :=
    DistanceCalculus.projective_effect_mul_effect_eq_zero M hM (by decide)
  have hherm : (obsOf M)ᴴ = obsOf M := by
    simp [obsOf, Matrix.conjTranspose_sub, (Matrix.nonneg_iff_posSemidef.mp (M.pos 0)).isHermitian.eq, (Matrix.nonneg_iff_posSemidef.mp (M.pos 1)).isHermitian.eq]
  rw [hherm, obsOf, sub_mul, mul_sub, mul_sub, h01, h10,
    (hM 0).isIdempotentElem.eq, (hM 1).isIdempotentElem.eq]
  simp
  have := M.sum_eq_one
  rwa [sum_zmod_two] at this

/-- Transferring a product across the tensor factors costs the two individual
distances: if `A` on the first factor is close to `B` on the second and `C` on
the first is close to `D` on the second, then `A * C` on the first factor is
close to `D * B` on the second. The second factor's product is read in the
reversed order because the correspondence between the two factors determined by
the state is an antihomomorphism, so it carries a product of first-factor
operators to the product of their partners taken in the opposite order.

This is the isometry case of `fact:add-a-proj` applied twice and combined with
the triangle inequality; `fact:add-a-proj` itself is blueprint
`ch12_qpbt_games.tex:305-321`, paper
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:352-362`. -/
theorem norm_product_transfer_le {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] (A C : Op ιA) (B D : Op ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB))
    (hA : (heteroKron A (1 : Op ιB))ᴴ * heteroKron A 1 = 1)
    (hD : (heteroKron (1 : Op ιA) D)ᴴ * heteroKron 1 D = 1) :
    ‖applyOperatorToState
        (heteroKron (A * C) (1 : Op ιB) - heteroKron 1 (D * B)) ψ‖ ≤
      ‖applyOperatorToState
        (heteroKron C (1 : Op ιB) - heteroKron 1 D) ψ‖ +
      ‖applyOperatorToState
        (heteroKron A (1 : Op ιB) - heteroKron 1 B) ψ‖ := by
  have hsplit : heteroKron (A * C) 1 - heteroKron 1 (D * B) =
      heteroKron A 1 * (heteroKron C 1 - heteroKron 1 D) +
        heteroKron 1 D * (heteroKron A 1 - heteroKron 1 B) := by
    simp [mul_sub, heteroKron_mul]
  rw [hsplit, MagicSquareRigidity.applyOperatorToState_add_op]
  refine le_trans (norm_add_le _ _) ?_
  rw [MagicSquareRigidity.norm_applyOperatorToState_isometry_mul hA,
    MagicSquareRigidity.norm_applyOperatorToState_isometry_mul hD]

/-! ## From the Magic Square variables to the point observables -/

/-- The signed sum of the effects of a binary measurement is its observable.
Formalization-only support for `lem:povm-to-obs`, blueprint
`ch14_qpbt_observables.tex:365-382`. -/
theorem sum_phaseSign_smul_effect_eq_obsOf {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : MIPStarRE.Quantum.Measurement (ZMod 2) ι) :
    ∑ b : ZMod 2, phaseSign b • M.effect b = obsOf M := by
  rw [sum_zmod_two, obsOf]
  have hzero : phaseSign 0 = 1 := by rfl
  have hone : phaseSign 1 = -1 := by
    rfl
  simp_all
  abel

section

variable {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (side : PlayerSide)
  (W : PauliKind) (r : PauliScalar P) (u : PauliPoint P)

/-- The strategy point observable is the observable of the trace-coarse-grained
point measurement. This is `def:strategy-observables` read through
`lem:povm-to-obs`, paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`ch14_qpbt_observables.tex:573-610`. -/
theorem pointObs_eq_obsOf :
    S.pointObs side W r u = obsOf (S.pointTraceMeas side W u r) := by
  rw [pointObs_eq_traceMeas_obs, sum_phaseSign_smul_effect_eq_obsOf]

/-- The strategy point observable is a reflection. Paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`ch14_qpbt_observables.tex:573-610`. -/
theorem pointObs_conjTranspose_mul_self :
    (S.pointObs side W r u)ᴴ * S.pointObs side W r u = 1 := by
  rw [(S.pointObs_isHermitian side W r u).eq]
  apply S.pointObs_sq_eq_one

end

/-- Consistency of two oppositely placed binary measurements bounds the
operator distance of their observables. This is `lem:povm-to-obs` in the form
used by Equations `eq:lc-11a` and `eq:lc-11b`; the statement is generic in the
two tensor factors and the state. Paper
`14_analysis_of_the_pauli_basis_test.tex:342-348`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem obsDist_le_of_consistencyDefect {X ιL ιR : Type*}
    [Fintype X] [DecidableEq X] [Fintype ιL] [DecidableEq ιL]
    [Fintype ιR] [DecidableEq ιR] (μ : Distribution X)
    (M : X → MIPStarRE.Quantum.Measurement (ZMod 2) ιL)
    (N : X → MIPStarRE.Quantum.Measurement (ZMod 2) ιR)
    (χ : EuclideanSpace ℂ (ιL × ιR)) {c : ℝ}
    (h : bipartiteDefect μ M
      N χ ≤ c) :
    opDistSq μ (fun x => heteroKron (obsOf (M x)) (1 : Op ιR))
      (fun x => heteroKron (1 : Op ιL) (obsOf (N x))) χ ≤ 4 * c := by
  classical
  set A : X → MIPStarRE.Quantum.Measurement (ZMod 2) (ιL × ιR) := fun x =>
    DistanceCalculus.leftPlacedMeasurement (M x) with hAdef
  set B : X → MIPStarRE.Quantum.Measurement (ZMod 2) (ιL × ιR) := fun x =>
    DistanceCalculus.rightPlacedMeasurement (N x) with hBdef
  have hleft : ∀ x, (∑ b : ZMod 2, phaseSign b • (A x).effect b) =
      heteroKron (obsOf (M x)) 1 := by
    intro x
    rw [← sum_phaseSign_smul_effect_eq_obsOf, heteroKron_left_sum_smul]
    rfl
  have hright : ∀ x, (∑ b : ZMod 2, phaseSign b • (B x).effect b) =
      heteroKron 1 (obsOf (N x)) := by
    intro x
    rw [← sum_phaseSign_smul_effect_eq_obsOf, heteroKron_right_sum_smul]
    rfl
  have hrw : opDistSq μ (fun x => heteroKron (obsOf (M x)) 1)
      (fun x => heteroKron 1 (obsOf (N x))) χ =
    opDistSq μ (fun x => ∑ b : ZMod 2, phaseSign b • (A x).effect b)
      (fun x => ∑ b : ZMod 2, phaseSign b • (B x).effect b) χ := by
    simp_all
  rw [hrw]
  have hcast : (Fintype.card (ZMod 2)) = 2 := by simp
  calc
    _ ≤ _ := (povm_to_obs_of_measurements μ A B norm_phaseSign χ)
    _ ≤ 2 * (2 * c) := by
      exact mul_le_mul_of_nonneg_left (opFamilyDistSq_placed_le_of_consistencyDefect_le h) (by norm_num)
    _ = 4 * c := by ring

/-! ## The anticommuting half of the twisted commutation -/

/-- The unit-alphabet operator distance written as an average of squared
state-dependent norms. Formalization-only support for `def:povm-distance`,
blueprint `ch12_qpbt_games.tex:234-241`. -/
theorem opDistSq_eq_avgOver {X ι : Type*} [Fintype X] [DecidableEq X]
    [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (M N : X → Op ι) (ψ : EuclideanSpace ℂ ι) :
    opDistSq μ M N ψ =
      avgOver μ (fun x => ‖applyOperatorToState (M x - N x) ψ‖ ^ 2) := by
  unfold opDistSq opFamilyDistSq
  simp

section

variable {P : AdmissibleParams}

section

variable {ε : ℝ} (S : ProjectiveSetting P ε) (ω : PauliTuple P)

/-- The Magic Square value defect of a tuple is nonnegative and admissible as
an error parameter for the rigidity input. Formalization-only support for
`eq:qld-implication-ms-anticomm`, paper
`14_analysis_of_the_pauli_basis_test.tex:349-356`. -/
theorem msValueAt_defect_nonneg :
    0 ≤ 1 - S.msValueAt ω ∧
      1 - (1 - S.msValueAt ω) ≤ (S.msStrategyAt ω).value := by
  have hle := Strategy.value_le_one (S.msStrategyAt ω)
  have heq : S.msValueAt ω = (S.msStrategyAt ω).value := rfl
  simp_all

end

/-- The two point observables approximately anticommute once each of them is
close to a Magic Square variable observable on the opposite factor and those
two anticommute. This is the anticommuting half of Equation
`eq:pts-obs-commutation`, stated generically in the two tensor factors and the
state. Paper `14_analysis_of_the_pauli_basis_test.tex:342-362`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem obs_anticommutator_avg_le {ιL ιR : Type}
    [Fintype ιL] [DecidableEq ιL] [Fintype ιR] [DecidableEq ιR]
    (OX OZ : PauliTuple P → Op ιL) (V0 V4 : PauliTuple P → Op ιR)
    (χ : EuclideanSpace ℂ (ιL × ιR)) {cd cv : ℝ}
    (hOX : ∀ ω, (OX ω)ᴴ * OX ω = 1) (hOZ : ∀ ω, (OZ ω)ᴴ * OZ ω = 1)
    (hV0 : ∀ ω, (V0 ω)ᴴ * V0 ω = 1) (hV4 : ∀ ω, (V4 ω)ᴴ * V4 ω = 1)
    (h0 : avgOver (anticommTupleDist P) (fun ω => ‖applyOperatorToState
        (heteroKron (OX ω) (1 : Op ιR) -
          heteroKron (1 : Op ιL) (V0 ω)) χ‖ ^ 2) ≤ cd)
    (h4 : avgOver (anticommTupleDist P) (fun ω => ‖applyOperatorToState
        (heteroKron (OZ ω) (1 : Op ιR) -
          heteroKron (1 : Op ιL) (V4 ω)) χ‖ ^ 2) ≤ cd)
    (hv : avgOver (anticommTupleDist P) (fun ω => ‖applyOperatorToState
        (heteroKron (1 : Op ιL) (V0 ω * V4 ω + V4 ω * V0 ω)) χ‖ ^ 2) ≤ cv) :
    avgOver (anticommTupleDist P) (fun ω => ‖applyOperatorToState
      (heteroKron (OX ω * OZ ω) (1 : Op ιR) +
        heteroKron (OZ ω * OX ω) (1 : Op ιR)) χ‖ ^ 2) ≤
      24 * cd + 3 * cv := by
  classical
  have hpoint : ∀ ω : PauliTuple P,
      ‖applyOperatorToState
          (heteroKron (OX ω * OZ ω) 1 +
            heteroKron (OZ ω * OX ω) 1) χ‖ ^ 2 ≤
        12 * ‖applyOperatorToState (heteroKron (OX ω) 1 -
            heteroKron 1 (V0 ω)) χ‖ ^ 2 +
        12 * ‖applyOperatorToState (heteroKron (OZ ω) 1 -
            heteroKron 1 (V4 ω)) χ‖ ^ 2 +
        3 * ‖applyOperatorToState
            (heteroKron 1 (V0 ω * V4 ω + V4 ω * V0 ω)) χ‖ ^ 2 := by
    intro ω
    have h1 := norm_product_transfer_le _ (OZ ω) (V0 ω) _ χ
      (heteroKron_left_isometry (hOX ω))
      (heteroKron_right_isometry (V4 ω) (hV4 ω))
    have h2 := norm_product_transfer_le _ (OX ω) (V4 ω) _ χ
      (heteroKron_left_isometry (hOZ ω))
      (heteroKron_right_isometry (V0 ω) (hV0 ω))
    have hdecomp : heteroKron (OX ω * OZ ω) 1 +
        heteroKron (OZ ω * OX ω) 1 =
      (heteroKron (OX ω * OZ ω) 1 -
          heteroKron 1 (V4 ω * V0 ω)) +
        (heteroKron (OZ ω * OX ω) 1 -
          heteroKron 1 (V0 ω * V4 ω)) +
        heteroKron 1 (V0 ω * V4 ω + V4 ω * V0 ω) := by
      rw [heteroKron_add_right]
      abel
    set t1 : ℝ := ‖applyOperatorToState (heteroKron (OX ω) 1 -
      heteroKron 1 (V0 ω)) χ‖ with ht1
    set t2 : ℝ := ‖applyOperatorToState (heteroKron (OZ ω) 1 -
      heteroKron 1 (V4 ω)) χ‖ with ht2
    set t3 : ℝ := ‖applyOperatorToState
      (heteroKron 1 (V0 ω * V4 ω + V4 ω * V0 ω)) χ‖ with ht3
    set t0 : ℝ := ‖applyOperatorToState (heteroKron (OX ω * OZ ω) 1 +
      heteroKron (OZ ω * OX ω) 1) χ‖ with ht0
    have hsum : t0 ≤
        ‖applyOperatorToState (heteroKron (OX ω * OZ ω) 1 -
            heteroKron 1 (V4 ω * V0 ω)) χ‖ +
          ‖applyOperatorToState (heteroKron (OZ ω * OX ω) 1 -
            heteroKron 1 (V0 ω * V4 ω)) χ‖ + t3 := by
      simp [ht0, ht3, hdecomp, MagicSquareRigidity.applyOperatorToState_add_op]
      exact le_trans (norm_add_le _ _)
        (add_le_add (norm_add_le _ _) le_rfl)
    have ht0nn : 0 ≤ t0 := by exact norm_nonneg _
    have ht1nn : 0 ≤ t1 := by exact norm_nonneg _
    have ht2nn : 0 ≤ t2 := by exact norm_nonneg _
    have ht3nn : 0 ≤ t3 := by exact norm_nonneg _
    have hbound : t0 ≤ 2 * t1 + 2 * t2 + t3 := by linarith
    have key : t0 ^ 2 ≤ 12 * t1 ^ 2 + 12 * t2 ^ 2 + 3 * t3 ^ 2 := by
      nlinarith [hbound, ht0nn, ht1nn, ht2nn, ht3nn,
        sq_nonneg (t1 - t2), sq_nonneg (2 * t1 - t3), sq_nonneg (2 * t2 - t3)]
    assumption
  calc
    _ ≤ _ :=
      avgOver_mono _ _ _ hpoint
    _ = 12 * avgOver (anticommTupleDist P) (fun ω =>
          ‖applyOperatorToState (heteroKron (OX ω) 1 -
            heteroKron 1 (V0 ω)) χ‖ ^ 2) +
        12 * avgOver (anticommTupleDist P) (fun ω =>
          ‖applyOperatorToState (heteroKron (OZ ω) 1 -
            heteroKron 1 (V4 ω)) χ‖ ^ 2) +
        3 * avgOver (anticommTupleDist P) (fun ω =>
          ‖applyOperatorToState
            (heteroKron 1
              (V0 ω * V4 ω + V4 ω * V0 ω)) χ‖ ^ 2) := by
      simp [avgOver_add, avgOver_const_mul]
    _ ≤ _ := by linarith

/-- The observable of a binary projective measurement obtained from a strategy
measurement by two postprocessings is a reflection. Formalization-only support
for `eq:qld-implication-ms-anticomm`, blueprint
`lem:qld-win-implications-obs`. -/
theorem msVarBitObs_conjTranspose_mul_self {ε : ℝ}
    (S : ProjectiveSetting P ε) (side : PlayerSide) (j : Fin 9)
    (ω : PauliTuple P) :
    (obsOf (S.msVarBitMeas side j ω))ᴴ *
      obsOf (S.msVarBitMeas side j ω) = 1 := by
  apply obsOf_conjTranspose_mul_self
  refine SandwichProduct.postprocess_isProjective _
    (SandwichProduct.postprocess_isProjective _ ?_ _) _
  cases side with
  | alice => exact S.isProjective.1 _
  | bob => exact S.isProjective.2 _

/-- The observable of a trace-coarse-grained point measurement is a
reflection. Paper `14_analysis_of_the_pauli_basis_test.tex:174-190`,
blueprint `ch14_qpbt_observables.tex:573-610`. -/
theorem pointTraceObs_conjTranspose_mul_self {ε : ℝ}
    (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)
    (u : PauliPoint P) (r : PauliScalar P) :
    (obsOf (S.pointTraceMeas side W u r))ᴴ *
      obsOf (S.pointTraceMeas side W u r) = 1 := by
  rw [← pointObs_eq_obsOf]
  apply pointObs_conjTranspose_mul_self

end

/-- The point observables approximately anticommute on anticommuting tuples.
This is the anticommuting half of Equation `eq:pts-obs-commutation`, paper
`14_analysis_of_the_pauli_basis_test.tex:342-362`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem point_obs_anticommutator_anticomm_le_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε), 0 ≤ ε →
      avgOver (anticommTupleDist P) (fun ω =>
        ‖applyOperatorToState
          (heteroKron (S.pointObs .alice .X ω.2.2.1 ω.1 *
              S.pointObs .alice .Z ω.2.2.2 ω.2.1) (1 : Op S.toStrategy.ιB) +
            heteroKron (S.pointObs .alice .Z ω.2.2.2 ω.2.1 *
              S.pointObs .alice .X ω.2.2.1 ω.1) (1 : Op S.toStrategy.ιB))
          S.toStrategy.ψ‖ ^ 2) ≤
        (96 * (16 * (Fintype.card PauliEdge : ℝ)) +
          3551040 * (16 * (Fintype.card PauliEdge : ℝ))) * ε := by
  classical
  intro P ε S hε
  simp only [pointObs_eq_obsOf]
  have hdist : ∀ W : PauliKind,
      avgOver (anticommTupleDist P) (fun ω => ‖applyOperatorToState
        (heteroKron
            (obsOf (S.pointTraceMeas .alice W (selectedTuplePoint W ω)
              (selectedTupleScalar W ω))) 1 -
          heteroKron 1
            (obsOf (S.msVarBitMeas .bob (selectedMsVar W) ω)))
        S.toStrategy.ψ‖ ^ 2) ≤
          4 * ((16 * (Fintype.card PauliEdge)) * ε) := by
    intro W
    have h := obsDist_le_of_consistencyDefect _
      _
      _ S.toStrategy.ψ
      (win_ms_cons_explicit P ε S hε W)
    rw [opDistSq_eq_avgOver] at h
    exact h
  have hdefect : avgOver (anticommTupleDist P)
      (fun ω => 1 - S.msValueAt ω) ≤
        (16 * (Fintype.card PauliEdge)) * ε := by
    have hprob := anticommTupleDist_isProbability P
    rw [avgOver_sub, avgOver_const_of_isProbability _ hprob]
    exact le_of_abs_le (win_magic_square_explicit P ε S hε)
  have hmain := obs_anticommutator_avg_le
    _
    _
    _
    _ S.toStrategy.ψ
    (fun ω => pointTraceObs_conjTranspose_mul_self S .alice .X ω.1 ω.2.2.1)
    (fun ω => pointTraceObs_conjTranspose_mul_self S .alice .Z ω.2.1 ω.2.2.2)
    (msVarBitObs_conjTranspose_mul_self S .bob 0)
    (msVarBitObs_conjTranspose_mul_self S .bob 4)
    (hdist .X) (hdist .Z) (by
      calc
        _ ≤ avgOver (anticommTupleDist P)
            (fun ω => 1183680 * (1 - S.msValueAt ω)) :=
          avgOver_mono _ _ _ (fun ω => (by
                                         obtain ⟨hnn, hwin⟩ := msValueAt_defect_nonneg S ω
                                         exact msVarObs_anticommutator_le (S.msStrategyAt ω) _ hnn
                                           hwin))
        _ = 1183680 * avgOver (anticommTupleDist P)
            (fun ω => 1 - S.msValueAt ω) := avgOver_const_mul _ _ _
        _ ≤ _ :=
          mul_le_mul_of_nonneg_left hdefect (by norm_num))
  linarith

end WinImplications

end

end MIPStarRE.QPBT
