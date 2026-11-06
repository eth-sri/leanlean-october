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

/-- Inflation to the ground slice is additive. Formalization-only support for
`thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:266-288`. -/
theorem naimarkInflation_add {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M N : Op ι) :
    MagicSquareRigidity.naimarkInflation (α := α) M +
        MagicSquareRigidity.naimarkInflation (α := α) N =
      MagicSquareRigidity.naimarkInflation (α := α) (M + N) := by
  ext p q
  by_cases h : p.2 = none ∧ q.2 = none <;> simp [h]

variable (α : Type) [Fintype α] [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]

/-- An operator inflated on the second factor acts on the dilated state exactly
as the original operator acts on the original state. Formalization-only support
for `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:266-288`. -/
theorem applyOperatorToState_heteroKron_one_naimarkInflation
    (N : Op ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    applyOperatorToState
        (heteroKron (1 : Op (ιA × Option α))
          (MagicSquareRigidity.naimarkInflation (α := α) N))
        (MagicSquareRigidity.naimarkDilatedState α ψ) =
      MagicSquareRigidity.naimarkDilatedState α
        (applyOperatorToState (heteroKron (1 : Op ιA) N) ψ) := by
  ext p
  rw [MagicSquareRigidity.applyOperatorToState_naimarkDilatedState,
    MagicSquareRigidity.naimarkDilatedState_apply]
  obtain ⟨⟨i, oa⟩, ⟨j, ob⟩⟩ := p
  by_cases hoa : oa = none
  · simp_all [heteroKron, applyOperatorToState, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]
  simp_all [heteroKron]

/-- The state-dependent norm of an operator inflated on the second factor,
measured on the dilated state, is the norm of the original operator on the
original state. Formalization-only support for `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:266-288`. -/
theorem norm_heteroKron_one_naimarkInflation
    (N : Op ιB) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    ‖applyOperatorToState
        (heteroKron (1 : Op (ιA × Option α))
          (MagicSquareRigidity.naimarkInflation (α := α) N))
        (MagicSquareRigidity.naimarkDilatedState α ψ)‖ =
      ‖applyOperatorToState (heteroKron (1 : Op ιA) N) ψ‖ := by
  rw [applyOperatorToState_heteroKron_one_naimarkInflation,
    MagicSquareRigidity.naimarkDilatedState_norm]

/-! ## The Magic Square anticommutation on the undilated strategy -/

variable (S : Strategy msGame)

/-- Bob's Magic Square variable reflections are the placed observables of his
totalized variable measurements on the dilated strategy. Formalization-only
support for `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:266-288`. -/
theorem msVarObsB_eq (j : Fin 9) :
    MagicSquareRigidity.msVarObsB S j =
      heteroKron (1 : Op (S.ιA × Option MsAnswer))
        (MagicSquareRigidity.dilatedObsB S (.var j) msBitOrZero) := by
  rw [MagicSquareRigidity.msVarObsB,
    MagicSquareRigidity.signObs_eq_obsOf_postprocess]
  rfl

/-- Bob's Magic Square variable observables approximately anticommute on the
strategy state. This auxiliary estimate is proved on the projective dilation
and read back through the ground slice. Paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-356`,
blueprint `lem:qld-ms-anticommutator-original-state`. -/
theorem msVarObs_anticommutator_le (ε : ℝ) (hε : 0 ≤ ε)
    (hwin : 1 - ε ≤ S.value) :
    ‖applyOperatorToState
        (heteroKron (1 : Op S.ιA)
          (obsOf ((S.B (.var 0)).postprocess msBitOrZero) *
              obsOf ((S.B (.var 4)).postprocess msBitOrZero) +
            obsOf ((S.B (.var 4)).postprocess msBitOrZero) *
              obsOf ((S.B (.var 0)).postprocess msBitOrZero)))
        S.ψ‖ ^ 2 ≤ 1183680 * ε := by
  have htrans := MagicSquareRigidity.ms_anticommutator_transfer_B S ε hwin
  have hclose := MagicSquareRigidity.msVarObsB_anticommute S ε hwin
  rw [MagicSquareRigidity.NormCloseOn, msVarObsB_eq, msVarObsB_eq] at hclose
  refine le_trans (le_of_eq ?_) (htrans.trans ?_)
  · simp only [heteroKron_mul, one_mul, sub_neg_eq_add, MagicSquareRigidity.naimarkInflation_mul,
      ← heteroKron_add_right, naimarkInflation_add, norm_heteroKron_one_naimarkInflation]
  · calc _ ≤ 3 * (624 * √ε) ^ 2 + 15552 * ε := by gcongr; exact hclose
      _ = _ := by rw [mul_pow, Real.sq_sqrt hε]; ring

/-- An operator inflated on the first factor acts on the dilated state exactly
as the original operator acts on the original state. Formalization-only support
for `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:266-288`. -/
theorem applyOperatorToState_heteroKron_naimarkInflation_one
    (M : Op ιA) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    applyOperatorToState
        (heteroKron (MagicSquareRigidity.naimarkInflation (α := α) M)
          (1 : Op (ιB × Option α)))
        (MagicSquareRigidity.naimarkDilatedState α ψ) =
      MagicSquareRigidity.naimarkDilatedState α
        (applyOperatorToState (heteroKron M (1 : Op ιB)) ψ) := by
  ext p
  rw [MagicSquareRigidity.applyOperatorToState_naimarkDilatedState,
    MagicSquareRigidity.naimarkDilatedState_apply]
  obtain ⟨⟨i, oa⟩, ⟨j, ob⟩⟩ := p
  by_cases hoa : oa = none
  · by_cases hob : ob = none
    · simp_all [heteroKron, applyOperatorToState, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]
    simp_all [heteroKron]
  simp_all [heteroKron]

/-- The state-dependent norm of an operator inflated on the first factor,
measured on the dilated state, is the norm of the original operator on the
original state. Formalization-only support for `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:266-288`. -/
theorem norm_heteroKron_naimarkInflation_one
    (M : Op ιA) (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    ‖applyOperatorToState
        (heteroKron (MagicSquareRigidity.naimarkInflation (α := α) M)
          (1 : Op (ιB × Option α)))
        (MagicSquareRigidity.naimarkDilatedState α ψ)‖ =
      ‖applyOperatorToState (heteroKron M (1 : Op ιB)) ψ‖ := by
  rw [applyOperatorToState_heteroKron_naimarkInflation_one,
    MagicSquareRigidity.naimarkDilatedState_norm]

/-- Alice's Magic Square variable reflections are the placed observables of her
totalized variable measurements on the dilated strategy. Formalization-only
support for `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:266-288`. -/
theorem msVarObsA_eq (j : Fin 9) :
    MagicSquareRigidity.msVarObsA S j =
      heteroKron (MagicSquareRigidity.dilatedObsA S (.var j))
        (1 : Op (S.ιB × Option MsAnswer)) := by
  rw [MagicSquareRigidity.msVarObsA,
    MagicSquareRigidity.signObs_eq_obsOf_postprocess]
  rfl

/-- Alice's Magic Square variable observables approximately anticommute on the
strategy state. This auxiliary estimate is proved on the projective dilation
and read back through the ground slice on the first tensor factor. Paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-356`,
blueprint `lem:qld-ms-anticommutator-original-state`. -/
theorem msVarObsA_anticommutator_le (ε : ℝ) (hε : 0 ≤ ε)
    (hwin : 1 - ε ≤ S.value) :
    ‖applyOperatorToState
        (heteroKron
          (obsOf ((S.A (.var 0)).postprocess msBitOrZero) *
              obsOf ((S.A (.var 4)).postprocess msBitOrZero) +
            obsOf ((S.A (.var 4)).postprocess msBitOrZero) *
              obsOf ((S.A (.var 0)).postprocess msBitOrZero))
          (1 : Op S.ιB))
        S.ψ‖ ^ 2 ≤ 1183680 * ε := by
  have htrans := MagicSquareRigidity.ms_anticommutator_transfer_A S ε hwin
  have hclose := MagicSquareRigidity.msVarObsA_anticommute S ε hwin
  rw [MagicSquareRigidity.NormCloseOn, msVarObsA_eq, msVarObsA_eq] at hclose
  refine le_trans (le_of_eq ?_) (htrans.trans ?_)
  · simp only [heteroKron_mul, one_mul, sub_neg_eq_add, MagicSquareRigidity.naimarkInflation_mul,
      ← heteroKron_add_left, naimarkInflation_add, norm_heteroKron_naimarkInflation_one]
  · calc _ ≤ 3 * (624 * √ε) ^ 2 + 15552 * ε := by gcongr; exact hclose
      _ = _ := by rw [mul_pow, Real.sq_sqrt hε]; ring

/-! ## Reflections and the product transfer -/

/-- Placing an isometry on the first factor gives an isometry.
Formalization-only support for `fact:add-a-proj`, blueprint
`ch12_qpbt_games.tex:305-321`. -/
theorem heteroKron_left_isometry {ιA ιB : Type*} [DecidableEq ιA]
    [DecidableEq ιB] [Fintype ιA] [Fintype ιB] (A : Op ιA)
    (hA : Aᴴ * A = 1) :
    (heteroKron A (1 : Op ιB))ᴴ * heteroKron A 1 = 1 := by
  simp_all [heteroKron_conjTranspose, heteroKron_mul, Matrix.conjTranspose_one, heteroKron_one_one]

/-- Placing an isometry on the second factor gives an isometry.
Formalization-only support for `fact:add-a-proj`, blueprint
`ch12_qpbt_games.tex:305-321`. -/
theorem heteroKron_right_isometry {ιA ιB : Type*} [DecidableEq ιA]
    [DecidableEq ιB] [Fintype ιA] [Fintype ιB] (B : Op ιB)
    (hB : Bᴴ * B = 1) :
    (heteroKron (1 : Op ιA) B)ᴴ * heteroKron 1 B = 1 := by
  simp_all [heteroKron_conjTranspose, heteroKron_mul, Matrix.conjTranspose_one, heteroKron_one_one]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The observable of a binary projective measurement is a reflection.
Formalization-only support for `lem:povm-to-obs`, blueprint
`ch14_qpbt_observables.tex:365-382`. -/
theorem obsOf_conjTranspose_mul_self (M : MIPStarRE.Quantum.Measurement (ZMod 2) ι)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    (obsOf M)ᴴ * obsOf M = 1 := by
  have hsum : M.effect 0 + M.effect 1 = 1 := by
    have := M.sum_eq_one
    rwa [sum_zmod_two] at this
  have h01 : M.effect 0 * M.effect 1 = 0 :=
    DistanceCalculus.projective_effect_mul_effect_eq_zero M hM (by decide)
  have h10 : M.effect 1 * M.effect 0 = 0 :=
    DistanceCalculus.projective_effect_mul_effect_eq_zero M hM (by decide)
  have hherm : (obsOf M)ᴴ = obsOf M := by
    rw [obsOf, Matrix.conjTranspose_sub]
    rw [(Matrix.nonneg_iff_posSemidef.mp (M.pos 0)).isHermitian.eq,
      (Matrix.nonneg_iff_posSemidef.mp (M.pos 1)).isHermitian.eq]
  rw [hherm, obsOf, sub_mul, mul_sub, mul_sub, h01, h10,
    (hM 0).isIdempotentElem.eq, (hM 1).isIdempotentElem.eq]
  simp_all

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
  have hsplit : heteroKron (A * C) (1 : Op ιB) - heteroKron 1 (D * B) =
      heteroKron A 1 * (heteroKron C (1 : Op ιB) - heteroKron 1 D) +
        heteroKron 1 D * (heteroKron A (1 : Op ιB) - heteroKron 1 B) := by
    rw [mul_sub, mul_sub, heteroKron_mul, heteroKron_mul, heteroKron_mul,
      heteroKron_mul]
    simp only [mul_one, one_mul]
    abel
  grind [MagicSquareRigidity.applyOperatorToState_add_op, le_trans, norm_add_le, MagicSquareRigidity.norm_applyOperatorToState_isometry_mul]

/-! ## From the Magic Square variables to the point observables -/

/-- The signed sum of the effects of a binary measurement is its observable.
Formalization-only support for `lem:povm-to-obs`, blueprint
`ch14_qpbt_observables.tex:365-382`. -/
theorem sum_phaseSign_smul_effect_eq_obsOf (M : MIPStarRE.Quantum.Measurement (ZMod 2) ι) :
    ∑ b : ZMod 2, phaseSign b • M.effect b = obsOf M := by
  rw [sum_zmod_two, obsOf]
  have hzero : phaseSign (0 : ZMod 2) = 1 := by simp [phaseSign]
  have hone : phaseSign (1 : ZMod 2) = -1 := by
    have h : (1 : ZMod 2) ≠ 0 := by decide
    simp [phaseSign, h]
  rw [hzero, hone, one_smul, neg_one_smul]
  abel

variable {P : AdmissibleParams} {ε : ℝ}

/-- The strategy point observable is the observable of the trace-coarse-grained
point measurement. This is `def:strategy-observables` read through
`lem:povm-to-obs`, paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`ch14_qpbt_observables.tex:573-610`. -/
theorem pointObs_eq_obsOf (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)
    (r : PauliScalar P) (u : Fin P.m → PauliScalar P) :
    S.pointObs side W r u = obsOf (S.pointTraceMeas side W u r) := by
  rw [pointObs_eq_traceMeas_obs, sum_phaseSign_smul_effect_eq_obsOf]

/-- The strategy point observable is a reflection. Paper
`14_analysis_of_the_pauli_basis_test.tex:174-190`, blueprint
`ch14_qpbt_observables.tex:573-610`. -/
theorem pointObs_conjTranspose_mul_self (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)
    (r : PauliScalar P) (u : Fin P.m → PauliScalar P) :
    (S.pointObs side W r u)ᴴ * S.pointObs side W r u = 1 := by
  rw [(S.pointObs_isHermitian side W r u).eq]
  exact S.pointObs_sq_eq_one side W r u

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
    (h : consistencyDefect μ (fun x a => heteroKron ((M x).effect a) 1)
      (fun x a => heteroKron 1 ((N x).effect a)) χ ≤ c) :
    opDistSq μ (fun x => heteroKron (obsOf (M x)) (1 : Op ιR))
      (fun x => heteroKron (1 : Op ιL) (obsOf (N x))) χ ≤ 4 * c := by
  have hobs := povm_to_obs_of_measurements μ
    (fun x => DistanceCalculus.leftPlacedMeasurement (ιB := ιR) (M x))
    (fun x => DistanceCalculus.rightPlacedMeasurement (ιA := ιL) (N x)) phaseSign norm_phaseSign χ
  have := opFamilyDistSq_placed_le_of_consistencyDefect_le μ M N χ h
  simp only [DistanceCalculus.leftPlacedMeasurement, DistanceCalculus.rightPlacedMeasurement,
    MIPStarRE.Quantum.Measurement.ofSumEqOne, ← heteroKron_left_sum_smul,
    ← heteroKron_right_sum_smul, sum_phaseSign_smul_effect_eq_obsOf, ZMod.card] at hobs this
  push_cast at hobs
  linarith

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

/-- The Magic Square value defect of a tuple is nonnegative and admissible as
an error parameter for the rigidity input. Formalization-only support for
`eq:qld-implication-ms-anticomm`, paper
`14_analysis_of_the_pauli_basis_test.tex:349-356`. -/
theorem msValueAt_defect_nonneg (S : ProjectiveSetting P ε) (ω : PauliTuple P) :
    0 ≤ 1 - S.msValueAt ω ∧
      1 - (1 - S.msValueAt ω) ≤ (S.msStrategyAt ω).value := by
  have hle := (S.msStrategyAt ω).value_le_one
  have heq : S.msValueAt ω = (S.msStrategyAt ω).value := rfl
  simp_all

theorem sq_le_of_triangle {t0 a b t1 t2 t3 : ℝ} (h : t0 ≤ a + b + t3) (h1 : a ≤ t2 + t1)
    (h2 : b ≤ t1 + t2) (h0 : 0 ≤ t0) : t0 ^ 2 ≤ 12 * t1 ^ 2 + 12 * t2 ^ 2 + 3 * t3 ^ 2 := by
  nlinarith [mul_self_le_mul_self h0 (h.trans (add_le_add_three h1 h2 le_rfl)),
    sq_nonneg (t1 - t2), sq_nonneg (2 * t1 - t3), sq_nonneg (2 * t2 - t3)]

/-- The two point observables approximately anticommute once each of them is
close to a Magic Square variable observable on the opposite factor and those
two anticommute. This is the anticommuting half of Equation
`eq:pts-obs-commutation`, stated generically in the two tensor factors and the
state. Paper `14_analysis_of_the_pauli_basis_test.tex:342-362`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem obs_anticommutator_avg_le {P : AdmissibleParams} {ιL ιR : Type}
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
  refine (avgOver_mono _ _ _ fun ω => sq_le_of_triangle
    (t3 := ‖applyOperatorToState (heteroKron (1 : Op ιL) (V0 ω * V4 ω + V4 ω * V0 ω)) χ‖)
    (norm_add₃_le.trans_eq' ?_) (norm_product_transfer_le (OX ω) (OZ ω) (V0 ω) (V4 ω) χ
      (heteroKron_left_isometry _ (hOX ω)) (heteroKron_right_isometry _ (hV4 ω)))
    (norm_product_transfer_le (OZ ω) (OX ω) (V4 ω) (V0 ω) χ
      (heteroKron_left_isometry _ (hOZ ω)) (heteroKron_right_isometry _ (hV0 ω)))
    (norm_nonneg _)).trans ?_
  · rw [← MagicSquareRigidity.applyOperatorToState_add_op,
      ← MagicSquareRigidity.applyOperatorToState_add_op, heteroKron_add_right]
    congr 2
    abel
  · simp only [avgOver_add, avgOver_const_mul]
    linarith

/-- The observable of a binary projective measurement obtained from a strategy
measurement by two postprocessings is a reflection. Formalization-only support
for `eq:qld-implication-ms-anticomm`, blueprint
`lem:qld-win-implications-obs`. -/
theorem msVarBitObs_conjTranspose_mul_self (S : ProjectiveSetting P ε) (side : PlayerSide) (j : Fin 9)
    (ω : PauliTuple P) :
    (obsOf (S.msVarBitMeas side j ω))ᴴ *
      obsOf (S.msVarBitMeas side j ω) = 1 := by
  refine obsOf_conjTranspose_mul_self (S.msVarBitMeas side j ω) ?_
  refine SandwichProduct.postprocess_isProjective _
    (SandwichProduct.postprocess_isProjective _ ?_ _) _
  cases side with
  | alice => exact S.isProjective.1 _
  | bob => exact S.isProjective.2 _

/-- The observable of a trace-coarse-grained point measurement is a
reflection. Paper `14_analysis_of_the_pauli_basis_test.tex:174-190`,
blueprint `ch14_qpbt_observables.tex:573-610`. -/
theorem pointTraceObs_conjTranspose_mul_self (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (r : PauliScalar P) :
    (obsOf (S.pointTraceMeas side W u r))ᴴ *
      obsOf (S.pointTraceMeas side W u r) = 1 := by
  rw [← pointObs_eq_obsOf]
  simp [pointObs_conjTranspose_mul_self]

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
  intro P ε S hε
  simp only [pointObs_eq_obsOf]
  have hdist := fun W => (opDistSq_eq_avgOver _ _ _ _).symm.trans_le
    (obsDist_le_of_consistencyDefect (anticommTupleDist P)
      (fun ω => S.pointTraceMeas .alice W (selectedTuplePoint W ω) (selectedTupleScalar W ω))
      (fun ω => S.msVarBitMeas .bob (selectedMsVar W) ω) S.toStrategy.ψ
      (win_ms_cons_explicit P ε S hε W))
  have hdefect : avgOver (anticommTupleDist P) (fun ω => 1 - S.msValueAt ω) ≤
      (16 * (Fintype.card PauliEdge : ℝ)) * ε := by
    rw [avgOver_sub, avgOver_const_of_isProbability _ (anticommTupleDist_isProbability P)]
    exact le_of_abs_le (win_magic_square_explicit P ε S hε)
  have hmsavg := (avgOver_mono (anticommTupleDist P) _ _ fun ω =>
    msVarObs_anticommutator_le (S.msStrategyAt ω) _ (msValueAt_defect_nonneg S ω).1 (msValueAt_defect_nonneg S ω).2).trans_eq
    (avgOver_const_mul _ _ _)
  have hmain := obs_anticommutator_avg_le (ιL := S.toStrategy.ιA)
    (ιR := S.toStrategy.ιB)
    (fun ω => obsOf (S.pointTraceMeas .alice .X ω.1 ω.2.2.1))
    (fun ω => obsOf (S.pointTraceMeas .alice .Z ω.2.1 ω.2.2.2))
    (fun ω => obsOf (S.msVarBitMeas .bob 0 ω))
    (fun ω => obsOf (S.msVarBitMeas .bob 4 ω)) S.toStrategy.ψ
    (fun ω => pointTraceObs_conjTranspose_mul_self S .alice .X ω.1 ω.2.2.1)
    (fun ω => pointTraceObs_conjTranspose_mul_self S .alice .Z ω.2.1 ω.2.2.2)
    (fun ω => msVarBitObs_conjTranspose_mul_self S .bob 0 ω)
    (fun ω => msVarBitObs_conjTranspose_mul_self S .bob 4 ω)
    (hdist .X) (hdist .Z) hmsavg
  linarith

end WinImplications

end

end MIPStarRE.QPBT
