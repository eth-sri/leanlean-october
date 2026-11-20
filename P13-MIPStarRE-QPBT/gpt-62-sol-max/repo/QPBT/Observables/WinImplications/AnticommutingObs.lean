module

public import QPBT.Observables.WinImplications.CommutingObs
public import QPBT.Test.MagicSquareTheorems.Rigidity.Anticommutation
public import QPBT.Test.MagicSquareTheorems.Rigidity.Transfer

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

/-! ## Anticommutation on the original space -/

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

variable (α : Type) [Fintype α] [DecidableEq α]
    {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : Op ιA) (ψ : EuclideanSpace ℂ (ιA × ιB))
include α ιA ιB M ψ

/-- An operator inflated on the first factor acts on the dilated state exactly
as the original operator acts on the original state. Formalization-only support
for `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:266-288`. -/
theorem applyOperatorToState_heteroKron_naimarkInflation_one :
    applyOperatorToState
        (heteroKron (MagicSquareRigidity.naimarkInflation (α := α) M)
          (1 : Op (ιB × Option α)))
        (MagicSquareRigidity.naimarkDilatedState α ψ) =
      MagicSquareRigidity.naimarkDilatedState α
        (applyOperatorToState (heteroKron M (1 : Op ιB)) ψ) := by
  classical
  ext p
  rw [MagicSquareRigidity.applyOperatorToState_naimarkDilatedState,
    MagicSquareRigidity.naimarkDilatedState_apply]
  obtain ⟨⟨i, oa⟩, ⟨j, ob⟩⟩ := p
  by_cases hoa : oa = none
  · by_cases hob : ob = none
    · subst hoa
      subst hob
      simp [heteroKron, applyOperatorToState, Matrix.mulVec, dotProduct,
        Fintype.sum_prod_type, Matrix.one_apply]
    · simp_all [heteroKron]
  · simp_all [heteroKron]

/-- The state-dependent norm of an operator inflated on the first factor,
measured on the dilated state, is the norm of the original operator on the
original state. Formalization-only support for `thm:ms-rigidity`, blueprint
`ch13_qpbt_test.tex:266-288`. -/
theorem norm_heteroKron_naimarkInflation_one :
    ‖applyOperatorToState
        (heteroKron (MagicSquareRigidity.naimarkInflation (α := α) M)
          (1 : Op (ιB × Option α)))
        (MagicSquareRigidity.naimarkDilatedState α ψ)‖ =
      ‖applyOperatorToState (heteroKron M (1 : Op ιB)) ψ‖ := by
  rw [applyOperatorToState_heteroKron_naimarkInflation_one,
    MagicSquareRigidity.naimarkDilatedState_norm]

end

/-- Alice's Magic Square variable reflections are the placed observables of her
totalized variable measurements on the dilated strategy. Formalization-only
support for `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:266-288`. -/
theorem msVarObsA_eq (S : Strategy msGame) (j : Fin 9) :
    MagicSquareRigidity.msVarObsA S j =
      heteroKron (MagicSquareRigidity.dilatedObsA S (.var j))
        (1 : Op (S.ιB × Option MsAnswer)) := by
  rw [MagicSquareRigidity.msVarObsA,
    MagicSquareRigidity.signObs_eq_obsOf_postprocess]
  rfl

section

variable (S : Strategy msGame) (ε : ℝ) (hε : 0 ≤ ε)
    (hwin : 1 - ε ≤ S.value)
include S ε hε hwin

/-- Alice's Magic Square variable observables approximately anticommute on the
strategy state. This auxiliary estimate is proved on the projective dilation
and read back through the ground slice on the first tensor factor. Paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:342-356`,
blueprint `lem:qld-ms-anticommutator-original-state`. -/
theorem msVarObsA_anticommutator_le :
    ‖applyOperatorToState
        (heteroKron
          (obsOf ((S.A (.var 0)).postprocess msBitOrZero) *
              obsOf ((S.A (.var 4)).postprocess msBitOrZero) +
            obsOf ((S.A (.var 4)).postprocess msBitOrZero) *
              obsOf ((S.A (.var 0)).postprocess msBitOrZero))
          (1 : Op S.ιB))
        S.ψ‖ ^ 2 ≤ 1183680 * ε := by
  suffices h : ‖applyOperatorToState _ S.ψ‖ ≤ 648 * Real.sqrt ε by
    calc
      _ ≤ (648 * Real.sqrt ε) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      _ ≤ _ := by rw [mul_pow, Real.sq_sqrt hε]; nlinarith
  rw [← norm_heteroKron_naimarkInflation_one MsAnswer, ← naimarkInflation_add,
    ← MagicSquareRigidity.naimarkInflation_mul, ← MagicSquareRigidity.naimarkInflation_mul,
    MagicSquareRigidity.naimarkInflation_obs_A, MagicSquareRigidity.naimarkInflation_obs_A]
  let G := MagicSquareRigidity.groundProjection S.ιA MsAnswer
  let L (M : Op (S.ιA × Option MsAnswer)) := heteroKron M (1 : Op (S.ιB × Option MsAnswer))
  let X := MagicSquareRigidity.dilatedObsA S (.var 0)
  let Z := MagicSquareRigidity.dilatedObsA S (.var 4)
  have hproj := MagicSquareRigidity.isProj_groundProjection S.ιA MsAnswer
  have hL (A B : Op (S.ιA × Option MsAnswer)) : L A * L B = L (A * B) := by
    simp [L, heteroKron_mul]
  have hLeak (A : Op (S.ιA × Option MsAnswer)) : (1 - L G) * L A = L ((1 - G) * A) := by
    simp only [L, sub_mul, one_mul, heteroKron_sub_left, heteroKron_mul, mul_one]
  have hcompress := MagicSquareRigidity.norm_compressed_anticommutator_le
    (MagicSquareRigidity.naimarkDilatedState MsAnswer S.ψ) (L G) (L X) (L Z)
    (by rw [hL]; exact congrArg L hproj.isIdempotentElem.eq)
    (MagicSquareRigidity.applyOperatorToState_leftTensor_groundProjection MsAnswer S.ψ)
    (MagicSquareRigidity.conjTranspose_mul_le_one_leftTensor
      (MagicSquareRigidity.conjTranspose_mul_le_one_of_isProj hproj))
    (MagicSquareRigidity.conjTranspose_mul_le_one_leftTensor
      (MagicSquareRigidity.conjTranspose_mul_le_one_dilatedObsA S (.var 0)))
    (MagicSquareRigidity.conjTranspose_mul_le_one_leftTensor
      (MagicSquareRigidity.conjTranspose_mul_le_one_dilatedObsA S (.var 4)))
  simp only [hL, hLeak] at hcompress
  rw [heteroKron_add_left]
  refine hcompress.trans ?_
  have hanti := MagicSquareRigidity.msVarObsA_anticommute S ε hwin
  simp only [MagicSquareRigidity.NormCloseOn, msVarObsA_eq, sub_neg_eq_add] at hanti
  have h0 := MagicSquareRigidity.norm_leak_obs_le_sqrt S ε hwin 0 0
  have h4 := MagicSquareRigidity.norm_leak_obs_le_sqrt S ε hwin 1 1
  change ‖applyOperatorToState (L ((1 - G) * X)) _‖ ≤ _ at h0
  change ‖applyOperatorToState (L ((1 - G) * Z)) _‖ ≤ _ at h4
  change ‖applyOperatorToState (L X * L Z + L Z * L X)
    (MagicSquareRigidity.naimarkDilatedState MsAnswer S.ψ)‖ ≤ _ at hanti
  simp only [hL] at hanti
  linarith

/-- Bob's original observables satisfy the same bound after player exchange. -/
theorem msVarObs_anticommutator_le :
    ‖applyOperatorToState
        (heteroKron (1 : Op S.ιA)
          (obsOf ((S.B (.var 0)).postprocess msBitOrZero) *
              obsOf ((S.B (.var 4)).postprocess msBitOrZero) +
            obsOf ((S.B (.var 4)).postprocess msBitOrZero) *
              obsOf ((S.B (.var 0)).postprocess msBitOrZero))) S.ψ‖ ^ 2 ≤ 1183680 * ε := by
  have hv : (msGameSymm.swapStrategy S).value = S.value := msGameSymm.swapStrategy_value S
  have h := msVarObsA_anticommutator_le (msGameSymm.swapStrategy S) ε hε (hv.symm ▸ hwin)
  have hn (M : Op S.ιB) :
      ‖applyOperatorToState (heteroKron M (1 : Op S.ιA))
        (reindexState (Equiv.prodComm _ _) S.ψ)‖ =
      ‖applyOperatorToState (heteroKron (1 : Op S.ιA) M) S.ψ‖ := by
    rw [norm_applyOperatorToState_reindexState, reindexOp_prodComm_heteroKron]
  rw [← hn]
  exact h

end

/-! ## Reflections and the product transfer -/

section

variable {ιA ιB : Type*} [DecidableEq ιA]
    [DecidableEq ιB] [Fintype ιA] [Fintype ιB]
include ιA ιB

/-- Placing an isometry on the first factor gives an isometry.
Formalization-only support for `fact:add-a-proj`, blueprint
`ch12_qpbt_games.tex:305-321`. -/
theorem heteroKron_left_isometry (A : Op ιA)
    (hA : Aᴴ * A = 1) :
    (heteroKron A (1 : Op ιB))ᴴ * heteroKron A 1 = 1 := by
  rw [heteroKron_conjTranspose, heteroKron_mul, hA, Matrix.conjTranspose_one,
    one_mul, heteroKron_one_one]

/-- Placing an isometry on the second factor gives an isometry.
Formalization-only support for `fact:add-a-proj`, blueprint
`ch12_qpbt_games.tex:305-321`. -/
theorem heteroKron_right_isometry (B : Op ιB)
    (hB : Bᴴ * B = 1) :
    (heteroKron (1 : Op ιA) B)ᴴ * heteroKron 1 B = 1 := by
  rw [heteroKron_conjTranspose, heteroKron_mul, hB, Matrix.conjTranspose_one,
    one_mul, heteroKron_one_one]

end

/-- The observable of a binary projective measurement is a reflection.
Formalization-only support for `lem:povm-to-obs`, blueprint
`ch14_qpbt_observables.tex:365-382`. -/
theorem obsOf_conjTranspose_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement (ZMod 2) ι)
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
  rw [sub_zero, zero_sub, sub_neg_eq_add]
  exact hsum

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
  rw [hsplit, MagicSquareRigidity.applyOperatorToState_add_op]
  refine le_trans (norm_add_le _ _) ?_
  rw [MagicSquareRigidity.norm_applyOperatorToState_isometry_mul hA,
    MagicSquareRigidity.norm_applyOperatorToState_isometry_mul hD]

/-! ## From the Magic Square variables to the point observables -/

section

variable {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)
    (r : PauliScalar P) (u : PauliPoint P)
include P ε S side W r u

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
  exact S.pointObs_sq_eq_one side W r u

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
    DistanceCalculus.leftPlacedMeasurement (ιB := ιR) (M x) with hAdef
  set B : X → MIPStarRE.Quantum.Measurement (ZMod 2) (ιL × ιR) := fun x =>
    DistanceCalculus.rightPlacedMeasurement (ιA := ιL) (N x) with hBdef
  have hfam : measurementDistSq μ
      A B χ ≤ 2 * c :=
    opFamilyDistSq_placed_le_of_consistencyDefect_le μ M N χ h
  have hobs := povm_to_obs_of_measurements μ A B phaseSign norm_phaseSign χ
  have hleft : ∀ x, (∑ b : ZMod 2, phaseSign b • (A x).effect b) =
      heteroKron (obsOf (M x)) (1 : Op ιR) := by
    intro x
    rw [← sum_phaseSign_smul_effect_eq_obsOf, heteroKron_left_sum_smul]
    rfl
  have hright : ∀ x, (∑ b : ZMod 2, phaseSign b • (B x).effect b) =
      heteroKron (1 : Op ιL) (obsOf (N x)) := by
    intro x
    rw [← sum_phaseSign_smul_effect_eq_obsOf, heteroKron_right_sum_smul]
    rfl
  have hrw : opDistSq μ (fun x => heteroKron (obsOf (M x)) (1 : Op ιR))
      (fun x => heteroKron (1 : Op ιL) (obsOf (N x))) χ =
    opDistSq μ (fun x => ∑ b : ZMod 2, phaseSign b • (A x).effect b)
      (fun x => ∑ b : ZMod 2, phaseSign b • (B x).effect b) χ := by
    congr 1 <;> funext x
    · simp_all
    · simp_all
  rw [hrw]
  have hcast : (Fintype.card (ZMod 2) : ℝ) = 2 := by simp
  calc
    _ ≤ (Fintype.card (ZMod 2) : ℝ) * measurementDistSq μ
        A B χ := hobs
    _ ≤ 2 * (2 * c) := by simp_all
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

/-- Every strategy value is at most one. This is an alias of the Games-layer
`MIPStarRE.QPBT.Strategy.value_le_one`, which carries the single proof; the name
is kept here so the existing callers of this layer resolve unchanged.
Formalization-only support for `def:tensor-product-value`, blueprint
`ch12_qpbt_games.tex:71-82`. -/
theorem strategy_value_le_one {G : Game} (S : Strategy G) : S.value ≤ 1 :=
  Strategy.value_le_one S

section

variable {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε)

/-- The Magic Square value defect of a tuple is nonnegative and admissible as
an error parameter for the rigidity input. Formalization-only support for
`eq:qld-implication-ms-anticomm`, paper
`14_analysis_of_the_pauli_basis_test.tex:349-356`. -/
theorem msValueAt_defect_nonneg (ω : PauliTuple P) :
    0 ≤ 1 - S.msValueAt ω ∧
      1 - (1 - S.msValueAt ω) ≤ (S.msStrategyAt ω).value := by
  have hle := strategy_value_le_one (S.msStrategyAt ω)
  have heq : S.msValueAt ω = (S.msStrategyAt ω).value := rfl
  simp_all

/-- The Magic Square variable observables induced by the test strategy at one
tuple approximately anticommute on Bob's factor, with error the tuple's Magic
Square defect. This is Equation `eq:qld-implication-ms-anticomm` before
averaging, paper `14_analysis_of_the_pauli_basis_test.tex:349-356`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem msVarBitObs_anticommutator_le (ω : PauliTuple P) :
    ‖applyOperatorToState
        (heteroKron (1 : Op S.toStrategy.ιA)
          (obsOf (S.msVarBitMeas .bob 0 ω) * obsOf (S.msVarBitMeas .bob 4 ω) +
            obsOf (S.msVarBitMeas .bob 4 ω) * obsOf (S.msVarBitMeas .bob 0 ω)))
        S.toStrategy.ψ‖ ^ 2 ≤ 1183680 * (1 - S.msValueAt ω) := by
  obtain ⟨hnn, hwin⟩ := msValueAt_defect_nonneg S ω
  exact msVarObs_anticommutator_le (S.msStrategyAt ω) (1 - S.msValueAt ω) hnn
    hwin

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
  let L (M : Op ιL) := heteroKron M (1 : Op ιR)
  let R (N : Op ιR) := heteroKron (1 : Op ιL) N
  let n (M : Op (ιL × ιR)) := ‖applyOperatorToState M χ‖
  let a ω := n (L (OX ω) - R (V0 ω))
  let b ω := n (L (OZ ω) - R (V4 ω))
  let c ω := n (R (V0 ω * V4 ω + V4 ω * V0 ω))
  let t ω := n (L (OX ω * OZ ω) + L (OZ ω * OX ω))
  have hpoint ω : t ω ^ 2 ≤ 12 * a ω ^ 2 + 12 * b ω ^ 2 + 3 * c ω ^ 2 := by
    let U := L (OX ω * OZ ω) - R (V4 ω * V0 ω)
    let V := L (OZ ω * OX ω) - R (V0 ω * V4 ω)
    let W := R (V0 ω * V4 ω + V4 ω * V0 ω)
    have hU : n U ≤ b ω + a ω := norm_product_transfer_le _ _ _ _ χ
      (heteroKron_left_isometry _ (hOX ω)) (heteroKron_right_isometry _ (hV4 ω))
    have hV : n V ≤ a ω + b ω := norm_product_transfer_le _ _ _ _ χ
      (heteroKron_left_isometry _ (hOZ ω)) (heteroKron_right_isometry _ (hV0 ω))
    have ht : t ω = n (U + V + W) := by
      refine congrArg n ?_
      change L (OX ω * OZ ω) + L (OZ ω * OX ω) = U + V + W
      dsimp only [U, V, W, R, L]
      rw [heteroKron_add_right]
      abel
    have htri (M N) : n (M + N) ≤ n M + n N := by
      simpa only [n, MagicSquareRigidity.applyOperatorToState_add_op] using
        norm_add_le (applyOperatorToState M χ) (applyOperatorToState N χ)
    have hbound : t ω ≤ 2 * a ω + 2 * b ω + c ω := by
      rw [ht]
      have h := (htri (U + V) W).trans (add_le_add (htri U V) le_rfl)
      change n (U + V + W) ≤ n U + n V + c ω at h
      linarith
    nlinarith only [DistanceCalculus.sq_le_three_sq_of_le (norm_nonneg _) hbound]
  refine (avgOver_mono _ _ _ hpoint).trans ?_
  simp only [avgOver_add, avgOver_const_mul]
  change avgOver _ (fun ω => a ω ^ 2) ≤ cd at h0
  change avgOver _ (fun ω => b ω ^ 2) ≤ cd at h4
  change avgOver _ (fun ω => c ω ^ 2) ≤ cv at hv
  linarith only [h0, h4, hv]

/-- The observable of a binary projective measurement obtained from a strategy
measurement by two postprocessings is a reflection. Formalization-only support
for `eq:qld-implication-ms-anticomm`, blueprint
`lem:qld-win-implications-obs`. -/
theorem msVarBitObs_conjTranspose_mul_self (side : PlayerSide) (j : Fin 9)
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
theorem pointTraceObs_conjTranspose_mul_self (side : PlayerSide) (W : PauliKind)
    (u : PauliPoint P) (r : PauliScalar P) :
    (obsOf (S.pointTraceMeas side W u r))ᴴ *
      obsOf (S.pointTraceMeas side W u r) = 1 := by
  rw [← pointObs_eq_obsOf]
  exact pointObs_conjTranspose_mul_self S side W r u

end

abbrev anticommutingObsConstant : ℝ :=
  96 * (16 * (Fintype.card PauliEdge : ℝ)) +
    3551040 * (16 * (Fintype.card PauliEdge : ℝ))

/-- The point observables approximately anticommute on anticommuting tuples.
This is the anticommuting half of Equation `eq:pts-obs-commutation`, paper
`14_analysis_of_the_pauli_basis_test.tex:342-362`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem point_obs_anticommutator_anticomm_le_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε), 0 ≤ ε →
      avgOver (anticommTupleDist P) (fun ω =>
        ‖applyOperatorToState
          (heteroKron (S.pointProductAt .alice .X ω) (1 : Op S.toStrategy.ιB) +
            heteroKron (S.pointProductAt .alice .Z ω) (1 : Op S.toStrategy.ιB))
          S.toStrategy.ψ‖ ^ 2) ≤
        anticommutingObsConstant * ε := by
  classical
  intro P ε S hε
  simp only [ProjectiveSetting.pointProductAt, ProjectiveSetting.pointObsAt, pointObs_eq_obsOf]
  let M W ω := S.pointTraceAt .alice W ω
  let N W ω := S.msVarBitMeas .bob (selectedMsVar W) ω
  have hd W := obsDist_le_of_consistencyDefect (anticommTupleDist P) (M W) (N W)
    S.toStrategy.ψ (win_ms_cons_explicit P ε S hε W)
  simp only [opDistSq_eq_avgOver] at hd
  let d := 16 * (Fintype.card PauliEdge : ℝ) * ε
  have hv : avgOver (anticommTupleDist P) (fun ω => 1 - S.msValueAt ω) ≤ d := by
    rw [avgOver_sub, avgOver_const_of_isProbability _ (anticommTupleDist_isProbability P)]
    exact le_of_abs_le (win_magic_square_explicit P ε S hε)
  have hms := avgOver_mono (anticommTupleDist P) _ _ (msVarBitObs_anticommutator_le S)
  rw [avgOver_const_mul] at hms
  have h := obs_anticommutator_avg_le
    (fun ω => obsOf (M .X ω)) (fun ω => obsOf (M .Z ω))
    (fun ω => obsOf (N .X ω)) (fun ω => obsOf (N .Z ω)) S.toStrategy.ψ
    (fun ω => pointTraceObs_conjTranspose_mul_self S .alice .X _ _)
    (fun ω => pointTraceObs_conjTranspose_mul_self S .alice .Z _ _)
    (fun ω => msVarBitObs_conjTranspose_mul_self S .bob 0 ω)
    (fun ω => msVarBitObs_conjTranspose_mul_self S .bob 4 ω)
    (hd .X) (hd .Z) (hms.trans (mul_le_mul_of_nonneg_left hv (by norm_num)))
  exact h.trans_eq (by dsimp [d, anticommutingObsConstant]; ring)

end WinImplications

end

end MIPStarRE.QPBT
