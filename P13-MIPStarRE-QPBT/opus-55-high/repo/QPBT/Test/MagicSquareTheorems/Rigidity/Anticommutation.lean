module

public import QPBT.Test.MagicSquareTheorems.Rigidity.CellRelations

/-!
# Approximate anticommutation in the Magic Square game

The Magic Square is the smallest linear constraint system whose solution group
forces two of its generators to anticommute.  This file carries out that
computation on the projective dilation of an arbitrary strategy, in the
state-dependent norm and with explicit constants.

The computation proceeds in three identical steps.  Each step takes two
constraints sharing exactly one cell and rewrites a product of two cell
reflections, one from each constraint, as the signed product of the two
reflections at the remaining cells.  Iterating the step around the grid returns
to the pair one started from, in the opposite order and with the sign reversed
by the exceptional parity of the third column; this yields the approximate
anticommutation of the two reflections at the cells labelled by the paper's
first and fifth variables.

The final squared-distance corollaries measure the anticommutation defects of
the dilated strategy on its own state, in the `opDistSq` convention of
`def:povm-distance`, at the scale `624 ^ 2 * sqrt ε`.  These are pre-isometry
estimates.  The post-isometry estimates on the ideal EPR-pair-plus-auxiliary
state in `thm:ms-rigidity` are obtained from them through
`ms_anticommutator_transfer_A` and `ms_anticommutator_transfer_B` in the
swap-isometry packet, issue Dengnifer/MIPStarRE-QPBT-bak#104.

## References

The statement supported here is `thm:ms-rigidity` in
`blueprint/src/chapter/ch13_qpbt_test.tex:224-253`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, arXiv:1709.09267v2, Theorem 6.9; the argument
below is the Magic Square instance of the solution-group computation used there
(their Figure describing the generators of the solution group).  The variable
and constraint indices are zero-based, so the paper's first and fifth variables
are the cells `0` and `4`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## Placement of an operator on one player's tensor factor -/

/-- Formalization-only: an operator acting on Alice's tensor factor alone. -/
def AlicePlaced {ιA ιB : Type} [DecidableEq ιB] (Z : Op (ιA × ιB)) : Prop :=
  ∃ M : Op ιA, Z = heteroKron M 1

/-- Formalization-only: an operator acting on Bob's tensor factor alone. -/
def BobPlaced {ιA ιB : Type} [DecidableEq ιA] (Z : Op (ιA × ιB)) : Prop :=
  ∃ N : Op ιB, Z = heteroKron 1 N

variable {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB]

/-- Formalization-only: operators of the two players commute. -/
theorem AlicePlaced.comm [DecidableEq ιB] {Z W : Op (ιA × ιB)} (hZ : AlicePlaced Z)
    (hW : BobPlaced W) : Z * W = W * Z := by
  obtain ⟨M, rfl⟩ := hZ
  obtain ⟨N, rfl⟩ := hW
  exact heteroKron_comm M N

/-- Formalization-only: products stay on Alice's tensor factor. -/
theorem AlicePlaced.mul {ιA ιB : Type} [Fintype ιA]
    [Fintype ιB] [DecidableEq ιB] {Z W : Op (ιA × ιB)} (hZ : AlicePlaced Z)
    (hW : AlicePlaced W) : AlicePlaced (Z * W) := by
  obtain ⟨M, rfl⟩ := hZ
  obtain ⟨M', rfl⟩ := hW
  exact ⟨M * M', by rw [heteroKron_mul, mul_one]⟩

/-- Formalization-only: products stay on Bob's tensor factor. -/
theorem BobPlaced.mul {Z W : Op (ιA × ιB)} (hZ : BobPlaced Z)
    (hW : BobPlaced W) : BobPlaced (Z * W) := by
  obtain ⟨N, rfl⟩ := hZ
  obtain ⟨N', rfl⟩ := hW
  exact ⟨N * N', by rw [heteroKron_mul, mul_one]⟩

/-- Formalization-only: operators of the two players commute. -/
theorem BobPlaced.comm [DecidableEq ιB] {Z W : Op (ιA × ιB)} (hZ : BobPlaced Z)
    (hW : AlicePlaced W) : Z * W = W * Z := (hW.comm hZ).symm

/-- Alice's cell reflection acts on her tensor factor alone. -/
theorem alicePlaced_msCellObsA (S : Strategy msGame) (i : Fin 6) (k : Fin 3) :
    AlicePlaced (msCellObsA S i k) := ⟨_, rfl⟩

/-- Bob's variable reflection acts on his tensor factor alone. -/
theorem bobPlaced_msVarObsB (S : Strategy msGame) (j : Fin 9) :
    BobPlaced (msVarObsB S j) := ⟨_, rfl⟩

/-- Alice's variable reflection acts on her tensor factor alone. -/
theorem alicePlaced_msVarObsA (S : Strategy msGame) (j : Fin 9) :
    AlicePlaced (msVarObsA S j) := ⟨_, rfl⟩

/-- Bob's cell reflection acts on his tensor factor alone. -/
theorem bobPlaced_msCellObsB (S : Strategy msGame) (i : Fin 6) (k : Fin 3) :
    BobPlaced (msCellObsB S i k) := ⟨_, rfl⟩

/-! ## Isometry bookkeeping -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Formalization-only: a product of isometric operators is isometric. -/
theorem isometry_mul_isometry {U V : Op ι} (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) : (U * V)ᴴ * (U * V) = 1 := by
  rw [Matrix.conjTranspose_mul]
  grind

/-- Formalization-only: a unit scalar multiple of an isometric operator is
isometric. -/
theorem isometry_smul {c : ℂ}
    (hstar : star c = c) (hsq : c * c = 1) {U : Op ι} (hU : Uᴴ * U = 1) :
    (c • U)ᴴ * (c • U) = 1 := by
  simp_all [smul_smul, one_smul]

/-- The complex sign of a binary value is fixed by conjugation. -/
theorem star_bitSign_ofReal (c : ZMod 2) :
    star ((bitSign c : ℝ) : ℂ) = ((bitSign c : ℝ) : ℂ) := by
  simp

/-! ## One step of the solution-group computation -/

/-- One step of the Magic Square solution-group computation.  Here `X`, `Y`, `W`
are three reflections of one player attached to a single constraint, with `X`
and `W` commuting and `Y` close to the signed product `sI • (X * W)` prescribed
by that constraint; the reflections `P`, `Q`, `R` play the same role for a
second constraint with sign `sJ`.  The reflections `Pa` and `Ra` are the
counterparts of `P` and `R` on the other player, and `P` is close to `X` because
the two constraints share the cell that `X` and `P` are attached to.  The
conclusion rewrites the product `Y * Q` as the signed product of the two
remaining reflections.  Formalization-only support for blueprint
`thm:ms-rigidity`. -/
theorem normCloseOn_step [DecidableEq ιB] {ψ : EuclideanSpace ℂ (ιA × ιB)} {δ : ℝ}
    {X Y W P Q R Pa Ra : Op (ιA × ιB)} {sI sJ : ℂ}
    (hXr : IsBinaryObservable X) (hYr : IsBinaryObservable Y) (hWr : IsBinaryObservable W)
    (hPr : IsBinaryObservable P)
    (hPar : IsBinaryObservable Pa) (hRar : IsBinaryObservable Ra)
    (hcY : Y * (Ra * Pa) = (Ra * Pa) * Y)
    (hcXW : (X * W) * (Ra * Pa) = (Ra * Pa) * (X * W))
    (hcP : P * Ra = Ra * P) (hcX : X * Ra = Ra * X)
    (hXW : X * W = W * X)
    (hsJnorm : ‖sJ‖ = 1) (hsIstar : star sI = sI) (hsIsq : sI * sI = 1)
    (hQ : NormCloseOn ψ δ Q (sJ • (P * R)))
    (hY : NormCloseOn ψ δ Y (sI • (X * W)))
    (hPPa : NormCloseOn ψ δ P Pa) (hRRa : NormCloseOn ψ δ R Ra)
    (hPX : NormCloseOn ψ (δ + δ) P X) :
    NormCloseOn ψ (10 * δ) (Y * Q) ((sI * sJ) • (W * R)) := by
  have hPRa : NormCloseOn ψ (δ + δ) (P * R) (Ra * Pa) := by
    have s1 : NormCloseOn ψ δ (P * R) (P * Ra) := NormCloseOn.isometry_mul hPr.isometry hRRa
    rw [show P * Ra = Ra * P from hcP] at s1
    exact s1.trans (NormCloseOn.isometry_mul hRar.isometry hPPa)
  have hRaPa : (Ra * Pa)ᴴ * (Ra * Pa) = 1 :=
    isometry_mul_isometry hRar.isometry hPar.isometry
  have hXWiso : (X * W)ᴴ * (X * W) = 1 := isometry_mul_isometry hXr.isometry hWr.isometry
  have hsXWiso : (sI • (X * W))ᴴ * (sI • (X * W)) = 1 :=
    isometry_smul hsIstar hsIsq hXWiso
  have hcsXW : (sI • (X * W)) * (Ra * Pa) = (Ra * Pa) * (sI • (X * W)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hcXW]
  have h2 : NormCloseOn ψ (δ + δ + δ + (δ + δ)) (Y * (P * R)) ((sI • (X * W)) * (P * R)) :=
    NormCloseOn.mul_left_subst hY hPRa hYr.isometry hsXWiso hRaPa hcY hcsXW
  have hPRXR : NormCloseOn ψ (δ + (δ + δ) + δ) (P * R) (X * R) :=
    NormCloseOn.mul_left_subst hPX hRRa hPr.isometry hXr.isometry hRar.isometry hcP hcX
  have h3 : NormCloseOn ψ (δ + (δ + δ) + δ)
      ((sI • (X * W)) * (P * R)) ((sI • (X * W)) * (X * R)) :=
    NormCloseOn.isometry_mul hsXWiso hPRXR
  have e2 : (sI • (X * W)) * (X * R) = sI • (W * R) := by
    rw [Matrix.smul_mul]
    congr 1
    calc (X * W) * (X * R) = X * (W * X) * R := by noncomm_ring
      _ = X * (X * W) * R := by simp_all
      _ = (X * X) * (W * R) := by noncomm_ring
      _ = W * R := by rw [hXr.mul_self_eq_one, one_mul]
  have hA : NormCloseOn ψ δ (Y * Q) (sJ • (Y * (P * R))) := by
    have h1 : NormCloseOn ψ δ (Y * Q) (Y * (sJ • (P * R))) :=
      NormCloseOn.isometry_mul hYr.isometry hQ
    rwa [Matrix.mul_smul] at h1
  have hB := NormCloseOn.smul hsJnorm h2
  have hC := NormCloseOn.smul hsJnorm h3
  have e3 : sJ • ((sI • (X * W)) * (X * R)) = (sI * sJ) • (W * R) := by
    rw [e2, smul_smul, mul_comm]
  have hfinal := (hA.trans hB).trans hC
  grind

/-! ## Negation and the sign of a constraint -/

/-- Formalization-only: closeness to a negation is symmetric in the two
operators, because `M - (-N) = N - (-M)`.  Used by the solution-group
computations of both logical Pauli pairs. -/
theorem normCloseOn_neg_swap {ψ : EuclideanSpace ℂ ι} {δ : ℝ} {M N : Op ι} (h : NormCloseOn ψ δ M (-N)) :
    NormCloseOn ψ δ N (-M) := by
  change ‖applyOperatorToState (N - -M) ψ‖ ≤ δ
  rw [show N - -M = M - -N by abel]
  exact h

/-! ## The Magic Square instance of one step -/

variable (S : Strategy msGame) (ε : ℝ)

/-- One step of the solution-group computation for Bob's cell reflections: for
two constraints sharing the cell at positions `k₀` and `l₀`, the product of the
reflections at the positions `k₁` and `l₁` is close to the signed product of the
reflections at the two remaining positions. -/
theorem msCellObsB_step (hwin : 1 - ε ≤ S.value)
    (I J : Fin 6) (k₀ k₁ k₂ l₀ l₁ l₂ : Fin 3)
    (hI : ∀ a, constraintBitOrZero k₀ a + constraintBitOrZero k₁ a +
      constraintBitOrZero k₂ a = constraintBitSum a)
    (hJ : ∀ a, constraintBitOrZero l₀ a + constraintBitOrZero l₁ a +
      constraintBitOrZero l₂ a = constraintBitSum a)
    (hcell : msConstraintVars I k₀ = msConstraintVars J l₀) :
    NormCloseOn (msDilatedStrategy S).ψ (10 * (12 * Real.sqrt ε))
      (msCellObsB S I k₁ * msCellObsB S J l₁)
      ((((bitSign (msParity I) : ℝ) : ℂ) * ((bitSign (msParity J) : ℝ) : ℂ)) •
        (msCellObsB S I k₂ * msCellObsB S J l₂)) :=
  normCloseOn_step (isBinaryObservable_msCellObsB S I k₀) (isBinaryObservable_msCellObsB S I k₁)
    (isBinaryObservable_msCellObsB S I k₂) (isBinaryObservable_msCellObsB S J l₀)
    (isBinaryObservable_msVarObsA S (msConstraintVars J l₀))
    (isBinaryObservable_msVarObsA S (msConstraintVars J l₂))
    (((alicePlaced_msVarObsA S (msConstraintVars J l₂)).mul
      (alicePlaced_msVarObsA S (msConstraintVars J l₀))).comm
      (bobPlaced_msCellObsB S I k₁)).symm
    (((alicePlaced_msVarObsA S (msConstraintVars J l₂)).mul
      (alicePlaced_msVarObsA S (msConstraintVars J l₀))).comm
      ((bobPlaced_msCellObsB S I k₀).mul (bobPlaced_msCellObsB S I k₂))).symm
    ((alicePlaced_msVarObsA S (msConstraintVars J l₂)).comm
      (bobPlaced_msCellObsB S J l₀)).symm
    ((alicePlaced_msVarObsA S (msConstraintVars J l₂)).comm
      (bobPlaced_msCellObsB S I k₀)).symm
    (msCellObsB_comm S I k₀ k₂) (norm_bitSign_ofReal (msParity J))
    (star_bitSign_ofReal (msParity I)) (bitSign_ofReal_mul_self (msParity I))
    (msCellObsB_single_close S ε hwin J l₀ l₁ l₂ hJ)
    (msCellObsB_single_close S ε hwin I k₀ k₁ k₂ hI)
    (msVarObsA_close_msCellObsB S ε hwin J l₀).symm
    (msVarObsA_close_msCellObsB S ε hwin J l₂).symm
    (msCellObsB_close_of_same_cell S ε hwin J I l₀ k₀ hcell.symm)

/-- Replacing both factors of a product of two of Bob's cell reflections by the
reflections that other constraints attach to the same two cells. -/
theorem msCellObsB_mul_close_of_same_cells (hwin : 1 - ε ≤ S.value) (I J I' J' : Fin 6) (k l k' l' : Fin 3)
    (h1 : msConstraintVars I k = msConstraintVars I' k')
    (h2 : msConstraintVars J l = msConstraintVars J' l') :
    NormCloseOn (msDilatedStrategy S).ψ (6 * (12 * Real.sqrt ε))
      (msCellObsB S I k * msCellObsB S J l)
      (msCellObsB S I' k' * msCellObsB S J' l') := by
  have hright := NormCloseOn.isometry_mul (isBinaryObservable_msCellObsB S I k).isometry
    (msCellObsB_close_of_same_cell S ε hwin J J' l l' h2)
  have hleft := NormCloseOn.mul_left_subst
    (msCellObsB_close_of_same_cell S ε hwin I I' k k' h1)
    (msVarObsA_close_msCellObsB S ε hwin J' l').symm
    (isBinaryObservable_msCellObsB S I k).isometry
    (isBinaryObservable_msCellObsB S I' k').isometry
    (isBinaryObservable_msVarObsA S (msConstraintVars J' l')).isometry
    ((alicePlaced_msVarObsA S (msConstraintVars J' l')).comm
      (bobPlaced_msCellObsB S I k)).symm
    ((alicePlaced_msVarObsA S (msConstraintVars J' l')).comm
      (bobPlaced_msCellObsB S I' k')).symm
  exact (hright.trans hleft).mono (by linarith)

/-! ## Approximate anticommutation of the two logical Pauli pairs -/

/-- The parity signs met along the solution-group computation. -/
theorem ms_step_signs :
    ((bitSign (msParity 0) : ℝ) : ℂ) * ((bitSign (msParity 4) : ℝ) : ℂ) = 1 ∧
      ((bitSign (msParity 5) : ℝ) : ℂ) * ((bitSign (msParity 2) : ℝ) : ℂ) = -1 ∧
      ((bitSign (msParity 1) : ℝ) : ℂ) * ((bitSign (msParity 3) : ℝ) : ℂ) = 1 := by
  norm_num [msParity, bitSign, ZMod.val_one]

/-- The two reflections that Alice attaches to the cells of the paper's first
and fifth variables approximately anticommute on the dilated state, in the
unsquared state-dependent norm and at the scale `624 * sqrt ε`.  For comparison,
the source states the corresponding post-isometry relation for the squared
distance: the last display of
blueprint `thm:ms-rigidity`, paper
`08_classical_and_quantum_low_degree_tests.tex:640-646`, reads
`⟨ψ|(M - N)ᴴ (M - N)|ψ⟩ ≤ O(sqrt ε)`.  The squared-distance form on the
dilated state is `msVarObsA_anticommute_dilated_opDistSq` below, obtained from
this bound through `NormCloseOn.opDistSq_le`. -/
theorem msVarObsA_anticommute (hwin : 1 - ε ≤ S.value) :
    NormCloseOn (msDilatedStrategy S).ψ (624 * Real.sqrt ε)
      (msVarObsA S 0 * msVarObsA S 4) (-(msVarObsA S 4 * msVarObsA S 0)) := by
  obtain ⟨s1, s2, s3⟩ := ms_step_signs
  have stepA := msCellObsB_step S ε hwin 0 4 1 0 2 0 1 2 (by decide) (by decide) (by decide)
  rw [s1, one_smul] at stepA
  have stepB := msCellObsB_step S ε hwin 5 2 2 0 1 2 1 0 (by decide) (by decide) (by decide)
  rw [s2, neg_one_smul] at stepB
  have stepC := msCellObsB_step S ε hwin 1 3 0 2 1 1 2 0 (by decide) (by decide) (by decide)
  rw [s3, one_smul] at stepC
  -- the three changes of representative
  have linkA := msCellObsB_mul_close_of_same_cells S ε hwin 0 4 5 2 2 2 0 1
    (by decide) (by decide)
  have linkB := msCellObsB_mul_close_of_same_cells S ε hwin 5 2 1 3 1 0 2 2
    (by decide) (by decide)
  have linkC := msCellObsB_mul_close_of_same_cells S ε hwin 1 3 4 0 1 0 1 0
    (by decide) (by decide)
  -- passage between Alice's variable reflections and Bob's cell reflections
  have hstart := (msCellObsB_mul_close S ε hwin 0 4 0 1).symm
  have hend := msCellObsB_mul_close S ε hwin 4 0 1 0
  rw [show msConstraintVars 4 1 = 4 from by decide,
    show msConstraintVars 0 0 = 0 from by decide] at hstart hend
  have hchain := ((((((hstart.trans stepA).trans linkA).trans stepB).trans
    linkB.neg).trans stepC.neg).trans linkC.neg).trans hend.neg
  grind [normCloseOn_neg_swap]

/-! ## The computation on Alice's cell reflections -/

/-- One of Alice's three cell reflections of a constraint question is close, on
the dilated state, to the signed product of the other two. -/
theorem msCellObsA_single_close (hwin : 1 - ε ≤ S.value)
    (i : Fin 6) (k₀ k₁ k₂ : Fin 3)
    (hsum : ∀ a, constraintBitOrZero k₀ a + constraintBitOrZero k₁ a +
      constraintBitOrZero k₂ a = constraintBitSum a) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε) (msCellObsA S i k₁)
      (((bitSign (msParity i) : ℝ) : ℂ) •
        (msCellObsA S i k₀ * msCellObsA S i k₂)) :=
  NormCloseOn.of_prod_close (isBinaryObservable_msCellObsA S i k₀)
    (isBinaryObservable_msCellObsA S i k₂) (msCellObsA_comm S i k₂ k₁)
    (msCellObsA_comm S i k₂ k₀) (msCellObsA_prod_close_of S ε hwin i k₀ k₁ k₂ hsum)

/-- A product of two of Alice's cell reflections is close, on the dilated state,
to the product of Bob's variable reflections at the same two cells, taken in the
reverse order. -/
theorem msCellObsA_mul_close (hwin : 1 - ε ≤ S.value)
    (I J : Fin 6) (k l : Fin 3) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε + 12 * Real.sqrt ε)
      (msCellObsA S I k * msCellObsA S J l)
      (msVarObsB S (msConstraintVars J l) * msVarObsB S (msConstraintVars I k)) := by
  have h1 := NormCloseOn.isometry_mul (isBinaryObservable_msCellObsA S I k).isometry
    (msCellObsA_close_msVarObsB S ε hwin J l)
  rw [msCellObsA_comm_msVarObsB S I k (msConstraintVars J l)] at h1
  exact h1.trans (NormCloseOn.isometry_mul (isBinaryObservable_msVarObsB S _).isometry
    (msCellObsA_close_msVarObsB S ε hwin I k))

/-- Two of Alice's cell reflections attached to a common cell by two different
constraint questions are close on the dilated state. -/
theorem msCellObsA_close_of_same_cell (hwin : 1 - ε ≤ S.value) (I J : Fin 6) (k l : Fin 3)
    (hcell : msConstraintVars I k = msConstraintVars J l) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε + 12 * Real.sqrt ε)
      (msCellObsA S I k) (msCellObsA S J l) :=
  (hcell ▸ msCellObsA_close_msVarObsB S ε hwin I k).trans
    (msCellObsA_close_msVarObsB S ε hwin J l).symm

/-- One step of the solution-group computation for Alice's cell reflections. -/
theorem msCellObsA_step (hwin : 1 - ε ≤ S.value)
    (I J : Fin 6) (k₀ k₁ k₂ l₀ l₁ l₂ : Fin 3)
    (hI : ∀ a, constraintBitOrZero k₀ a + constraintBitOrZero k₁ a +
      constraintBitOrZero k₂ a = constraintBitSum a)
    (hJ : ∀ a, constraintBitOrZero l₀ a + constraintBitOrZero l₁ a +
      constraintBitOrZero l₂ a = constraintBitSum a)
    (hcell : msConstraintVars I k₀ = msConstraintVars J l₀) :
    NormCloseOn (msDilatedStrategy S).ψ (10 * (12 * Real.sqrt ε))
      (msCellObsA S I k₁ * msCellObsA S J l₁)
      ((((bitSign (msParity I) : ℝ) : ℂ) * ((bitSign (msParity J) : ℝ) : ℂ)) •
        (msCellObsA S I k₂ * msCellObsA S J l₂)) :=
  normCloseOn_step (isBinaryObservable_msCellObsA S I k₀) (isBinaryObservable_msCellObsA S I k₁)
    (isBinaryObservable_msCellObsA S I k₂) (isBinaryObservable_msCellObsA S J l₀)
    (isBinaryObservable_msVarObsB S (msConstraintVars J l₀))
    (isBinaryObservable_msVarObsB S (msConstraintVars J l₂))
    (((bobPlaced_msVarObsB S (msConstraintVars J l₂)).mul
      (bobPlaced_msVarObsB S (msConstraintVars J l₀))).comm
      (alicePlaced_msCellObsA S I k₁)).symm
    (((bobPlaced_msVarObsB S (msConstraintVars J l₂)).mul
      (bobPlaced_msVarObsB S (msConstraintVars J l₀))).comm
      ((alicePlaced_msCellObsA S I k₀).mul (alicePlaced_msCellObsA S I k₂))).symm
    ((bobPlaced_msVarObsB S (msConstraintVars J l₂)).comm
      (alicePlaced_msCellObsA S J l₀)).symm
    ((bobPlaced_msVarObsB S (msConstraintVars J l₂)).comm
      (alicePlaced_msCellObsA S I k₀)).symm
    (msCellObsA_comm S I k₀ k₂) (norm_bitSign_ofReal (msParity J))
    (star_bitSign_ofReal (msParity I)) (bitSign_ofReal_mul_self (msParity I))
    (msCellObsA_single_close S ε hwin J l₀ l₁ l₂ hJ)
    (msCellObsA_single_close S ε hwin I k₀ k₁ k₂ hI)
    (msCellObsA_close_msVarObsB S ε hwin J l₀)
    (msCellObsA_close_msVarObsB S ε hwin J l₂)
    (msCellObsA_close_of_same_cell S ε hwin J I l₀ k₀ hcell.symm)

/-- Replacing both factors of a product of two of Alice's cell reflections by
the reflections that other constraints attach to the same two cells. -/
theorem msCellObsA_mul_close_of_same_cells (hwin : 1 - ε ≤ S.value) (I J I' J' : Fin 6) (k l k' l' : Fin 3)
    (h1 : msConstraintVars I k = msConstraintVars I' k')
    (h2 : msConstraintVars J l = msConstraintVars J' l') :
    NormCloseOn (msDilatedStrategy S).ψ (6 * (12 * Real.sqrt ε))
      (msCellObsA S I k * msCellObsA S J l)
      (msCellObsA S I' k' * msCellObsA S J' l') := by
  have hright := NormCloseOn.isometry_mul (isBinaryObservable_msCellObsA S I k).isometry
    (msCellObsA_close_of_same_cell S ε hwin J J' l l' h2)
  have hleft := NormCloseOn.mul_left_subst
    (msCellObsA_close_of_same_cell S ε hwin I I' k k' h1)
    (msCellObsA_close_msVarObsB S ε hwin J' l')
    (isBinaryObservable_msCellObsA S I k).isometry
    (isBinaryObservable_msCellObsA S I' k').isometry
    (isBinaryObservable_msVarObsB S (msConstraintVars J' l')).isometry
    (msCellObsA_comm_msVarObsB S I k (msConstraintVars J' l'))
    (msCellObsA_comm_msVarObsB S I' k' (msConstraintVars J' l'))
  exact (hright.trans hleft).mono (by linarith)

/-- The two reflections that Bob attaches to the cells of the paper's first and
fifth variables approximately anticommute on the dilated state, in the unsquared
state-dependent norm and at the scale `624 * sqrt ε`.  For comparison, the
source states the corresponding post-isometry relation in the second half of
the last conclusion of `thm:ms-rigidity` for the squared distance: blueprint
`ch13_qpbt_test.tex:244-249`, paper
`08_classical_and_quantum_low_degree_tests.tex:640-646`, reads
`⟨ψ|(M - N)ᴴ (M - N)|ψ⟩ ≤ O(sqrt ε)`.  The squared-distance form on the
dilated state is `msVarObsB_anticommute_dilated_opDistSq` below, obtained from
this bound through `NormCloseOn.opDistSq_le`. -/
theorem msVarObsB_anticommute (hwin : 1 - ε ≤ S.value) :
    NormCloseOn (msDilatedStrategy S).ψ (624 * Real.sqrt ε)
      (msVarObsB S 0 * msVarObsB S 4) (-(msVarObsB S 4 * msVarObsB S 0)) := by
  obtain ⟨s1, s2, s3⟩ := ms_step_signs
  have stepA := msCellObsA_step S ε hwin 0 4 1 0 2 0 1 2 (by decide) (by decide) (by decide)
  rw [s1, one_smul] at stepA
  have stepB := msCellObsA_step S ε hwin 5 2 2 0 1 2 1 0 (by decide) (by decide) (by decide)
  rw [s2, neg_one_smul] at stepB
  have stepC := msCellObsA_step S ε hwin 1 3 0 2 1 1 2 0 (by decide) (by decide) (by decide)
  rw [s3, one_smul] at stepC
  have linkA := msCellObsA_mul_close_of_same_cells S ε hwin 0 4 5 2 2 2 0 1
    (by decide) (by decide)
  have linkB := msCellObsA_mul_close_of_same_cells S ε hwin 5 2 1 3 1 0 2 2
    (by decide) (by decide)
  have linkC := msCellObsA_mul_close_of_same_cells S ε hwin 1 3 4 0 1 0 1 0
    (by decide) (by decide)
  have hstart := (msCellObsA_mul_close S ε hwin 0 4 0 1).symm
  have hend := msCellObsA_mul_close S ε hwin 4 0 1 0
  rw [show msConstraintVars 4 1 = 4 from by decide,
    show msConstraintVars 0 0 = 0 from by decide] at hstart hend
  have hchain := ((((((hstart.trans stepA).trans linkA).trans stepB).trans
    linkB.neg).trans stepC.neg).trans linkC.neg).trans hend.neg
  grind [normCloseOn_neg_swap]

end

end MIPStarRE.QPBT.MagicSquareRigidity
