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
private def AlicePlaced {ιA ιB : Type} [DecidableEq ιB] (Z : Op (ιA × ιB)) : Prop :=
  ∃ M : Op ιA, Z = heteroKron M 1

/-- Formalization-only: an operator acting on Bob's tensor factor alone. -/
private def BobPlaced {ιA ιB : Type} [DecidableEq ιA] (Z : Op (ιA × ιB)) : Prop :=
  ∃ N : Op ιB, Z = heteroKron 1 N

/-- Formalization-only: operators of the two players commute. -/
private theorem AlicePlaced.comm {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] {Z W : Op (ιA × ιB)} (hZ : AlicePlaced Z)
    (hW : BobPlaced W) : Z * W = W * Z := by
  obtain ⟨M, rfl⟩ := hZ
  obtain ⟨N, rfl⟩ := hW
  apply heteroKron_comm

/-- Formalization-only: products stay on Alice's tensor factor. -/
private theorem AlicePlaced.mul {ιA ιB : Type} [Fintype ιA]
    [Fintype ιB] [DecidableEq ιB] {Z W : Op (ιA × ιB)} (hZ : AlicePlaced Z)
    (hW : AlicePlaced W) : AlicePlaced (Z * W) := by
  obtain ⟨M, rfl⟩ := hZ
  obtain ⟨M', rfl⟩ := hW
  exact ⟨M * M', by simp [heteroKron_mul]⟩

/-- Formalization-only: products stay on Bob's tensor factor. -/
private theorem BobPlaced.mul {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] {Z W : Op (ιA × ιB)} (hZ : BobPlaced Z)
    (hW : BobPlaced W) : BobPlaced (Z * W) := by
  obtain ⟨N, rfl⟩ := hZ
  obtain ⟨N', rfl⟩ := hW
  exact ⟨N * N', by simp [heteroKron_mul]⟩

/-- Formalization-only: operators of the two players commute. -/
private theorem BobPlaced.comm {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] {Z W : Op (ιA × ιB)} (hZ : BobPlaced Z)
    (hW : AlicePlaced W) : Z * W = W * Z := (hW.comm hZ).symm

section

variable (S : Strategy msGame) {ι : Type} [Fintype ι] (i : Fin 6) (j : Fin 9) [DecidableEq ι]
  (k : Fin 3) {c : ℂ} (hstar : star c = c) (hsq : c * c = 1) {U V : Op ι} (hU : Uᴴ * U = 1)

/-- Alice's cell reflection acts on her tensor factor alone. -/
private theorem alicePlaced_msCellObsA :
    AlicePlaced (msCellObsA S i k) := ⟨_, rfl⟩

/-- Bob's variable reflection acts on his tensor factor alone. -/
private theorem bobPlaced_msVarObsB :
    BobPlaced (msVarObsB S j) := ⟨_, rfl⟩

/-! ## Isometry bookkeeping -/

include hU in
/-- Formalization-only: a product of isometric operators is isometric. -/
theorem isometry_mul_isometry (hV : Vᴴ * V = 1) : (U * V)ᴴ * (U * V) = 1 := by
  simp
  calc _ = Vᴴ * (Uᴴ * U) * V := by noncomm_ring
    _ = 1 := by simp_all

include hU hsq hstar in
/-- Formalization-only: a unit scalar multiple of an isometric operator is
isometric. -/
private theorem isometry_smul :
    (c • U)ᴴ * (c • U) = 1 := by
  rw [← Matrix.star_eq_conjTranspose, star_smul, Matrix.star_eq_conjTranspose, hstar, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hU, hsq, one_smul]

end

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
private theorem normCloseOn_step {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB] {ψ : EuclideanSpace ℂ (ιA × ιB)} {δ : ℝ}
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
  have hsXWiso :=
    isometry_smul hsIstar hsIsq (isometry_mul_isometry hXr.isometry hWr.isometry)
  have h2 :=
    NormCloseOn.mul_left_subst hY (by
      have s1 := NormCloseOn.isometry_mul hPr.isometry hRRa
      rw [show P * Ra = Ra * P from hcP] at s1
      exact s1.trans (NormCloseOn.isometry_mul hRar.isometry hPPa)) hYr.isometry hsXWiso (isometry_mul_isometry hRar.isometry hPar.isometry) hcY (by simp [hcXW])
  have h3 :=
    NormCloseOn.isometry_mul hsXWiso (NormCloseOn.mul_left_subst hPX hRRa hPr.isometry hXr.isometry hRar.isometry hcP hcX)
  have e2 : (sI • (X * W)) * (X * R) = sI • (W * R) := by
    simp
    congr 1
    calc _ = X * (W * X) * R := by noncomm_ring
      _ = X * (X * W) * R := by rw [hXW]
      _ = (X * X) * (W * R) := by noncomm_ring
      _ = W * R := by simp [hXr.mul_self_eq_one]
  have hA : NormCloseOn ψ δ (Y * Q) (sJ • (Y * (P * R))) := by
    have h1 :=
      NormCloseOn.isometry_mul hYr.isometry hQ
    rwa [Matrix.mul_smul] at h1
  have hfinal := (hA.trans (NormCloseOn.smul hsJnorm h2)).trans (NormCloseOn.smul hsJnorm h3)
  rw [e2, smul_smul, mul_comm] at hfinal
  exact hfinal.mono (by linarith)

/-! ## Negation and the sign of a constraint -/

/-- Formalization-only: closeness to a negation is symmetric in the two
operators, because `M - (-N) = N - (-M)`.  Used by the solution-group
computations of both logical Pauli pairs. -/
theorem normCloseOn_neg_swap {ι : Type} [Fintype ι] [DecidableEq ι]
    {ψ : EuclideanSpace ℂ ι} {δ : ℝ} {M N : Op ι} (h : NormCloseOn ψ δ M (-N)) :
    NormCloseOn ψ δ N (-M) := by
  change _ ≤ δ
  rw [show N - -M = M - -N by abel]
  exact h

/-! ## The Magic Square instance of one step -/

/-! ## Approximate anticommutation of the two logical Pauli pairs -/

/-! ## The computation on Alice's cell reflections -/

section

variable (S : Strategy msGame) (ε : ℝ) (hwin : 1 - ε ≤ S.value) (I i J : Fin 6)
  (k₀ k k₁ k₂ l l₀ l₁ l₂ : Fin 3)

include hwin in
/-- One of Alice's three cell reflections of a constraint question is close, on
the dilated state, to the signed product of the other two. -/
theorem msCellObsA_single_close
    (hsum : ∀ a, constraintBitOrZero k₀ a + constraintBitOrZero k₁ a +
      constraintBitOrZero k₂ a = constraintBitSum a) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε) (msCellObsA S i k₁)
      (((bitSign (msParity i) : ℝ) : ℂ) •
        (msCellObsA S i k₀ * msCellObsA S i k₂)) := by
  have hZX := msCellObsA_comm S i k₂ k₀
  have e1 : (msCellObsA S i k₂ * msCellObsA S i k₀) *
      (msCellObsA S i k₀ * msCellObsA S i k₁ * msCellObsA S i k₂) =
      msCellObsA S i k₁ := by
    calc _
        = msCellObsA S i k₂ *
            ((msCellObsA S i k₀ * msCellObsA S i k₀) * msCellObsA S i k₁) *
            msCellObsA S i k₂ := by noncomm_ring
      _ = msCellObsA S i k₂ * msCellObsA S i k₁ * msCellObsA S i k₂ := by
          simp [((isBinaryObservable_msCellObsA S i k₀).mul_self_eq_one)]
      _ = msCellObsA S i k₁ * msCellObsA S i k₂ * msCellObsA S i k₂ := by rw [(msCellObsA_comm S i k₂ k₁)]
      _ = _ := by simp [mul_assoc, ((isBinaryObservable_msCellObsA S i k₂).mul_self_eq_one)]
  have h := NormCloseOn.isometry_mul (((isBinaryObservable_msCellObsA S i k₂).mul
      (isBinaryObservable_msCellObsA S i k₀) hZX).isometry) (msCellObsA_prod_close_of S ε hwin i k₀ k₁ k₂ hsum)
  rw [e1, Matrix.mul_smul, mul_one, hZX] at h
  exact h

include hwin in
/-- A product of two of Alice's cell reflections is close, on the dilated state,
to the product of Bob's variable reflections at the same two cells, taken in the
reverse order. -/
theorem msCellObsA_mul_close :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε + 12 * Real.sqrt ε)
      (msCellObsA S I k * msCellObsA S J l)
      (msVarObsB S (msConstraintVars J l) * msVarObsB S (msConstraintVars I k)) := by
  have h1 :=
    NormCloseOn.isometry_mul (isBinaryObservable_msCellObsA S I k).isometry
      (msCellObsA_close_msVarObsB hwin J l)
  rw [msCellObsA_comm_msVarObsB S I k (msConstraintVars J l)] at h1
  exact h1.trans (NormCloseOn.isometry_mul (isBinaryObservable_msVarObsB S _).isometry
    (msCellObsA_close_msVarObsB hwin I k))

include hwin in
/-- Two of Alice's cell reflections attached to a common cell by two different
constraint questions are close on the dilated state. -/
theorem msCellObsA_close_of_same_cell
    (hcell : msConstraintVars I k = msConstraintVars J l) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε + 12 * Real.sqrt ε)
      (msCellObsA S I k) (msCellObsA S J l) := by
  have p1 := msCellObsA_close_msVarObsB hwin I k
  rw [hcell] at p1
  exact p1.trans ((msCellObsA_close_msVarObsB hwin J l).symm)

include hwin in
/-- One step of the solution-group computation for Alice's cell reflections. -/
theorem msCellObsA_step
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
    (isBinaryObservable_msVarObsB S _)
    (isBinaryObservable_msVarObsB S _)
    (((bobPlaced_msVarObsB S (msConstraintVars J l₂)).mul
      (bobPlaced_msVarObsB S _)).comm
      (alicePlaced_msCellObsA S I k₁)).symm
    (((bobPlaced_msVarObsB S (msConstraintVars J l₂)).mul
      (bobPlaced_msVarObsB S _)).comm
      ((alicePlaced_msCellObsA S I k₀).mul (alicePlaced_msCellObsA S I k₂))).symm
    ((bobPlaced_msVarObsB S (msConstraintVars J l₂)).comm
      (alicePlaced_msCellObsA S J l₀)).symm
    ((bobPlaced_msVarObsB S (msConstraintVars J l₂)).comm
      (alicePlaced_msCellObsA S I k₀)).symm
    (msCellObsA_comm S I k₀ k₂) ((by rcases bit_sign_eq_one_or_neg_one (msParity J) with h | h <;> rw [h] <;> norm_num))
    ((by simp)) ((by rcases bit_sign_eq_one_or_neg_one (msParity I) with h | h <;> rw [h] <;> norm_num))
    (msCellObsA_single_close S ε hwin J l₀ l₁ l₂ hJ)
    (msCellObsA_single_close S ε hwin I k₀ k₁ k₂ hI)
    (msCellObsA_close_msVarObsB hwin J l₀)
    (msCellObsA_close_msVarObsB hwin J l₂)
    (msCellObsA_close_of_same_cell S ε hwin J I l₀ k₀ hcell.symm)

end

/-- Replacing both factors of a product of two of Alice's cell reflections by
the reflections that other constraints attach to the same two cells. -/
theorem msCellObsA_mul_close_of_same_cells (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (I J I' J' : Fin 6) (k l k' l' : Fin 3)
    (h1 : msConstraintVars I k = msConstraintVars I' k')
    (h2 : msConstraintVars J l = msConstraintVars J' l') :
    NormCloseOn (msDilatedStrategy S).ψ (6 * (12 * Real.sqrt ε))
      (msCellObsA S I k * msCellObsA S J l)
      (msCellObsA S I' k' * msCellObsA S J' l') := by
  exact ((NormCloseOn.isometry_mul (isBinaryObservable_msCellObsA S I k).isometry
    (msCellObsA_close_of_same_cell S ε hwin J J' l l' h2)).trans (NormCloseOn.mul_left_subst
    (msCellObsA_close_of_same_cell S ε hwin I I' k k' h1)
    (msCellObsA_close_msVarObsB hwin J' l')
    (isBinaryObservable_msCellObsA S I k).isometry
    (isBinaryObservable_msCellObsA S I' k').isometry
    (isBinaryObservable_msVarObsB S (msConstraintVars J' l')).isometry
    (msCellObsA_comm_msVarObsB S I k _)
    (msCellObsA_comm_msVarObsB S I' k' _))).mono (by linarith)

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
theorem msVarObsB_anticommute (S : Strategy msGame) (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    NormCloseOn (msDilatedStrategy S).ψ (624 * Real.sqrt ε)
      (msVarObsB S 0 * msVarObsB S 4) (-(msVarObsB S 4 * msVarObsB S 0)) := by
  have hsign_pos : ∀ i : Fin 6, i ≠ 5 → ((bitSign (msParity i) : ℝ) : ℂ) = 1 := by
    intro i hi
    have hp : msParity i = 0 := by
      unfold msParity
      simp
      omega
    rw [hp]
    rfl
  have hsign_neg : ((bitSign (msParity 5) : ℝ) : ℂ) = -1 := by
    simp [msParity, bitSign, ZMod.val_one]
  have stepA := msCellObsA_step S ε hwin 0 4 1 0 2 0 1 2 (by intro a; simp only [constraintBitSum]; ring) (fun a => rfl) (by decide)
  simp [*] at stepA
  have stepB := msCellObsA_step S ε hwin 5 2 2 0 1 2 1 0 (by intro a; simp only [constraintBitSum]; ring) (by intro a; simp only [constraintBitSum]; ring) (by decide)
  simp [*] at stepB
  have stepC := msCellObsA_step S ε hwin 1 3 0 2 1 1 2 0 (by intro a; simp only [constraintBitSum]; ring) (by intro a; simp only [constraintBitSum]; ring) (by decide)
  simp [*] at stepC
  have hstart := (msCellObsA_mul_close S ε hwin 0 4 0 1).symm
  have hend := msCellObsA_mul_close S ε hwin 4 0 1 0
  have hchain := ((((((hstart.trans stepA).trans (msCellObsA_mul_close_of_same_cells S ε hwin 0 4 5 2 2 2 0 1
    (by decide) (by decide))).trans stepB).trans
    (msCellObsA_mul_close_of_same_cells S ε hwin 5 2 1 3 1 0 2 2
      (by decide) (by decide)).neg).trans stepC.neg).trans (msCellObsA_mul_close_of_same_cells S ε hwin 1 3 4 0 1 0 1 0
      (by decide) (by decide)).neg).trans hend.neg
  exact normCloseOn_neg_swap (hchain.mono (by linarith))

end

end MIPStarRE.QPBT.MagicSquareRigidity
