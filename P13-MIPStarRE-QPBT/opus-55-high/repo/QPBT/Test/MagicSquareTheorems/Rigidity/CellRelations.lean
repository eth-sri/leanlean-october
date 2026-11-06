module

public import QPBT.Test.MagicSquareTheorems.Rigidity.Reflections

/-!
# The Magic Square cell relations on the dilated strategy

Every question of the projectively dilated Magic Square strategy carries a
complete projective measurement, so each binary relabelling of its answers
produces a reflection.  Three reflections are attached to a constraint question,
one for each cell of the row or column, and one reflection is attached to each
variable question; the three reflections of a constraint commute exactly and
their product, in any order, is the reflection of the sum of the three reported
bits.  Reflections of the two players commute exactly.

The value-to-parity relations are converted here into operator estimates on the
dilated state, with explicit constants: the six row and column products are
close to the sign prescribed by the corresponding linear equation, and the two
reflections that the two players attach to a common cell are close to each
other.  The two logical Pauli pairs are the reflections at the cells labelled by
the paper's first and fifth variables.

## References

The statement supported here is `thm:ms-rigidity` in
`blueprint/src/chapter/ch13_qpbt_test.tex:224-253`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, arXiv:1709.09267v2, Theorem 6.9.  The variable and
constraint indices are zero-based, so the paper's first and fifth variables are
the cells `0` and `4`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## Deviation of a sign observable from a comparison observable -/

/-- The sign of a binary value is `1` or `-1`. -/
theorem bit_sign_eq_one_or_neg_one (b : ZMod 2) : bitSign b = 1 ∨ bitSign b = -1 := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) b with h | h <;> rw [h]
  · simp [bitSign]
  simp [bitSign, ZMod.val_one]

/-- The sign is injective on binary values. -/
theorem bit_sign_injective : Function.Injective bitSign := by
  intro b c hbc
  by_contra hne
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) b with hb | hb <;>
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) c with hc | hc
  · simp_all
  · rw [hb, hc] at hbc
    norm_num [bitSign, ZMod.val_one] at hbc
  · rw [hb, hc] at hbc
    norm_num [bitSign, ZMod.val_one] at hbc
  simp_all

section SignDefect

variable {G : Game}

variable (T : Strategy G) (x : G.QuestionA) (y : G.QuestionB)

/-- Two sign observables of the two players, placed on the composite space,
differ in the state-dependent norm by at most twice the square root of the Born
mass of the answer pairs on which the two labels disagree.  This is the estimate
that turns every mass of the value-to-parity layer into an operator relation of
`thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:224-253`. -/
theorem norm_alice_sub_bob_signObs_sq_le (hA : MIPStarRE.QPBT.Measurement.IsProjective (T.A x))
    (hB : MIPStarRE.QPBT.Measurement.IsProjective (T.B y))
    (f : G.AnswerA → ZMod 2) (g : G.AnswerB → ZMod 2) :
    ‖applyOperatorToState (heteroKron (signObs (T.A x) f) 1 -
        heteroKron 1 (signObs (T.B y) g)) T.ψ‖ ^ 2 ≤
      4 * outcomeEventWeight T x y (fun a b => f a ≠ g b) := by
  have hAone : (1 : Op T.ιA) = ∑ a, (1 : ℂ) • (T.A x).effect a := by
    simpa using smul_one_eq_sum_smul_effect (T.A x) (1 : ℂ)
  have hBone : (1 : Op T.ιB) = ∑ b, (1 : ℂ) • (T.B y).effect b := by
    simpa using smul_one_eq_sum_smul_effect (T.B y) (1 : ℂ)
  have hexpand : heteroKron (signObs (T.A x) f) 1 - heteroKron 1 (signObs (T.B y) g) =
      ∑ a, ∑ b, ((bitSign (f a) - bitSign (g b) : ℝ) : ℂ) •
        heteroKron ((T.A x).effect a) ((T.B y).effect b) := by
    rw [signObs, signObs]
    nth_rewrite 1 [hBone]
    nth_rewrite 1 [hAone]
    rw [joint_expand, joint_expand, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← sub_smul]
    congr 1
    push_cast
    ring
  rw [hexpand]
  refine norm_apply_joint_defect_sq_le T x y hA hB
    (fun a b => bitSign (f a) - bitSign (g b)) (fun a b => f a ≠ g b) ?_ ?_
  · intro a b
    rcases bit_sign_eq_one_or_neg_one (f a) with h1 | h1 <;>
      rcases bit_sign_eq_one_or_neg_one (g b) with h2 | h2 <;>
        simp only [h1, h2] <;> norm_num
  simp_all

/-- Alice's sign observable deviates from a constant sign by at most twice the
square root of the mass of the answers carrying the other label. -/
theorem norm_alice_signObs_sub_const_sq_le (hA : MIPStarRE.QPBT.Measurement.IsProjective (T.A x))
    (hB : MIPStarRE.QPBT.Measurement.IsProjective (T.B y))
    (f : G.AnswerA → ZMod 2) (c : ZMod 2) :
    ‖applyOperatorToState (heteroKron (signObs (T.A x) f) 1 -
        ((bitSign c : ℝ) : ℂ) • (1 : Op (T.ιA × T.ιB))) T.ψ‖ ^ 2 ≤
      4 * aliceEventWeight T x (fun a => f a ≠ c) := by
  have hconst : heteroKron (1 : Op T.ιA) (signObs (T.B y) (fun _ => c)) =
      ((bitSign c : ℝ) : ℂ) • (1 : Op (T.ιA × T.ιB)) := by
    rw [signObs, ← smul_one_eq_sum_smul_effect (T.B y) (((bitSign c : ℝ) : ℂ)),
      heteroKron_smul_right, heteroKron_one_one]
  grind [norm_alice_sub_bob_signObs_sq_le, le_trans, le_of_eq, outcome_event_weight_left_eq]

/-- Bob's sign observable deviates from a constant sign by at most twice the
square root of the mass of the answers carrying the other label. -/
theorem norm_bob_signObs_sub_const_sq_le (hA : MIPStarRE.QPBT.Measurement.IsProjective (T.A x))
    (hB : MIPStarRE.QPBT.Measurement.IsProjective (T.B y))
    (g : G.AnswerB → ZMod 2) (c : ZMod 2) :
    ‖applyOperatorToState (((bitSign c : ℝ) : ℂ) • (1 : Op (T.ιA × T.ιB)) -
        heteroKron 1 (signObs (T.B y) g)) T.ψ‖ ^ 2 ≤
      4 * bobEventWeight T y (fun b => c ≠ g b) := by
  have hconst : heteroKron (signObs (T.A x) (fun _ => c)) (1 : Op T.ιB) =
      ((bitSign c : ℝ) : ℂ) • (1 : Op (T.ιA × T.ιB)) := by
    rw [signObs, ← smul_one_eq_sum_smul_effect (T.A x) (((bitSign c : ℝ) : ℂ)),
      heteroKron_smul_left, heteroKron_one_one]
  grind [norm_alice_sub_bob_signObs_sq_le, le_trans, le_of_eq, outcome_event_weight_right_eq]

end SignDefect

/-! ## Comparison of Born masses with the game error -/

/-- Formalization-only: a squared state-dependent bound by four times a mass
which is itself bounded by `36 * ε` yields closeness at scale `12 * sqrt ε`. -/
theorem normCloseOn_of_sq_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {ψ : EuclideanSpace ℂ ι} {M N : Op ι} {m ε : ℝ}
    (hsq : ‖applyOperatorToState (M - N) ψ‖ ^ 2 ≤ 4 * m) (hm0 : 0 ≤ m)
    (hm : m ≤ 36 * ε) : NormCloseOn ψ (12 * Real.sqrt ε) M N := by
  have hε : (0 : ℝ) ≤ ε := by
    have h36 : (0 : ℝ) ≤ 36 * ε := le_trans hm0 hm
    linarith
  have hbound : ‖applyOperatorToState (M - N) ψ‖ ^ 2 ≤ (12 * Real.sqrt ε) ^ 2 := by
    have hsq' : (12 * Real.sqrt ε) ^ 2 = 144 * ε := by
      rw [mul_pow, Real.sq_sqrt hε]
      ring
    rw [hsq']
    linarith
  calc ‖applyOperatorToState (M - N) ψ‖
      = Real.sqrt (‖applyOperatorToState (M - N) ψ‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((12 * Real.sqrt ε) ^ 2) := Real.sqrt_le_sqrt hbound
    _ = 12 * Real.sqrt ε := Real.sqrt_sq (by positivity)

/-- Formalization-only: monotonicity of Alice's marginal event mass. -/
theorem alice_event_weight_mono (T : Strategy msGame) (x : MsType)
    (E F : MsAnswer → Prop) [DecidablePred E] [DecidablePred F]
    (h : ∀ a, E a → F a) : aliceEventWeight T x E ≤ aliceEventWeight T x F := by
  rw [← outcome_event_weight_left_eq T x x E, ← outcome_event_weight_left_eq T x x F]
  simp_all [outcome_event_weight_mono]

/-- Formalization-only: monotonicity of Bob's marginal event mass. -/
theorem bob_event_weight_mono (T : Strategy msGame) (y : MsType)
    (E F : MsAnswer → Prop) [DecidablePred E] [DecidablePred F]
    (h : ∀ b, E b → F b) : bobEventWeight T y E ≤ bobEventWeight T y F := by
  rw [← outcome_event_weight_right_eq T y y E, ← outcome_event_weight_right_eq T y y F]
  simp_all [outcome_event_weight_mono]

/-! ## The Magic Square reflections of the dilated strategy -/

variable (S : Strategy msGame)

/-- Alice's cell reflection at one position of a constraint question of the
dilated strategy, placed on its composite space.  This is a pre-isometry
observable of `msDilatedStrategy S`; the state-dependent relations below
evaluate it on `(msDilatedStrategy S).ψ`.  It is not the paper's post-isometry
operator $\tilde A$.  The post-isometry operators on the ideal state in
`thm:ms-rigidity` arise later by conjugating with the local isometries and using
the transfer theorems of issue Dengnifer/MIPStarRE-QPBT-bak#104.  Formalization-only
operator-relation
support for blueprint `ch13_qpbt_test.tex:224-253` and paper
`08_classical_and_quantum_low_degree_tests.tex:612-652`. -/
noncomputable def msCellObsA (i : Fin 6) (k : Fin 3) :
    Op ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB) :=
  heteroKron (signObs ((msDilatedStrategy S).A (MsType.constraint i))
    (constraintBitOrZero k)) 1

/-- Bob's cell reflection at one position of a constraint question of the
dilated strategy, placed on its composite space.  This is a pre-isometry
observable of `msDilatedStrategy S`; the state-dependent relations below
evaluate it on `(msDilatedStrategy S).ψ`.  It is not the paper's post-isometry
operator $\tilde B$.  The post-isometry operators on the ideal state in
`thm:ms-rigidity` arise later by conjugating with the local isometries and using
the transfer theorems of issue Dengnifer/MIPStarRE-QPBT-bak#104.  Formalization-only
operator-relation
support for blueprint `ch13_qpbt_test.tex:224-253` and paper
`08_classical_and_quantum_low_degree_tests.tex:612-652`. -/
noncomputable def msCellObsB (i : Fin 6) (k : Fin 3) :
    Op ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB) :=
  heteroKron 1 (signObs ((msDilatedStrategy S).B (MsType.constraint i))
    (constraintBitOrZero k))

/-- Alice's reflection at a variable question of the dilated strategy, placed on
the composite space. -/
noncomputable def msVarObsA (j : Fin 9) :
    Op ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB) :=
  heteroKron (signObs ((msDilatedStrategy S).A (MsType.var j)) msBitOrZero) 1

/-- Bob's reflection at a variable question of the dilated strategy, placed on
the composite space. -/
noncomputable def msVarObsB (j : Fin 9) :
    Op ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB) :=
  heteroKron 1 (signObs ((msDilatedStrategy S).B (MsType.var j)) msBitOrZero)

/-- Alice's cell operators are binary observables. -/
theorem isBinaryObservable_msCellObsA (i : Fin 6) (k : Fin 3) :
    IsBinaryObservable (msCellObsA S i k) :=
  isBinaryObservable_heteroKron_one
    (isBinaryObservable_signObs _ (msDilatedStrategy_isProjective_A S _) _)

/-- Bob's cell operators are binary observables. -/
theorem isBinaryObservable_msCellObsB (i : Fin 6) (k : Fin 3) :
    IsBinaryObservable (msCellObsB S i k) :=
  isBinaryObservable_one_heteroKron
    (isBinaryObservable_signObs _ (msDilatedStrategy_isProjective_B S _) _)

/-- Alice's variable operators are binary observables. -/
theorem isBinaryObservable_msVarObsA (j : Fin 9) :
    IsBinaryObservable (msVarObsA S j) :=
  isBinaryObservable_heteroKron_one
    (isBinaryObservable_signObs _ (msDilatedStrategy_isProjective_A S _) _)

/-- Bob's variable operators are binary observables. -/
theorem isBinaryObservable_msVarObsB (j : Fin 9) :
    IsBinaryObservable (msVarObsB S j) :=
  isBinaryObservable_one_heteroKron
    (isBinaryObservable_signObs _ (msDilatedStrategy_isProjective_B S _) _)

/-- The three cell reflections of one constraint question commute exactly. -/
theorem msCellObsA_comm (i : Fin 6) (k l : Fin 3) :
    msCellObsA S i k * msCellObsA S i l = msCellObsA S i l * msCellObsA S i k := by
  grind [msCellObsA, heteroKron_mul, signObs_comm, msDilatedStrategy_isProjective_A]

/-- The three cell reflections of one constraint question commute exactly, on
Bob's side as well. -/
theorem msCellObsB_comm (i : Fin 6) (k l : Fin 3) :
    msCellObsB S i k * msCellObsB S i l = msCellObsB S i l * msCellObsB S i k := by
  grind [msCellObsB, heteroKron_mul, signObs_comm, msDilatedStrategy_isProjective_B]

/-- Alice's cell reflection commutes exactly with Bob's variable reflection. -/
theorem msCellObsA_comm_msVarObsB (i : Fin 6) (k : Fin 3)
    (j : Fin 9) :
    msCellObsA S i k * msVarObsB S j = msVarObsB S j * msCellObsA S i k :=
  heteroKron_comm _ _

/-- Alice's variable reflection commutes exactly with Bob's cell reflection. -/
theorem msVarObsA_comm_msCellObsB (j : Fin 9) (i : Fin 6)
    (k : Fin 3) :
    msVarObsA S j * msCellObsB S i k = msCellObsB S i k * msVarObsA S j :=
  heteroKron_comm _ _

/-! ## The six row and column product relations -/

/-- The sum of the three answer bits reported for a constraint question, with
malformed answers contributing zero. -/
def constraintBitSum (a : MsAnswer) : ZMod 2 :=
  constraintBitOrZero 0 a + constraintBitOrZero 1 a + constraintBitOrZero 2 a

/-- An answer whose three reported bits do not sum to the prescribed parity is a
parity failure in the sense of the value-to-parity layer. -/
theorem constraintParityFailure_of_bitSum_ne (i : Fin 6) (a : MsAnswer)
    (h : constraintBitSum a ≠ msParity i) : ConstraintParityFailure i a := by
  cases a with
  | bit γ => exact wrong_constraint_answer_implies_parity_failure i (MsAnswer.bit γ) rfl
  | triple β =>
      intro hprod
      apply h
      have hsum : bitSign (∑ k : Fin 3, β k) = bitSign (msParity i) := by
        rw [bit_sign_sum_fin_three]
        exact hprod
      have hbit := bit_sign_injective hsum
      rw [Fin.sum_univ_three] at hbit
      exact hbit

/-- The product of Alice's three cell reflections of a constraint question is
the reflection attached to the sum of the three reported bits. -/
theorem msCellObsA_prod (i : Fin 6) :
    msCellObsA S i 0 * msCellObsA S i 1 * msCellObsA S i 2 =
      heteroKron (signObs ((msDilatedStrategy S).A (MsType.constraint i))
        constraintBitSum) 1 := by
  rw [msCellObsA, msCellObsA, msCellObsA, heteroKron_mul, heteroKron_mul,
    signObs_mul _ (msDilatedStrategy_isProjective_A S _),
    signObs_mul _ (msDilatedStrategy_isProjective_A S _), mul_one, one_mul]
  rfl

/-- The product of Bob's three cell reflections of a constraint question is the
reflection attached to the sum of the three reported bits. -/
theorem msCellObsB_prod (i : Fin 6) :
    msCellObsB S i 0 * msCellObsB S i 1 * msCellObsB S i 2 =
      heteroKron 1 (signObs ((msDilatedStrategy S).B (MsType.constraint i))
        constraintBitSum) := by
  rw [msCellObsB, msCellObsB, msCellObsB, heteroKron_mul, heteroKron_mul,
    signObs_mul _ (msDilatedStrategy_isProjective_B S _),
    signObs_mul _ (msDilatedStrategy_isProjective_B S _), mul_one, one_mul]
  rfl

/-- Formalization-only: nonnegativity of Alice's marginal event mass. -/
theorem alice_event_weight_nonneg (T : Strategy msGame) (x : MsType)
    (E : MsAnswer → Prop) [DecidablePred E] : 0 ≤ aliceEventWeight T x E := by
  rw [← outcome_event_weight_left_eq T x x E]
  simp [outcome_event_weight_nonneg]

/-- Formalization-only: nonnegativity of Bob's marginal event mass. -/
theorem bob_event_weight_nonneg (T : Strategy msGame) (y : MsType)
    (E : MsAnswer → Prop) [DecidablePred E] : 0 ≤ bobEventWeight T y E := by
  rw [← outcome_event_weight_right_eq T y y E]
  simp [outcome_event_weight_nonneg]

/-- Each of the six row and column relations holds for Alice's cell reflections
on the dilated state, with the sign prescribed by the corresponding linear
equation and with error `12 * sqrt ε`.  This is the first operator consequence
of `thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:224-253`. -/
theorem msCellObsA_prod_close (ε : ℝ) (hwin : 1 - ε ≤ S.value)
    (i : Fin 6) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε)
      (msCellObsA S i 0 * msCellObsA S i 1 * msCellObsA S i 2)
      (((bitSign (msParity i) : ℝ) : ℂ) • 1) := by
  have hsq := norm_alice_signObs_sub_const_sq_le (msDilatedStrategy S)
    (MsType.constraint i) (MsType.constraint i)
    (msDilatedStrategy_isProjective_A S _) (msDilatedStrategy_isProjective_B S _)
    constraintBitSum (msParity i)
  rw [← msCellObsA_prod] at hsq
  refine normCloseOn_of_sq_le hsq (alice_event_weight_nonneg _ _ _) ?_
  calc aliceEventWeight (msDilatedStrategy S) (MsType.constraint i)
        (fun a => constraintBitSum a ≠ msParity i)
      ≤ aliceEventWeight (msDilatedStrategy S) (MsType.constraint i)
          (ConstraintParityFailure i) :=
        alice_event_weight_mono _ _ _ _ fun a ha =>
          constraintParityFailure_of_bitSum_ne i a ha
    _ = aliceParityFailureMass S i := ms_dilated_strategy_alice_parity_failure_mass S i
    _ ≤ 36 * ε := alice_parity_failure_mass_le S ε hwin i

/-- Each of the six row and column relations holds for Bob's cell reflections on
the dilated state, with the sign prescribed by the corresponding linear equation
and with error `12 * sqrt ε`. -/
theorem msCellObsB_prod_close (ε : ℝ) (hwin : 1 - ε ≤ S.value)
    (i : Fin 6) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε)
      (((bitSign (msParity i) : ℝ) : ℂ) • 1)
      (msCellObsB S i 0 * msCellObsB S i 1 * msCellObsB S i 2) := by
  have hsq := norm_bob_signObs_sub_const_sq_le (msDilatedStrategy S)
    (MsType.constraint i) (MsType.constraint i)
    (msDilatedStrategy_isProjective_A S _) (msDilatedStrategy_isProjective_B S _)
    constraintBitSum (msParity i)
  rw [← msCellObsB_prod] at hsq
  refine normCloseOn_of_sq_le hsq (bob_event_weight_nonneg _ _ _) ?_
  calc bobEventWeight (msDilatedStrategy S) (MsType.constraint i)
        (fun b => msParity i ≠ constraintBitSum b)
      ≤ bobEventWeight (msDilatedStrategy S) (MsType.constraint i)
          (ConstraintParityFailure i) :=
        bob_event_weight_mono _ _ _ _ fun b hb =>
          constraintParityFailure_of_bitSum_ne i b (Ne.symm hb)
    _ = bobParityFailureMass S i := ms_dilated_strategy_bob_parity_failure_mass S i
    _ ≤ 36 * ε := bob_parity_failure_mass_le S ε hwin i

/-! ## Agreement of the two reflections attached to a common cell -/

/-- Alice's cell reflection agrees, on the dilated state and up to
`12 * sqrt ε`, with Bob's reflection at the same cell. -/
theorem msCellObsA_close_msVarObsB (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) (k : Fin 3) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε) (msCellObsA S i k)
      (msVarObsB S (msConstraintVars i k)) := by
  have hsq := norm_alice_sub_bob_signObs_sq_le (msDilatedStrategy S)
    (MsType.constraint i) (MsType.var (msConstraintVars i k))
    (msDilatedStrategy_isProjective_A S _) (msDilatedStrategy_isProjective_B S _)
    (constraintBitOrZero k) msBitOrZero
  refine normCloseOn_of_sq_le hsq (outcome_event_weight_nonneg _ _ _ _) ?_
  calc outcomeEventWeight (msDilatedStrategy S) (MsType.constraint i)
        (MsType.var (msConstraintVars i k))
        (fun a b => constraintBitOrZero k a ≠ msBitOrZero b)
      = forwardCellMismatchMass S i k :=
        ms_dilated_strategy_forward_cell_mismatch_mass S i k
    _ ≤ 36 * ε := forward_cell_mismatch_mass_le S ε hwin i k

/-- Alice's variable reflection agrees, on the dilated state and up to
`12 * sqrt ε`, with Bob's reflection at the same cell read from a constraint
question. -/
theorem msVarObsA_close_msCellObsB (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) (k : Fin 3) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε)
      (msVarObsA S (msConstraintVars i k)) (msCellObsB S i k) := by
  have hsq := norm_alice_sub_bob_signObs_sq_le (msDilatedStrategy S)
    (MsType.var (msConstraintVars i k)) (MsType.constraint i)
    (msDilatedStrategy_isProjective_A S _) (msDilatedStrategy_isProjective_B S _)
    msBitOrZero (constraintBitOrZero k)
  refine normCloseOn_of_sq_le hsq (outcome_event_weight_nonneg _ _ _ _) ?_
  calc outcomeEventWeight (msDilatedStrategy S) (MsType.var (msConstraintVars i k))
        (MsType.constraint i) (fun a b => msBitOrZero a ≠ constraintBitOrZero k b)
      = reverseCellMismatchMass S i k :=
        ms_dilated_strategy_reverse_cell_mismatch_mass S i k
    _ ≤ 36 * ε := reverse_cell_mismatch_mass_le S ε hwin i k

/-! ## Permuted row and column products -/

/-- The product of Alice's three cell reflections of a constraint question, in
any order in which the three positions occur once each, is the reflection
attached to the sum of the three reported bits. -/
theorem msCellObsA_prod_of (i : Fin 6) (k₀ k₁ k₂ : Fin 3)
    (hsum : ∀ a, constraintBitOrZero k₀ a + constraintBitOrZero k₁ a +
      constraintBitOrZero k₂ a = constraintBitSum a) :
    msCellObsA S i k₀ * msCellObsA S i k₁ * msCellObsA S i k₂ =
      heteroKron (signObs ((msDilatedStrategy S).A (MsType.constraint i))
        constraintBitSum) 1 := by
  have hkey : signObs ((msDilatedStrategy S).A (MsType.constraint i))
        (constraintBitOrZero k₀) *
      signObs ((msDilatedStrategy S).A (MsType.constraint i)) (constraintBitOrZero k₁) *
      signObs ((msDilatedStrategy S).A (MsType.constraint i)) (constraintBitOrZero k₂) =
      signObs ((msDilatedStrategy S).A (MsType.constraint i)) constraintBitSum := by
    rw [signObs_mul _ (msDilatedStrategy_isProjective_A S _),
      signObs_mul _ (msDilatedStrategy_isProjective_A S _)]
    congr 1
    funext a
    exact hsum a
  simp_all [msCellObsA, heteroKron_mul, mul_one]

/-- The product of Bob's three cell reflections of a constraint question, in any
order in which the three positions occur once each, is the reflection attached
to the sum of the three reported bits. -/
theorem msCellObsB_prod_of (i : Fin 6) (k₀ k₁ k₂ : Fin 3)
    (hsum : ∀ a, constraintBitOrZero k₀ a + constraintBitOrZero k₁ a +
      constraintBitOrZero k₂ a = constraintBitSum a) :
    msCellObsB S i k₀ * msCellObsB S i k₁ * msCellObsB S i k₂ =
      heteroKron 1 (signObs ((msDilatedStrategy S).B (MsType.constraint i))
        constraintBitSum) := by
  have hkey : signObs ((msDilatedStrategy S).B (MsType.constraint i))
        (constraintBitOrZero k₀) *
      signObs ((msDilatedStrategy S).B (MsType.constraint i)) (constraintBitOrZero k₁) *
      signObs ((msDilatedStrategy S).B (MsType.constraint i)) (constraintBitOrZero k₂) =
      signObs ((msDilatedStrategy S).B (MsType.constraint i)) constraintBitSum := by
    rw [signObs_mul _ (msDilatedStrategy_isProjective_B S _),
      signObs_mul _ (msDilatedStrategy_isProjective_B S _)]
    congr 1
    funext a
    exact hsum a
  simp_all [msCellObsB, heteroKron_mul, mul_one]

/-- Each permuted row or column product of Alice's cell reflections is close, on
the dilated state, to the sign prescribed by the corresponding linear
equation. -/
theorem msCellObsA_prod_close_of (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) (k₀ k₁ k₂ : Fin 3)
    (hsum : ∀ a, constraintBitOrZero k₀ a + constraintBitOrZero k₁ a +
      constraintBitOrZero k₂ a = constraintBitSum a) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε)
      (msCellObsA S i k₀ * msCellObsA S i k₁ * msCellObsA S i k₂)
      (((bitSign (msParity i) : ℝ) : ℂ) • 1) := by
  rw [msCellObsA_prod_of S i k₀ k₁ k₂ hsum, ← msCellObsA_prod S i]
  grind [msCellObsA_prod_close]

/-- Each permuted row or column product of Bob's cell reflections is close, on
the dilated state, to the sign prescribed by the corresponding linear
equation. -/
theorem msCellObsB_prod_close_of (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) (k₀ k₁ k₂ : Fin 3)
    (hsum : ∀ a, constraintBitOrZero k₀ a + constraintBitOrZero k₁ a +
      constraintBitOrZero k₂ a = constraintBitSum a) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε)
      (((bitSign (msParity i) : ℝ) : ℂ) • 1)
      (msCellObsB S i k₀ * msCellObsB S i k₁ * msCellObsB S i k₂) := by
  rw [msCellObsB_prod_of S i k₀ k₁ k₂ hsum, ← msCellObsB_prod S i]
  grind [msCellObsB_prod_close]

/-! ## The two logical Pauli pairs -/

/-! ## Unit scalars -/

variable (c : ZMod 2)

/-- The sign of a binary value has modulus one as a complex number. -/
theorem norm_bitSign_ofReal : ‖((bitSign c : ℝ) : ℂ)‖ = 1 := by
  grind [Complex.norm_real, Real.norm_eq_abs, bit_sign_eq_one_or_neg_one]

/-- The square of the sign of a binary value is one. -/
theorem bitSign_ofReal_mul_self :
    ((bitSign c : ℝ) : ℂ) * ((bitSign c : ℝ) : ℂ) = 1 := by
  rcases bit_sign_eq_one_or_neg_one c with h | h <;> rw [h] <;> norm_num

/-! ## Building blocks of the solution-group computation -/

/-- If `X Y Z` is close to `s • 1` for commuting binary observables, then `Y`
is close to `s • (X Z)`. -/
theorem NormCloseOn.of_prod_close {ι : Type} [Fintype ι] [DecidableEq ι]
    {ψ : EuclideanSpace ℂ ι} {δ : ℝ} {X Y Z : Op ι} {s : ℂ}
    (hX : IsBinaryObservable X) (hZ : IsBinaryObservable Z) (hZY : Z * Y = Y * Z)
    (hZX : Z * X = X * Z) (h : NormCloseOn ψ δ (X * Y * Z) (s • 1)) :
    NormCloseOn ψ δ Y (s • (X * Z)) := by
  have e : Z * X * (X * Y * Z) = Y := by
    rw [show Z * X * (X * Y * Z) = Z * (X * X) * Y * Z by noncomm_ring, hX.mul_self_eq_one,
      mul_one, hZY, mul_assoc, hZ.mul_self_eq_one, mul_one]
  have h' := NormCloseOn.isometry_mul (hZ.mul hX hZX).isometry h
  rwa [e, Matrix.mul_smul, mul_one, hZX] at h'

/-- One of Bob's three cell reflections of a constraint question is close, on
the dilated state, to the signed product of the other two. -/
theorem msCellObsB_single_close (ε : ℝ) (hwin : 1 - ε ≤ S.value)
    (i : Fin 6) (k₀ k₁ k₂ : Fin 3)
    (hsum : ∀ a, constraintBitOrZero k₀ a + constraintBitOrZero k₁ a +
      constraintBitOrZero k₂ a = constraintBitSum a) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε) (msCellObsB S i k₁)
      (((bitSign (msParity i) : ℝ) : ℂ) •
        (msCellObsB S i k₀ * msCellObsB S i k₂)) :=
  NormCloseOn.of_prod_close (isBinaryObservable_msCellObsB S i k₀)
    (isBinaryObservable_msCellObsB S i k₂) (msCellObsB_comm S i k₂ k₁)
    (msCellObsB_comm S i k₂ k₀) (msCellObsB_prod_close_of S ε hwin i k₀ k₁ k₂ hsum).symm

/-- A product of two of Bob's cell reflections is close, on the dilated state,
to the product of Alice's variable reflections at the same two cells, taken in
the reverse order. -/
theorem msCellObsB_mul_close (ε : ℝ) (hwin : 1 - ε ≤ S.value)
    (I J : Fin 6) (k l : Fin 3) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε + 12 * Real.sqrt ε)
      (msCellObsB S I k * msCellObsB S J l)
      (msVarObsA S (msConstraintVars J l) * msVarObsA S (msConstraintVars I k)) := by
  have h1 := NormCloseOn.isometry_mul (isBinaryObservable_msCellObsB S I k).isometry
    (msVarObsA_close_msCellObsB S ε hwin J l).symm
  rw [← msVarObsA_comm_msCellObsB S (msConstraintVars J l) I k] at h1
  exact h1.trans (NormCloseOn.isometry_mul (isBinaryObservable_msVarObsA S _).isometry
    (msVarObsA_close_msCellObsB S ε hwin I k).symm)

/-- Two of Bob's cell reflections attached to a common cell by two different
constraint questions are close on the dilated state. -/
theorem msCellObsB_close_of_same_cell (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (I J : Fin 6) (k l : Fin 3)
    (hcell : msConstraintVars I k = msConstraintVars J l) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε + 12 * Real.sqrt ε)
      (msCellObsB S I k) (msCellObsB S J l) :=
  (hcell ▸ (msVarObsA_close_msCellObsB S ε hwin I k).symm).trans
    (msVarObsA_close_msCellObsB S ε hwin J l)

end

end MIPStarRE.QPBT.MagicSquareRigidity
