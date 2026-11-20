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
  · left
    rfl
  · norm_num [bitSign, ZMod.val_one]

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
  · simp_all

section SignDefect

variable {G : Game}

/-- Two sign observables of the two players, placed on the composite space,
differ in the state-dependent norm by at most twice the square root of the Born
mass of the answer pairs on which the two labels disagree.  This is the estimate
that turns every mass of the value-to-parity layer into an operator relation of
`thm:ms-rigidity`, blueprint `ch13_qpbt_test.tex:224-253`. -/
theorem norm_alice_sub_bob_signObs_sq_le {T : Strategy G} {x : G.QuestionA}
    {y : G.QuestionB} (hA : MIPStarRE.QPBT.Measurement.IsProjective (T.A x))
    (hB : MIPStarRE.QPBT.Measurement.IsProjective (T.B y))
    (f : G.AnswerA → ZMod 2) (g : G.AnswerB → ZMod 2) :
    ‖applyOperatorToState (heteroKron (signObs (T.A x) f) 1 -
        heteroKron 1 (signObs (T.B y) g)) T.ψ‖ ^ 2 ≤
      4 * outcomeEventWeight T x y (fun a b => f a ≠ g b) := by
  classical
  have hAone : 1 = ∑ a, (1 : ℂ) • (T.A x).effect a := by
    simpa using smul_one_eq_sum_smul_effect (T.A x) 1
  have hBone : 1 = ∑ b, (1 : ℂ) • (T.B y).effect b := by
    simpa using smul_one_eq_sum_smul_effect (T.B y) 1
  have hexpand : heteroKron (signObs (T.A x) f) 1 - heteroKron 1 (signObs (T.B y) g) =
      ∑ a, ∑ b, ((bitSign (f a) - bitSign (g b) : ℝ) : ℂ) •
        heteroKron ((T.A x).effect a) ((T.B y).effect b) := by
    rw [signObs, signObs]
    nth_rewrite 1 [hBone]
    nth_rewrite 1 [hAone]
    rw [joint_expand, joint_expand, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    congr 1 with b
    rw [← sub_smul]
    congr 1
    push_cast
    ring
  rw [hexpand]
  refine norm_apply_joint_defect_sq_le T x y hA hB
    _ (fun a b => f a ≠ g b) ?_ ?_
  · intro a b
    rcases bit_sign_eq_one_or_neg_one (f a) with h1 | h1 <;>
      rcases bit_sign_eq_one_or_neg_one (g b) with h2 | h2 <;>
        simp only [h1, h2] <;> norm_num
  · intro a b hab
    simp_all

/-- Alice's sign observable deviates from a constant sign by at most twice the
square root of the mass of the answers carrying the other label. -/
theorem norm_alice_signObs_sub_const_sq_le (T : Strategy G) (x : G.QuestionA)
    (y : G.QuestionB) (hA : MIPStarRE.QPBT.Measurement.IsProjective (T.A x))
    (hB : MIPStarRE.QPBT.Measurement.IsProjective (T.B y))
    (f : G.AnswerA → ZMod 2) (c : ZMod 2) :
    ‖applyOperatorToState (heteroKron (signObs (T.A x) f) 1 -
        ((bitSign c : ℝ) : ℂ) • (1 : Op (T.ιA × T.ιB))) T.ψ‖ ^ 2 ≤
      4 * aliceEventWeight T x (fun a => f a ≠ c) := by
  classical
  have hconst : heteroKron (1 : Op T.ιA) (signObs (T.B y) (fun _ => c)) =
      ((bitSign c : ℝ) : ℂ) • 1 := by
    rw [signObs, ← smul_one_eq_sum_smul_effect,
      heteroKron_smul_right, heteroKron_one_one]
  have h := norm_alice_sub_bob_signObs_sq_le hA hB f (fun _ => c)
  rw [hconst] at h
  refine le_trans h (le_of_eq ?_)
  congr 1
  apply outcome_event_weight_left_eq

end SignDefect

/-! ## Comparison of Born masses with the game error -/

/-- Formalization-only: a squared state-dependent bound by four times a mass
which is itself bounded by `36 * ε` yields closeness at scale `12 * sqrt ε`. -/
private theorem normCloseOn_of_sq_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {ψ : EuclideanSpace ℂ ι} {M N : Op ι} {m ε : ℝ}
    (hsq : ‖applyOperatorToState (M - N) ψ‖ ^ 2 ≤ 4 * m) (hm0 : 0 ≤ m)
    (hm : m ≤ 36 * ε) : NormCloseOn ψ (12 * Real.sqrt ε) M N := by
  have hε : 0 ≤ ε := by
    linarith
  have hbound : ‖applyOperatorToState (M - N) ψ‖ ^ 2 ≤ (12 * Real.sqrt ε) ^ 2 := by
    have hsq' : (12 * Real.sqrt ε) ^ 2 = 144 * ε := by
      rw [mul_pow, Real.sq_sqrt hε]
      ring
    linarith
  calc _
      = _ :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt hbound
    _ = _ := Real.sqrt_sq (by positivity)

/-- Formalization-only: monotonicity of Alice's marginal event mass. -/
private theorem alice_event_weight_mono (T : Strategy msGame) (x : MsType)
    (E F : MsAnswer → Prop) [DecidablePred E] [DecidablePred F]
    (h : ∀ a, E a → F a) : aliceEventWeight T x E ≤ aliceEventWeight T x F := by
  rw [← outcome_event_weight_left_eq, ← outcome_event_weight_left_eq T x x F]
  solve_by_elim [outcome_event_weight_mono]

/-! ## The Magic Square reflections of the dilated strategy -/

section

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

/-- Bob's reflection at a variable question of the dilated strategy, placed on
the composite space. -/
noncomputable def msVarObsB (j : Fin 9) :
    Op ((msDilatedStrategy S).ιA × (msDilatedStrategy S).ιB) :=
  heteroKron 1 (signObs ((msDilatedStrategy S).B (MsType.var j)) msBitOrZero)

/-- Alice's cell operators are binary observables. -/
theorem isBinaryObservable_msCellObsA (i : Fin 6) (k : Fin 3) :
    IsBinaryObservable (msCellObsA S i k) :=
  isBinaryObservable_heteroKron_one
    (isBinaryObservable_signObs (msDilatedStrategy_isProjective_A S _) _)

/-- Bob's variable operators are binary observables. -/
theorem isBinaryObservable_msVarObsB (j : Fin 9) :
    IsBinaryObservable (msVarObsB S j) :=
  isBinaryObservable_one_heteroKron
    (isBinaryObservable_signObs (msDilatedStrategy_isProjective_B S _) _)

/-- The three cell reflections of one constraint question commute exactly. -/
theorem msCellObsA_comm (i : Fin 6) (k l : Fin 3) :
    msCellObsA S i k * msCellObsA S i l = msCellObsA S i l * msCellObsA S i k := by
  rw [msCellObsA, msCellObsA, heteroKron_mul, heteroKron_mul,
    signObs_comm _ (msDilatedStrategy_isProjective_A S _)]

/-- Alice's cell reflection commutes exactly with Bob's variable reflection. -/
theorem msCellObsA_comm_msVarObsB (i : Fin 6) (k : Fin 3)
    (j : Fin 9) :
    msCellObsA S i k * msVarObsB S j = msVarObsB S j * msCellObsA S i k :=
  heteroKron_comm _ _

end

/-! ## The six row and column product relations -/

/-- The sum of the three answer bits reported for a constraint question, with
malformed answers contributing zero. -/
def constraintBitSum (a : MsAnswer) : ZMod 2 :=
  constraintBitOrZero 0 a + constraintBitOrZero 1 a + constraintBitOrZero 2 a

section

variable (S : Strategy msGame) (i : Fin 6)

/-- The product of Alice's three cell reflections of a constraint question is
the reflection attached to the sum of the three reported bits. -/
theorem msCellObsA_prod :
    msCellObsA S i 0 * msCellObsA S i 1 * msCellObsA S i 2 =
      heteroKron (signObs ((msDilatedStrategy S).A (MsType.constraint i))
        constraintBitSum) 1 := by
  rw [msCellObsA, msCellObsA, msCellObsA, heteroKron_mul, heteroKron_mul,
    signObs_mul _ (msDilatedStrategy_isProjective_A S _),
    signObs_mul _ (msDilatedStrategy_isProjective_A S _), mul_one, one_mul]
  rfl

end

/-- Formalization-only: nonnegativity of Alice's marginal event mass. -/
private theorem alice_event_weight_nonneg (T : Strategy msGame) (x : MsType)
    (E : MsAnswer → Prop) [DecidablePred E] : 0 ≤ aliceEventWeight T x E := by
  rw [← outcome_event_weight_left_eq T x x E]
  apply outcome_event_weight_nonneg

/-! ## Agreement of the two reflections attached to a common cell -/

/-- Alice's cell reflection agrees, on the dilated state and up to
`12 * sqrt ε`, with Bob's reflection at the same cell. -/
theorem msCellObsA_close_msVarObsB {S : Strategy msGame} {ε : ℝ}
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) (k : Fin 3) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε) (msCellObsA S i k)
      (msVarObsB S (msConstraintVars i k)) := by
  classical
  refine normCloseOn_of_sq_le (norm_alice_sub_bob_signObs_sq_le
    (msDilatedStrategy_isProjective_A S _) (msDilatedStrategy_isProjective_B S _)
    _ msBitOrZero) (outcome_event_weight_nonneg _ _ _ _) ?_
  refine Eq.trans_le (ms_dilated_strategy_forward_cell_mismatch_mass S i k) ?_
  solve_by_elim [forward_cell_mismatch_mass_le]

/-! ## Permuted row and column products -/

/-- The product of Alice's three cell reflections of a constraint question, in
any order in which the three positions occur once each, is the reflection
attached to the sum of the three reported bits. -/
theorem msCellObsA_prod_of (S : Strategy msGame) (i : Fin 6) (k₀ k₁ k₂ : Fin 3)
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
    simp_all [signObs_mul _ (msDilatedStrategy_isProjective_A S _)]
  rw [msCellObsA, msCellObsA, msCellObsA, heteroKron_mul, heteroKron_mul]
  simp
  rw [hkey]

/-- Each permuted row or column product of Alice's cell reflections is close, on
the dilated state, to the sign prescribed by the corresponding linear
equation. -/
theorem msCellObsA_prod_close_of (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) (k₀ k₁ k₂ : Fin 3)
    (hsum : ∀ a, constraintBitOrZero k₀ a + constraintBitOrZero k₁ a +
      constraintBitOrZero k₂ a = constraintBitSum a) :
    NormCloseOn (msDilatedStrategy S).ψ (12 * Real.sqrt ε)
      (msCellObsA S i k₀ * msCellObsA S i k₁ * msCellObsA S i k₂)
      (((bitSign (msParity i) : ℝ) : ℂ) • 1) := by
  rw [msCellObsA_prod_of S i k₀ k₁ k₂ hsum, ← msCellObsA_prod]
  classical
  have hsq := norm_alice_signObs_sub_const_sq_le (msDilatedStrategy S)
    (MsType.constraint i) (MsType.constraint i)
    (msDilatedStrategy_isProjective_A S _) (msDilatedStrategy_isProjective_B S _)
    constraintBitSum (msParity i)
  rw [← msCellObsA_prod] at hsq
  refine normCloseOn_of_sq_le hsq (alice_event_weight_nonneg _ _ _) ?_
  calc _
      ≤ aliceEventWeight (msDilatedStrategy S) (MsType.constraint i)
          (ConstraintParityFailure i) :=
        alice_event_weight_mono _ _ _ _ fun a ha =>
          (by
            cases a with
            | bit γ => solve_by_elim [wrong_constraint_answer_implies_parity_failure]
            | triple β =>
                intro hprod
                apply ha
                have hsum : bitSign (∑ k : Fin 3, β k) = bitSign (msParity i) := by
                  rw [bit_sign_sum_fin_three]
                  exact hprod
                have hbit := bit_sign_injective hsum
                rw [Fin.sum_univ_three] at hbit
                exact hbit)
    _ = aliceParityFailureMass S i := (ms_dilated_strategy_alice_event_weight S _ _)
    _ ≤ 36 * ε := alice_parity_failure_mass_le S ε hwin i

/-! ## The two logical Pauli pairs -/

/-! ## Unit scalars -/

/-! ## Building blocks of the solution-group computation -/

end

end MIPStarRE.QPBT.MagicSquareRigidity
