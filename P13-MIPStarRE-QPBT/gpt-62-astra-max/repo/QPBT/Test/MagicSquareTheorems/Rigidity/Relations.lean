module

public import QPBT.Test.MagicSquareTheorems.Basic

/-!
# Magic Square value-to-parity relations

This file extracts the elementary probability relations used at the start of
the Magic Square rigidity argument.  A strategy of value at least `1 - ε` has
total rejection mass at most `ε`.  Since the question distribution is
supported on at most 36 directed incidences, the rejection mass at each
incidence is at most `36 * ε`.  This controls malformed answers, consistency
of the two reported bits at every cell, and the parity product on each of the
six row or column constraints.

The arguments apply to arbitrary finite POVMs.  In particular, malformed
answers remain in the event masses when `msBitOrZero` and
`constraintBitOrZero` turn the common answer alphabet into binary outcomes.

## References

The Magic Square game is defined in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:512-610`
and blueprint `def:ms-game`.  These relations are the
probabilistic input to the rigidity result cited at paper lines 612-652 from
Coladangelo--Stark, Theorem 6.9.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## The directed incidence distribution -/

/-- The 36 possible directed constraint-variable incidences. -/
def directedIncidence : ((Fin 6 × Fin 3) × Bool) → MsType × MsType
  | ((i, k), false) => (.constraint i, .var (msConstraintVars i k))
  | ((i, k), true) => (.var (msConstraintVars i k), .constraint i)

/-- Every question pair in the Magic Square distribution is a directed incidence. -/
theorem ms_support_subset_directed_incidences :
    (graphDistribution msEdges_nonempty).support ⊆
      (Finset.univ : Finset ((Fin 6 × Fin 3) × Bool)).image directedIncidence := by
  intro xy hxy
  rcases Finset.mem_image.mp ((Finset.mem_filter.mp hxy).2) with ⟨ik, _hik, heq⟩
  have heq' :
      ((.constraint ik.1, .var (msConstraintVars ik.1 ik.2))) = xy ∨
        ((.constraint ik.1, .var (msConstraintVars ik.1 ik.2))) =
          xy.swap :=
    (Sym2.mk_eq_mk_iff).mp heq
  rcases heq' with heq' | heq'
  · refine Finset.mem_image.mpr ⟨(ik, false), Finset.mem_univ _, ?_⟩
    exact heq'
  · refine Finset.mem_image.mpr ⟨(ik, true), Finset.mem_univ _, ?_⟩
    exact congrArg Prod.swap heq'

section

variable (i : Fin 6) (k : Fin 3)

/-- A constraint-to-variable incidence belongs to the question support. -/
theorem ms_forward_incidence_mem_support :
    (.constraint i, .var (msConstraintVars i k)) ∈
      (graphDistribution msEdges_nonempty).support := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact Finset.mem_image.mpr ⟨(i, k), Finset.mem_univ _, rfl⟩

end

/-- Every supported question pair has probability at least `1 / 36`. -/
theorem ms_question_weight_ge {xy : MsType × MsType}
    (hxy : xy ∈ (graphDistribution msEdges_nonempty).support) :
    (1 : ℝ) / 36 ≤ (graphDistribution msEdges_nonempty).weight xy := by
  have hmemFilter :
      xy ∈ (Finset.univ.filter fun ab =>
        Sym2.mk ab.1 ab.2 ∈ msEdges) := hxy
  rw [show (graphDistribution msEdges_nonempty).weight xy =
      _ by
    change (Distribution.uniformOnFinset
        (Finset.univ.filter fun ab =>
          Sym2.mk ab.1 ab.2 ∈ msEdges)).weight xy =
      1 / (((Finset.univ : Finset (MsType × MsType)).filter fun ab =>
        Sym2.mk ab.1 ab.2 ∈ msEdges).card : ℝ)
    simp [*]]
  apply one_div_le_one_div_of_le
  · exact_mod_cast Finset.card_pos.mpr ⟨xy, hxy⟩
  · exact_mod_cast (by
                     calc
                       _ ≤
                           ((Finset.univ : Finset ((Fin 6 × Fin 3) × Bool)).image
                             directedIncidence).card :=
                         Finset.card_le_card ms_support_subset_directed_incidences
                       _ ≤ (Finset.univ : Finset ((Fin 6 × Fin 3) × Bool)).card :=
                         Finset.card_image_le
                       _ = 36 := by norm_num)

/-! ## Rejection mass from the game value -/

private instance msWinFalseDecidableRel (x y : MsType) :
    DecidableRel (fun a b : MsAnswer => msWinPredicate x y a b = false) :=
  fun _ _ => inferInstance

section

variable (S : Strategy msGame)

/-- The rejection mass conditioned on a question pair. -/
noncomputable def rejectionMass (x y : MsType) : ℝ :=
  @outcomeEventWeight msGame S x y
    (fun a b => msWinPredicate x y a b = false) (fun _ _ => inferInstance)

/-- The acceptance mass conditioned on a question pair. -/
noncomputable def acceptanceMass (x y : MsType) : ℝ :=
  @outcomeEventWeight msGame S x y
    (fun a b => msWinPredicate x y a b = true) (fun _ _ => inferInstance)

/-- The rejection mass averaged over the Magic Square question distribution. -/
noncomputable def totalRejectionMass : ℝ :=
  avgOver (graphDistribution msEdges_nonempty) fun xy =>
    rejectionMass S xy.1 xy.2

/-- Total rejection mass is exactly one minus the strategy value. -/
theorem total_rejection_mass_eq_one_sub_value :
    totalRejectionMass S = 1 - S.value := by
  rw [show S.value = avgOver (graphDistribution msEdges_nonempty) (fun xy =>
      acceptanceMass S xy.1 xy.2) by aesop]
  calc
    _ =
        avgOver (graphDistribution msEdges_nonempty) (fun xy =>
          1 - acceptanceMass S xy.1 xy.2) := by
      apply avgOver_congr
      intro xy
      linarith [show acceptanceMass S xy.1 xy.2 + rejectionMass S xy.1 xy.2 = 1 by
        rw [← show (∑ a : MsAnswer, ∑ b : MsAnswer, outcomeWeight S xy.1 xy.2 a b) = 1 by
          apply outcomeWeight_sum_eq_one S]
        unfold acceptanceMass rejectionMass outcomeEventWeight
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.sum_add_distrib]
        grind]
    _ = _ := avgOver_sub _ _ _
    _ = _ := by
      rw [avgOver_const_of_isProbability _ (by
        apply Distribution.uniformOnFinset_isProbability
        refine ⟨(.constraint 0, .var (msConstraintVars 0 0)), ?_⟩
        simp [msEdges])]

/-- Conditioned rejection mass is nonnegative. -/
theorem rejection_mass_nonneg (x y : MsType) :
    0 ≤ rejectionMass S x y :=
  outcome_event_weight_nonneg S x y _

/-- A supported conditioned rejection mass is at most 36 times total rejection. -/
theorem rejection_mass_le_thirty_six_mul_total
    {xy : MsType × MsType}
    (hxy : xy ∈ (graphDistribution msEdges_nonempty).support) :
    rejectionMass S xy.1 xy.2 ≤ 36 * totalRejectionMass S := by
  have hrejection :=
    rejection_mass_nonneg S xy.1 xy.2
  have hweight := ms_question_weight_ge hxy
  have hterm :
      (graphDistribution msEdges_nonempty).weight xy *
          rejectionMass S xy.1 xy.2 ≤ totalRejectionMass S := by
    unfold totalRejectionMass avgOver
    exact Finset.single_le_sum
      (fun z _ => mul_nonneg
        ((graphDistribution msEdges_nonempty).nonnegative z)
        (rejection_mass_nonneg S z.1 z.2)) hxy
  nlinarith

/-- A supported conditioned rejection mass is at most `36 * ε`. -/
theorem rejection_mass_le (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) {xy : MsType × MsType}
    (hxy : xy ∈ (graphDistribution msEdges_nonempty).support) :
    rejectionMass S xy.1 xy.2 ≤ 36 * ε := by
  refine le_trans (rejection_mass_le_thirty_six_mul_total S hxy) ?_
  exact mul_le_mul_of_nonneg_left ((by
                                   rw [total_rejection_mass_eq_one_sub_value]
                                   linarith)) (by norm_num)

/-- An event which always rejects has mass at most the conditioned rejection mass. -/
theorem outcome_event_weight_le_rejection_mass {x y : MsType}
    {E : MsAnswer → MsAnswer → Prop} [DecidableRel E]
    (hE : ∀ a b, E a b → msWinPredicate x y a b = false) :
    outcomeEventWeight S x y E ≤ rejectionMass S x y := outcome_event_weight_mono S x y E (fun a b => msWinPredicate x y a b = false) hE

end

/-! ## Malformed answers and cell consistency -/

/-- The selected constraint bit, with a wrong-form single-bit answer folded to zero. -/
def constraintBitOrZero (k : Fin 3) : MsAnswer → ZMod 2
  | .triple β => β k
  | .bit _ => 0

/-- Whether an answer has the wrong form for a constraint question. -/
def wrongConstraintAnswer : MsAnswer → Bool
  | .triple _ => false
  | .bit _ => true

/-- The three cells in any fixed row or column are distinct. -/
theorem constraint_vars_injective (i : Fin 6) : Function.Injective (msConstraintVars i) := by
  intro k l hkl
  unfold msConstraintVars at hkl
  split at hkl <;> simp only [Fin.mk.injEq] at hkl ⊢ <;> omega

/-- Every Magic Square variable is incident to a row constraint. -/
theorem every_variable_is_incident (j : Fin 9) :
    ∃ i : Fin 6, ∃ k : Fin 3, msConstraintVars i k = j := by
  let i : Fin 6 := ⟨j.val / 3, by omega⟩
  let k : Fin 3 := ⟨j.val % 3, Nat.mod_lt _ (by omega)⟩
  refine ⟨i, k, ?_⟩
  apply Fin.ext
  simp only [msConstraintVars, i, k]
  rw [if_pos (by omega)]
  omega

section

variable (S : Strategy msGame) (i : Fin 6) (k : Fin 3)

/-- The forward-incidence mass on which the two totalized cell bits disagree. -/
noncomputable def forwardCellMismatchMass : ℝ :=
  @outcomeEventWeight msGame S (.constraint i) (.var (msConstraintVars i k))
    (fun a b => constraintBitOrZero k a ≠ msBitOrZero b) (fun _ _ => inferInstance)

end

section

variable (i : Fin 6) (k : Fin 3) (a b : MsAnswer)

private theorem forward_cell_mismatch_rejects (hmismatch : constraintBitOrZero k a ≠ msBitOrZero b) :
    msWinPredicate (.constraint i) (.var (msConstraintVars i k)) a b = false := by
  cases a with
  | bit γa => rfl
  | triple β =>
      cases b with
      | triple βb => rfl
      | bit γ =>
          rw [msWinPredicate, decide_eq_false_iff_not]
          intro haccept
          rcases haccept.2 with ⟨l, hl, hbit⟩
          have hlk := constraint_vars_injective i hl
          subst l
          exact hmismatch hbit

end

/-- Every forward directed incidence has cell-mismatch mass at most `36 * ε`. -/
theorem forward_cell_mismatch_mass_le (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) (k : Fin 3) :
    forwardCellMismatchMass S i k ≤ 36 * ε := by
  unfold forwardCellMismatchMass
  refine le_trans (outcome_event_weight_le_rejection_mass S (forward_cell_mismatch_rejects i k)) ?_
  exact rejection_mass_le S ε hwin (ms_forward_incidence_mem_support i k)

/-! ## Row and column parity products -/

/-- The real sign `(-1)^b` associated with a binary answer. -/
def bitSign (b : ZMod 2) : ℝ :=
  (-1 : ℝ) ^ b.val

/-- The binary sign turns addition into multiplication. -/
theorem bit_sign_add (b c : ZMod 2) :
    bitSign (b + c) = bitSign b * bitSign c := by
  unfold bitSign
  rw [ZMod.val_add, ← neg_one_pow_eq_pow_mod_two]
  apply pow_add

/-- The sign of a three-bit parity is the product of the three signs. -/
theorem bit_sign_sum_fin_three (β : Fin 3 → ZMod 2) :
    bitSign (∑ k : Fin 3, β k) = ∏ k : Fin 3, bitSign (β k) := by
  simp [Fin.sum_univ_three, Fin.prod_univ_three, bit_sign_add]

/-- The product of the three output signs, with malformed constraint answers
assigned zero so that they remain parity failures. -/
def constraintParityProduct : MsAnswer → ℝ
  | .triple β => ∏ k : Fin 3, bitSign (β k)
  | .bit _ => 0

section

variable (i : Fin 6)

/-- Failure of the required sign product for one row or column constraint. -/
def ConstraintParityFailure (a : MsAnswer) : Prop :=
  constraintParityProduct a ≠ bitSign (msParity i)

/-- Equality of the real parity signs is classically decidable on the finite
Magic Square answer alphabet. -/
noncomputable instance constraintParityFailureDecidablePred :
    DecidablePred (ConstraintParityFailure i) :=
  fun a => Classical.propDecidable (ConstraintParityFailure i a)

/-- Every wrong-form constraint answer is included in the parity-failure event. -/
theorem wrong_constraint_answer_implies_parity_failure (a : MsAnswer)
    (ha : wrongConstraintAnswer a = true) : ConstraintParityFailure i a := by
  cases a with
  | triple β => simp_all [wrongConstraintAnswer]
  | bit γ =>
      exact ((pow_ne_zero _ (by norm_num))).symm

end

section

variable (S : Strategy msGame) (i : Fin 6)

/-- Alice's local failure mass for the row or column sign product. -/
noncomputable def aliceParityFailureMass : ℝ :=
  @aliceEventWeight msGame S (.constraint i) (ConstraintParityFailure i)
    (constraintParityFailureDecidablePred i)

end

section

variable (i : Fin 6) (k : Fin 3) (a b : MsAnswer)

private theorem forward_parity_failure_rejects (hparity : ConstraintParityFailure i a) :
    msWinPredicate (.constraint i) (.var (msConstraintVars i k)) a b = false := by
  cases a with
  | bit δ => rfl
  | triple β =>
      cases b with
      | triple βb => rfl
      | bit γ =>
          rw [msWinPredicate, decide_eq_false_iff_not]
          intro haccept
          apply hparity
          refine Eq.trans ((bit_sign_sum_fin_three β).symm) ?_
          rw [haccept.1]

end

/-- Alice satisfies each of the six row or column sign products up to mass `36 * ε`. -/
theorem alice_parity_failure_mass_le (S : Strategy msGame) (ε : ℝ)
    (hwin : 1 - ε ≤ S.value) (i : Fin 6) :
    aliceParityFailureMass S i ≤ 36 * ε := by
  unfold aliceParityFailureMass
  rw [← outcome_event_weight_left_eq]
  refine le_trans (outcome_event_weight_le_rejection_mass S (forward_parity_failure_rejects i 0)) ?_
  exact rejection_mass_le S ε hwin (ms_forward_incidence_mem_support i 0)

end

end MIPStarRE.QPBT.MagicSquareRigidity
