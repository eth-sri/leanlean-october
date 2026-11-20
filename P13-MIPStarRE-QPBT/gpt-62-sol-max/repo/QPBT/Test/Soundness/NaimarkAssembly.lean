module

public import QPBT.Test.Soundness.NaimarkOperatorTransfer
public import QPBT.Test.Soundness.ProjectiveSetting
public import QPBT.Test.Soundness.ScalarAbsorption

/-!
# Pauli isometry bounds for arbitrary strategies

The projective-setting isometry bounds are composed with the questionwise
Naimark dilation.  An arbitrary Pauli-test strategy winning with probability at
least `1 - ε` dilates to a projective setting at the same error, the projective
bounds apply there, and the resulting witness is pulled back to the original
spaces.  The state comparison transfers as an equality; both operator families
transfer with the dilation constants of `pauli_naimark_operator_distanceA_le`,
which the enlarged universal prefactor absorbs.  The error domain is still
restricted to `[0, 1]`.

## References

This is a formalization-only support result for blueprint `thm:pauli`, whose
source statement is at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
The source performs the projective reduction in one sentence at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-190`, and the
isometry passage is at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
Blueprint `thm:pauli-arbitrary-strategy-isometry-support`; issue Dengnifer/MIPStarRE-QPBT-bak#614.
-/

@[expose] public section

namespace MIPStarRE.QPBT

noncomputable section

/-- **Scope restriction:** the three Pauli soundness estimates for an
*arbitrary* strategy whose value is at least `1 - ε`, still restricted to
`0 ≤ ε ≤ 1`.  The projectivity hypothesis of
`exists_projective_setting_isometry_bounds` is discharged by the Naimark
dilation `pauliNaimarkSetting`, which preserves the value exactly, and the
witness is returned to the original spaces by `pauliNaimarkWitness`.  The
universal prefactor grows from `a` to `21 * a ^ 2`, which absorbs the
`3 * dilated + 6 * stateError ^ 2` transfer constants; the exponent `b` is
unchanged.  No hypothesis beyond the source premises is added.

This is a Lean-only support result, not the unrestricted source theorem at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`;
the remaining `1 < ε` part of the source domain is supplied by
`pauli_isometry_bounds_extend_epsilon`. -/
theorem exists_arbitrary_strategy_isometry_bounds :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : AdmissibleParams) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
        ∀ S : Strategy (pauliBasisTest P), 1 - ε ≤ S.value →
          ∃ w : PauliSoundnessWitness P S,
            w.completedWithin (P.qldError a b ε) := by
  obtain ⟨a, b, ha, hb, hb1, hproj⟩ := exists_projective_setting_isometry_bounds
  have haa : a ≤ 21 * a ^ 2 := by nlinarith
  refine ⟨21 * a ^ 2, b, by nlinarith, hb, hb1, ?_⟩
  intro P ε hε0 hε1 S hwin
  have hprojective := hproj P ε hε0 hε1 (pauliNaimarkSetting P ε S hwin)
  simp only [pauliNaimarkSetting] at hprojective
  obtain ⟨t, hstate, hA, hB⟩ := hprojective
  have hmono : P.qldError a b ε ≤
      P.qldError (21 * a ^ 2) b ε :=
    deltaQld_mono ha haa le_rfl hb hε0 hε1
  let d := P.qldError a b ε
  let r := ‖isometryTensor t.φA t.φB (pauliNaimarkStrategy P S).ψ - idealState P t.aux‖
  have hsq : r ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hstate 2
  have habsorb := three_add_six_sq_deltaQld_le (P := P) ha hb hε0 hε1
  have transfer {x y : ℝ} (h : x ≤ 3 * y + 6 * r ^ 2) (hy : y ≤ d) :
      x ≤ P.qldError (21 * a ^ 2) b ε :=
    (show x ≤ 3 * d + 6 * d ^ 2 by linarith).trans habsorb
  exact ⟨pauliNaimarkWitness P S t, by
      rw [pauli_naimark_witness_state_distance_eq]; exact hstate.trans hmono,
    fun W => transfer (pauli_naimark_operator_distanceA_le P S t W) (hA W),
    fun W => transfer (pauli_naimark_operator_distanceB_le P S t W) (hB W)⟩

end

end MIPStarRE.QPBT
