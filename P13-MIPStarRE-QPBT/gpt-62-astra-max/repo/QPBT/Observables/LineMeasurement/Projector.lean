module

public import QPBT.Observables.ExpandedPlacement
public import QPBT.Observables.LineMeasurement.Restriction

/-!
# Pauli-register line projectors

This module constructs the projective measurement `tau^{W,line}` of one
generalized-Pauli register whose outcome is the restriction to a canonical
line of the low-degree encoding of the measured basis label. It records that
the outcome projectors are orthogonal projections summing to the identity,
that they are symmetric matrices (so that they act identically on either half
of an EPR pair), and that on an axis-parallel line they vanish outside the
embedded degree-`d` subspace.

## References

The projectors are `tau^{W,line}_{f''}` of `def:expanded-line-measurement`,
with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:552-556`. Their
perfect self-consistency on an EPR pair is the ancillary input to item 1 of
`lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:527-532`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

section

variable (P : AdmissibleParams) (W : PauliKind) (line : LineDesc P.toLdParams)
  (f : PauliLinePoly P)

variable {P} in
/-- The Pauli-register projector onto labels whose low-degree encoding
restricts to `f` on `line`. This is `tau^{W,line}_f` in the proof of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`, blueprint
`def:expanded-line-measurement`. -/
noncomputable def tauLineProj :
    Op (PauliRegister P) :=
  ∑ h ∈ Finset.univ.filter (fun h : PauliRegister P =>
      restrictToLine line (lowDegreeEncoding h) = f),
    pauliProj W h

/-- Pauli line projectors are positive semidefinite. This is the positivity of
the ancillary measurement in `def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`. -/
theorem tauLineProj_nonneg :
    0 ≤ tauLineProj W line f := by
  classical
  exact Finset.sum_nonneg fun e _ => (posSemidef_pauliProj W e).nonneg

/-- The line coarse-graining of the generalized Pauli projectors is a
symmetric matrix. Symmetry is what makes the projector act identically on
either half of an EPR pair, and hence is the hypothesis behind the perfect
ancilla consistency used in `enu:qld-comm-line-self-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:527-532`. -/
theorem tauLineProj_transpose :
    (tauLineProj W line f)ᵀ = tauLineProj W line f := by
  classical
  simp only [tauLineProj, Matrix.transpose_sum, pauliProj_transpose]

end

/-- Pauli line projectors belonging to distinct line polynomials are
orthogonal, while each projector is idempotent. This is the ancillary product
calculation in `def:expanded-line-measurement` and item 1 of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-558`. -/
theorem tauLineProj_mul_tauLineProj (P : AdmissibleParams) (W : PauliKind)
    (line : LineDesc P.toLdParams) (f g : PauliLinePoly P) :
    tauLineProj W line f * tauLineProj W line g =
      if f = g then tauLineProj W line f else 0 := by
  classical
  unfold tauLineProj
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  by_cases hfg : f = g
  · subst g
    simp
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.sum_eq_single]
    · rw [pauliProj_mul_pauliProj, if_pos rfl]
    · intro e' he' hee'
      rw [pauliProj_mul_pauliProj, if_neg hee'.symm]
    · exact fun h => (h he).elim
  · rw [if_neg hfg]
    apply Finset.sum_eq_zero
    intro e he
    apply Finset.sum_eq_zero
    intro e' he'
    rw [pauliProj_mul_pauliProj, if_neg]
    intro hee'
    apply hfg
    simp_all

/-- The line fibers partition the complete family of Pauli eigenspace
projectors. This is the completeness of the ancillary measurement in
`def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`. -/
theorem sum_tauLineProj_eq_one (P : AdmissibleParams) (W : PauliKind)
    (line : LineDesc P.toLdParams) :
    ∑ f, tauLineProj W line f = 1 := by
  classical
  rw [show (∑ f, tauLineProj W line f) =
      _ by
    apply Finset.sum_fiberwise]
  exact sum_pauliProj_eq_one W

/-- On an axis-parallel line, Pauli line projectors vanish outside the
embedded degree-`d` subspace, because every restricted low-degree encoding has
degree at most `d` there. This is the ancillary half of the last assertion of
`def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`. -/
theorem tauLineProj_eq_zero_of_axis (P : AdmissibleParams) (W : PauliKind)
    (line : LineDesc P.toLdParams) (haxis : line.kind = .axis)
    (f : PauliLinePoly P) (hf : ¬ f.FitsDegree P.d) :
    tauLineProj W line f = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro e he
  exfalso
  apply hf
  rw [← (Finset.mem_filter.mp he).2]
  intro i hi
  unfold restrictToLine
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  calc
    _ ≤ 1 :=
      polynomialOnLine_lowDegreeEncoding_natDegree_le_one_of_axis P.toLdParams line haxis e
    _ ≤ P.toLdParams.d := P.toLdParams.hd
    _ < i.val := hi

/-! ## Interaction with the point projectors -/

/-- On a point of the line, Pauli line projectors of non-evaluating
polynomials vanish: every restricted low-degree encoding evaluates there.
Formalization-only auxiliary for items 2 and 3 of `lem:qld-comm-line-cons`,
paper `14_analysis_of_the_pauli_basis_test.tex:534-545`. -/
theorem tauLineProj_eq_zero_of_evalOpt_none (P : AdmissibleParams)
    (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : PauliPoint P) (hu : u ∈ line.pointSet)
    (f : PauliLinePoly P) (hf : evalOpt line u f = none) :
    tauLineProj W line f = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro e he
  exfalso
  have hev := evalOpt_restrictToLine_lowDegreeEncoding line e hu
  rw [(Finset.mem_filter.mp he).2] at hev
  have hev' := hev
  rw [hf] at hev'
  exact absurd hev' (by simp)

/-- A Pauli line projector followed by a Pauli point projector at a point of
the line is the line projector when the line polynomial evaluates to the
point value, and zero otherwise. This is the exact consistency
`tau^{W,line}_{f''}` versus `tau^{W,u}_{f''(u)}` in items 2 and 3 of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:534-545`. -/
theorem tauLineProj_mul_tauPointProj {P : AdmissibleParams} (W : PauliKind)
    {line : LineDesc P.toLdParams} {u : PauliPoint P}
    (hu : u ∈ line.pointSet) (f : PauliLinePoly P)
    (b : PauliScalar P) :
    tauLineProj W line f * ProjectiveSetting.tauPointProj W u b =
      if evalOpt line u f = some b then tauLineProj W line f else 0 := by
  classical
  unfold tauLineProj ProjectiveSetting.tauPointProj
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, pauliProj_mul_pauliProj]
  calc
    _ =
      ∑ e ∈ Finset.univ.filter (fun e : PauliRegister P =>
        restrictToLine line (lowDegreeEncoding e) = f),
        if evalOpt line u f = some b then pauliProj W e else 0 := by
      refine Finset.sum_congr rfl fun e he => ?_
      rw [Finset.sum_ite_eq]
      have hev := evalOpt_restrictToLine_lowDegreeEncoding line e hu
      rw [(Finset.mem_filter.mp he).2] at hev
      have hev' := hev
      by_cases hb : evalOpt line u f = some b
      · rw [if_pos hb, if_pos]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Option.some.inj (hev'.symm.trans hb))⟩
      · rw [if_neg hb, if_neg]
        intro hmem
        apply hb
        exact hev'.trans (congrArg some (Finset.mem_filter.mp hmem).2)
    _ = _ := by
      split_ifs <;> simp

/-- Pauli line and point projectors commute. -/
theorem tauPointProj_mul_tauLineProj (P : AdmissibleParams) (W : PauliKind)
    (line : LineDesc P.toLdParams) (u : PauliPoint P)
    (f : PauliLinePoly P) (b : PauliScalar P) :
    ProjectiveSetting.tauPointProj W u b * tauLineProj W line f =
      tauLineProj W line f * ProjectiveSetting.tauPointProj W u b := by
  classical
  unfold tauLineProj ProjectiveSetting.tauPointProj
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => ?_
  simp [pauliProj_mul_pauliProj]
  by_cases h : e = e'
  · subst h
    simp
  · rw [if_neg (Ne.symm h), if_neg h]

/-- The EPR quadratic form of a line projector on one half and a point
projector on the other half is the EPR quadratic form of the line projector
alone when the line polynomial evaluates to the point value, and zero
otherwise. This is the exact ancillary consistency in items 2 and 3 of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:534-545`. -/
theorem stateQForm_eprState_tauLineProj_tauPointProj (P : AdmissibleParams)
    (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : PauliPoint P) (hu : u ∈ line.pointSet)
    (f : PauliLinePoly P) (b : PauliScalar P) :
    DistanceCalculus.stateQForm (eprState (PauliRegister P))
        (heteroKron (tauLineProj W line f)
          (ProjectiveSetting.tauPointProj W u b)) =
      if evalOpt line u f = some b then
        DistanceCalculus.stateQForm (eprState (PauliRegister P))
          (heteroKron (tauLineProj W line f) (1 : Op (PauliRegister P)))
      else 0 := by
  have h : DistanceCalculus.stateQForm (eprState (PauliRegister P))
      (heteroKron (tauLineProj W line f)
        (ProjectiveSetting.tauPointProj W u b)) =
      DistanceCalculus.stateQForm (eprState (PauliRegister P))
        (heteroKron (tauLineProj W line f *
          ProjectiveSetting.tauPointProj W u b) 1) := by
    unfold DistanceCalculus.stateQForm
    congr 2
    ext p
    simpa [applyOperatorToState] using
      congrFun ((by
                  let T := tauLineProj W line f
                  let T' := ProjectiveSetting.tauPointProj W u b
                  have hfactor : heteroKron T T' = heteroKron T 1 * heteroKron 1 T' := by
                    simp [heteroKron_mul]
                  rw [hfactor, ← Matrix.mulVec_mulVec,
                    ← epr_action_eq_of_transpose
                      (ProjectiveSetting.tauPointProj_transpose W u b),
                    Matrix.mulVec_mulVec, heteroKron_mul, Matrix.mul_one])) p
  rw [h, tauLineProj_mul_tauPointProj W hu f b]
  split_ifs
  · rfl
  · simp [DistanceCalculus.stateQForm, applyOperatorToState, heteroKron]

/-- The EPR overlap of a point projector on the first factor with a line
projector on the second vanishes unless the line polynomial evaluates at the
point to the measured value, and otherwise equals the overlap of the line
projector alone. This is the interchanged form of
`stateQForm_eprState_tauLineProj_tauPointProj`, supporting
`def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:527-532`. -/
theorem stateQForm_eprState_tauPointProj_tauLineProj (P : AdmissibleParams)
    (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : PauliPoint P) (hu : u ∈ line.pointSet)
    (f : PauliLinePoly P) (b : PauliScalar P) :
    DistanceCalculus.stateQForm (eprState (PauliRegister P))
        (heteroKron (ProjectiveSetting.tauPointProj W u b)
          (tauLineProj W line f)) =
      if evalOpt line u f = some b then
        DistanceCalculus.stateQForm (eprState (PauliRegister P))
          (heteroKron (tauLineProj W line f) (1 : Op (PauliRegister P)))
      else 0 := by
  have h : DistanceCalculus.stateQForm (eprState (PauliRegister P))
      (heteroKron (ProjectiveSetting.tauPointProj W u b)
        (tauLineProj W line f)) =
      DistanceCalculus.stateQForm (eprState (PauliRegister P))
        (heteroKron (tauLineProj W line f *
          ProjectiveSetting.tauPointProj W u b) 1) := by
    unfold DistanceCalculus.stateQForm
    congr 2
    ext p
    simpa [applyOperatorToState] using
      congrFun ((by
                  let T := tauLineProj W line f
                  let T' := ProjectiveSetting.tauPointProj W u b
                  have hfactor : heteroKron T' T = heteroKron T' 1 * heteroKron 1 T := by
                    simp [heteroKron_mul]
                  rw [hfactor, ← Matrix.mulVec_mulVec,
                    ← epr_action_eq_of_transpose (tauLineProj_transpose P W line f),
                    Matrix.mulVec_mulVec, heteroKron_mul, Matrix.mul_one,
                    tauPointProj_mul_tauLineProj])) p
  rw [h, tauLineProj_mul_tauPointProj W hu f b]
  split_ifs
  · rfl
  · simp [DistanceCalculus.stateQForm, applyOperatorToState, heteroKron]

/-! ## Perfect consistency on an EPR pair -/

/-- The EPR quadratic forms of the Pauli line projectors on one half sum to
one. Formalization-only auxiliary for the ancillary overlaps in
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:527-545`. -/
theorem sum_stateQForm_eprState_tauLineProj_one (P : AdmissibleParams)
    (W : PauliKind) (line : LineDesc P.toLdParams) :
    ∑ f : PauliLinePoly P,
        DistanceCalculus.stateQForm (eprState (PauliRegister P))
          (heteroKron (tauLineProj W line f) (1 : Op (PauliRegister P))) = 1 := by
  rw [← DistanceCalculus.stateQForm_finset_sum,
    ← DistanceCalculus.heteroKron_finset_sum_left,
    sum_tauLineProj_eq_one, heteroKron_one_one,
    DistanceCalculus.stateQForm_one, eprState_norm]
  norm_num

end

end MIPStarRE.QPBT
