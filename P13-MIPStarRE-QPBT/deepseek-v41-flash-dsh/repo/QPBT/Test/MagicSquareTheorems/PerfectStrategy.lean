module

public import QPBT.Test.MagicSquareTheorems.PerfectStrategy.Measurements

/-!
# Perfect strategies for the Magic Square game

This file completes the construction of `thm:ms-from-ac`.  It identifies the
question pairs in the support of the Magic Square distribution, shows that the
measurement family commutes there and annihilates rejected answer pairs on the
EPR state, evaluates the Born weights of the accepted answers, and assembles a
symmetric SPCC strategy of value one from an anticommuting consistent pair of
binary measurements.

## References

The source statement is blueprint
`thm:ms-from-ac`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:654-722`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section
variable (i : Fin 6)


private theorem msConstraintVars_injective  :
    Function.Injective (msConstraintVars i) := by
  intro k l h
  fin_cases i <;> fin_cases k <;> fin_cases l <;>
    simp [msConstraintVars] at h ⊢

private theorem msConstraintVars_exists_iff  (k : Fin 3) (β : Fin 3 → ZMod 2) (b : ZMod 2) :
    (∃ l : Fin 3, msConstraintVars i l = msConstraintVars i k ∧ β l = b) ↔
      β k = b := by
  constructor
  · rintro ⟨l, hl, hlb⟩
    rwa [msConstraintVars_injective i hl] at hlb
  · intro h
    exact ⟨k, rfl, h⟩
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (P : Fin 9 → Measurement (ZMod 2) V) (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j)) (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))



/-- Formalization-only auxiliary for the perfect Magic Square strategy and the
proof of `lem:pauli-completeness`: a constraint effect commutes with each
incident variable effect in the measurement family built from commuting
projective cell measurements. -/
theorem msStrategyMeasurement_incident_commute 
    (i : Fin 6) (k : Fin 3) (a b : MsAnswer) :
    Commute ((msStrategyMeasurement P hP hcomm (.constraint i)).effect a)
      ((msStrategyMeasurement P hP hcomm
        (.var (msConstraintVars i k))).effect b) := by
  by_cases ha : a ∈ Set.range (fun ab => MsAnswer.triple (parityTriple i ab))
  · rcases ha with ⟨ab, rfl⟩
    rw [msStrategyMeasurement_constraint_triple]
    by_cases hb : b ∈ Set.range (MsAnswer.bit : ZMod 2 → MsAnswer)
    · rcases hb with ⟨c, rfl⟩
      rw [msStrategyMeasurement_var_bit]
      change Commute
        ((P (msConstraintVars i 0)).effect ab.1 *
          (P (msConstraintVars i 1)).effect ab.2)
        ((P (msConstraintVars i k)).effect c)
      exact (hcomm i 0 k ab.1 c).mul_left (hcomm i 1 k ab.2 c)
    · rw [msStrategyMeasurement_var_zero _ _ _ _ hb]
      exact Commute.zero_right _
  · rw [msStrategyMeasurement_constraint_zero _ _ _ _ ha]
    exact Commute.zero_left _

private theorem msStrategyMeasurement_rejected_mul 
    (hmul : ∀ i k ab b,
      (msConstraintJoint P hP hcomm i).effect ab *
          (P (msConstraintVars i k)).effect b =
        if parityTriple i ab k = b then
          (msConstraintJoint P hP hcomm i).effect ab else 0)
    (i : Fin 6) (k : Fin 3) (a b : MsAnswer)
    (hrej : msWinPredicate (.constraint i) (.var (msConstraintVars i k)) a b = false) :
    ((msStrategyMeasurement P hP hcomm (.constraint i)).effect a) *
      ((msStrategyMeasurement P hP hcomm
        (.var (msConstraintVars i k))).effect b) = 0 := by
  by_cases ha : a ∈ Set.range (fun ab => MsAnswer.triple (parityTriple i ab))
  · rcases ha with ⟨ab, rfl⟩
    rw [msStrategyMeasurement_constraint_triple]
    by_cases hb : b ∈ Set.range (MsAnswer.bit : ZMod 2 → MsAnswer)
    · rcases hb with ⟨c, rfl⟩
      rw [msStrategyMeasurement_var_bit]
      have hne : parityTriple i ab k ≠ c := by
        simpa [msWinPredicate, parityTriple_sum,
          msConstraintVars_exists_iff] using hrej
      rw [hmul i k ab c]
      simp [hne]
    · rw [msStrategyMeasurement_var_zero _ _ _ _ hb]
      simp
  · rw [msStrategyMeasurement_constraint_zero _ _ _ _ ha]
    simp

private theorem msStrategyMeasurement_rejected_mul_reverse 
    (hmul : ∀ i k ab b,
      (msConstraintJoint P hP hcomm i).effect ab *
          (P (msConstraintVars i k)).effect b =
        if parityTriple i ab k = b then
          (msConstraintJoint P hP hcomm i).effect ab else 0)
    (i : Fin 6) (k : Fin 3) (a b : MsAnswer)
    (hrej : msWinPredicate (.var (msConstraintVars i k)) (.constraint i) a b = false) :
    ((msStrategyMeasurement P hP hcomm
        (.var (msConstraintVars i k))).effect a) *
      ((msStrategyMeasurement P hP hcomm (.constraint i)).effect b) = 0 := by
  rw [(msStrategyMeasurement_incident_commute P hP hcomm i k b a).symm.eq]
  exact msStrategyMeasurement_rejected_mul P hP hcomm hmul i k b a
    (by simpa [msWinPredicate_symm] using hrej)

/-- Formalization-only auxiliary for the perfect Magic Square strategy and the
proof of `lem:pauli-completeness`: every supported Magic Square question
pair is an incident constraint-variable pair in one of its two orders. -/
theorem msGame_support_incidence (x y : MsType)
    (hxy : (x, y) ∈ msGameSymm.μ.support) :
    (∃ i : Fin 6, ∃ k : Fin 3,
      x = .constraint i ∧ y = .var (msConstraintVars i k)) ∨
      ∃ i : Fin 6, ∃ k : Fin 3,
        x = .var (msConstraintVars i k) ∧ y = .constraint i := by
  change (x, y) ∈
    Finset.univ.filter (fun ab : MsType × MsType =>
      Sym2.mk ab.1 ab.2 ∈ msEdges) at hxy
  have hedge : Sym2.mk x y ∈ msEdges := (Finset.mem_filter.mp hxy).2
  rw [msEdges] at hedge
  rcases Finset.mem_image.mp hedge with ⟨⟨i, k⟩, _, hik⟩
  rcases Sym2.eq_iff.mp hik with hik | hik
  · left
    exact ⟨i, k, hik.1.symm, hik.2.symm⟩
  · right
    exact ⟨i, k, hik.2.symm, hik.1.symm⟩

/-- Formalization-only auxiliary for the perfect Magic Square strategy and the
proof of `lem:pauli-completeness`: the constructed Magic Square family has
zero operator product on rejected answers in its support, from the stated cell
and joint-measurement identities. -/
theorem msStrategyMeasurement_rejected_mul_on_support 
    (hmul : ∀ i k ab b,
      (msConstraintJoint P hP hcomm i).effect ab *
          (P (msConstraintVars i k)).effect b =
        if parityTriple i ab k = b then
          (msConstraintJoint P hP hcomm i).effect ab else 0)
    (x y : MsType) (hxy : (x, y) ∈ msGameSymm.μ.support)
    (a b : MsAnswer) (hrej : msWinPredicate x y a b = false) :
    ((msStrategyMeasurement P hP hcomm x).effect a) *
      ((msStrategyMeasurement P hP hcomm y).effect b) = 0 := by
  rcases msGame_support_incidence x y hxy with hxy | hxy
  · rcases hxy with ⟨i, k, rfl, rfl⟩
    exact msStrategyMeasurement_rejected_mul P hP hcomm hmul i k a b hrej
  · rcases hxy with ⟨i, k, rfl, rfl⟩
    exact msStrategyMeasurement_rejected_mul_reverse P hP hcomm hmul i k a b hrej

/-- Formalization-only auxiliary for the perfect Magic Square strategy and the
proof of `lem:pauli-completeness`: the constructed Magic Square family has
symmetric effects when its underlying projective cell measurements have
symmetric effects. -/
theorem msStrategyMeasurement_effect_transpose 
    (hPt : ∀ j b, ((P j).effect b)ᵀ = (P j).effect b)
    (x : MsType) (a : MsAnswer) :
    ((msStrategyMeasurement P hP hcomm x).effect a)ᵀ =
      (msStrategyMeasurement P hP hcomm x).effect a := by
  cases x with
  | var j =>
      exact postprocess_effect_transpose (P j) MsAnswer.bit (hPt j) a
  | constraint i =>
      exact postprocess_effect_transpose (msConstraintJoint P hP hcomm i)
        (fun ab => .triple (parityTriple i ab))
        (msConstraintJoint_effect_transpose P hP hcomm hPt i) a

/-- Formalization-only auxiliary for the perfect Magic Square strategy and the
proof of `lem:pauli-completeness`: local effects with zero product
annihilate the maximally entangled vector after tensor placement, provided the
second effect is symmetric. -/
theorem heteroKron_mulVec_epr_eq_zero_of_mul_eq_zero  [Nonempty V]
    (E F : Op V) (hFt : Fᵀ = F) (hEF : E * F = 0) :
    (heteroKron E F).mulVec (eprState V) = 0 := by
  have hfactor : heteroKron E F =
      heteroKron E 1 * heteroKron 1 F := by
    rw [heteroKron_mul]
    simp
  rw [hfactor, ← Matrix.mulVec_mulVec,
    ← epr_action_eq_of_transpose F hFt, Matrix.mulVec_mulVec,
    heteroKron_mul, hEF]
  have hz : heteroKron (0 : Op V) (1 : Op V) = 0 := by
    ext ⟨i, k⟩ ⟨j, l⟩
    simp [heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply]
  simp [mul_one]
  rw [hz]
  exact Matrix.zero_mulVec _

end

end MIPStarRE.QPBT
