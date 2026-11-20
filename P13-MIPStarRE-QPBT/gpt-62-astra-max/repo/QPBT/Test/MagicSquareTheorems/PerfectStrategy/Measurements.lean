module

public import QPBT.Test.MagicSquareTheorems.PerfectStrategy.Observables

/-!
# Measurements of the perfect Magic Square strategy

This module turns the operator table of `thm:ms-from-ac` into a measurement
family.  It forms the joint measurement of two commuting binary projective
measurements, records the post-processing identities for injective
relabellings, encodes a constraint answer as the parity triple determined by
two freely chosen bits, and assembles the nine cell measurements into the
Magic Square measurement family, closing with the multiplication rule relating
a constraint outcome to the outcomes of its incident variables.

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

section

variable {V : Type*} [Fintype V] [DecidableEq V] (M N : Measurement (ZMod 2) V)
  (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
  (hN : MIPStarRE.QPBT.Measurement.IsProjective N)
  (hcomm : ∀ a b, Commute (M.effect a) (N.effect b))

/-- The joint measurement of two commuting binary projective measurements. -/
noncomputable def binaryJointMeasurement :
    Measurement (ZMod 2 × ZMod 2) V :=
  Measurement.ofSumEqOne
    (fun ab => M.effect ab.1 * N.effect ab.2)
    (fun ab => (hM ab.1).mul (hN ab.2) (hcomm ab.1 ab.2) |>.nonneg)
    (by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [N.sum_eq_one]
      simp [M.sum_eq_one])

private theorem binaryJointMeasurement_mul_first
    (ab : ZMod 2 × ZMod 2) (b : ZMod 2) :
    (binaryJointMeasurement M N hM hN hcomm).effect ab * M.effect b =
      if ab.1 = b then
        (binaryJointMeasurement M N hM hN hcomm).effect ab else 0 := by
  change (M.effect ab.1 * N.effect ab.2) * M.effect b =
    if ab.1 = b then M.effect ab.1 * N.effect ab.2 else 0
  calc
    _ =
        _ := mul_assoc _ _ _
    _ = M.effect ab.1 * (M.effect b * N.effect ab.2) := by
      rw [(hcomm b ab.2).symm.eq]
    _ = _ :=
      (mul_assoc _ _ _).symm
    _ = _ := by
      simp_all [binary_effect_mul]

end

section

variable {α β V : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Fintype V]
  [DecidableEq V] (M : Measurement α V)

private theorem postprocess_effect_of_injective {f : α → β} (hf : Function.Injective f) (a : α) :
    (M.postprocess f).effect (f a) = M.effect a := by
  simp only [Measurement.postprocess_effect, Finset.sum_filter]
  rw [Fintype.sum_eq_single a]
  · simp
  · intro b hba
    have hfb : f b ≠ f a := fun h => hba (hf h)
    simp [hfb]

/-- Relabeling a measurement gives zero effect to outcomes outside the image. -/
theorem postprocess_effect_eq_zero_of_notMem (f : α → β) {b : β}
    (hb : b ∉ Set.range f) :
    (M.postprocess f).effect b = 0 := by
  apply Finset.sum_eq_zero
  aesop

private theorem postprocess_projective_of_injective (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f : α → β) (hf : Function.Injective f) :
    MIPStarRE.QPBT.Measurement.IsProjective (M.postprocess f) := by
  intro b
  by_cases hb : b ∈ Set.range f
  · rcases hb with ⟨a, rfl⟩
    rw [postprocess_effect_of_injective M hf a]
    exact hM a
  · rw [postprocess_effect_eq_zero_of_notMem M f hb]
    exact IsStarProjection.zero _

end

section

variable (i : Fin 6)

/-- Encode two freely chosen bits as the unique triple of the prescribed parity. -/
def parityTriple (ab : ZMod 2 × ZMod 2) : Fin 3 → ZMod 2 :=
  ![ab.1, ab.2, msParity i - ab.1 - ab.2]

private theorem parityTriple_injective :
    Function.Injective (parityTriple i) := by
  intro ab cd h
  apply Prod.ext
  · exact congrFun h 0
  · exact congrFun h 1

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): the triple encoding two freely chosen bits sums
to the parity `msParity i` prescribed by the constraint. -/
theorem parityTriple_sum (ab : ZMod 2 × ZMod 2) :
    ∑ k : Fin 3, parityTriple i ab k = msParity i := by
  rw [Fin.sum_univ_three]
  simp [parityTriple]
  ring

end

private theorem bit_embedding_injective :
    Function.Injective (MsAnswer.bit : ZMod 2 → MsAnswer) := by
  solve_by_elim [MsAnswer.bit.inj]

private theorem triple_embedding_injective (i : Fin 6) :
    Function.Injective (fun ab => MsAnswer.triple (parityTriple i ab)) := by
  intro ab cd h
  apply parityTriple_injective i
  exact MsAnswer.triple.inj h

section

variable {V : Type*} [Fintype V] [DecidableEq V]

section

variable (OA OB : Op V) (hOA : OAᴴ = OA) (hOB : OBᴴ = OB) (hOA_sq : OA * OA = 1)
  (hOB_sq : OB * OB = 1) (hac : OA * OB = -(OB * OA)) (j : Fin 9)

/-- The binary measurement associated with a cell of the operator table. -/
noncomputable def msCellMeasurement :
    Measurement (ZMod 2) (V × ZMod 2) :=
  reflectionMeasurement (msCellObservable OA OB j)
    (msCellObservable_conjTranspose OA OB hOA hOB hac j)
    (msCellObservable_sq OA OB hOA_sq hOB_sq hac j)

@[simp]
private theorem msCellMeasurement_effect (b : ZMod 2) :
    (msCellMeasurement OA OB hOA hOB hOA_sq hOB_sq hac j).effect b =
      reflectionEffect (msCellObservable OA OB j) b :=
  rfl

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): each of the nine cell measurements of the Magic
Square strategy is projective. -/
theorem msCellMeasurement_projective :
    MIPStarRE.QPBT.Measurement.IsProjective
      (msCellMeasurement OA OB hOA hOB hOA_sq hOB_sq hac j) :=
  reflectionMeasurement_projective _
    _
    _

end

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): every effect of a cell measurement is symmetric
whenever `OA` and `OB` are symmetric. -/
theorem msCellMeasurement_transpose
    (OA OB : Op V) (hOA : OAᴴ = OA) (hOB : OBᴴ = OB)
    (hOA_sq : OA * OA = 1) (hOB_sq : OB * OB = 1)
    (hOA_t : OAᵀ = OA) (hOB_t : OBᵀ = OB)
    (hac : OA * OB = -(OB * OA)) (j : Fin 9) (b : ZMod 2) :
    ((msCellMeasurement OA OB hOA hOB hOA_sq hOB_sq hac j).effect b)ᵀ =
      (msCellMeasurement OA OB hOA hOB hOA_sq hOB_sq hac j).effect b := by
  rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
    simp [reflectionEffect, Matrix.transpose_add, Matrix.transpose_sub, (msCellObservable_transpose OA OB hOA_t hOB_t hac j)]

section

variable (P : Fin 9 → Measurement (ZMod 2) V)
  (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
  (hcomm : ∀ i k l a b, Commute ((P (msConstraintVars i k)).effect a) ((P (msConstraintVars i l)).effect b))

/-- The joint measurement of the first two cells in a Magic Square constraint. -/
noncomputable def msConstraintJoint
    (i : Fin 6) : Measurement (ZMod 2 × ZMod 2) V :=
  binaryJointMeasurement (P (msConstraintVars i 0))
    (P (msConstraintVars i 1)) (hP _) (hP _) (hcomm i 0 1)

/-- The global Magic Square measurement family induced by the nine cell measurements. -/
noncomputable def msStrategyMeasurement :
    MsType → Measurement MsAnswer V
  | .var j => (P j).postprocess MsAnswer.bit
  | .constraint i =>
      (msConstraintJoint P hP hcomm i).postprocess
        (fun ab => .triple (parityTriple i ab))

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): on a variable question the global measurement
family reproduces the corresponding cell measurement: its effect at the answer
`bit b` is the effect of `P j` at `b`. -/
theorem msStrategyMeasurement_var_bit
    (j : Fin 9) (b : ZMod 2) :
    (msStrategyMeasurement P hP hcomm (.var j)).effect (.bit b) =
      (P j).effect b := postprocess_effect_of_injective _
    bit_embedding_injective b

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): on a variable question the global measurement
family assigns the zero effect to every answer outside the range of
`MsAnswer.bit`. -/
theorem msStrategyMeasurement_var_zero
    (j : Fin 9) {a : MsAnswer}
    (ha : a ∉ Set.range (MsAnswer.bit : ZMod 2 → MsAnswer)) :
    (msStrategyMeasurement P hP hcomm (.var j)).effect a = 0 := postprocess_effect_eq_zero_of_notMem (P j) MsAnswer.bit ha

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): on a constraint question the effect at the answer
triple encoding the bits `ab` equals the effect at `ab` of the joint measurement
of the first two cells of that constraint. -/
theorem msStrategyMeasurement_constraint_triple
    (i : Fin 6) (ab : ZMod 2 × ZMod 2) :
    (msStrategyMeasurement P hP hcomm (.constraint i)).effect
        (.triple (parityTriple i ab)) =
      (msConstraintJoint P hP hcomm i).effect ab := postprocess_effect_of_injective _
    (triple_embedding_injective i) ab

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): on a constraint question the global measurement
family assigns the zero effect to every answer that is not a parity triple of
the constraint. -/
theorem msStrategyMeasurement_constraint_zero
    (i : Fin 6) {a : MsAnswer}
    (ha : a ∉ Set.range (fun ab => MsAnswer.triple (parityTriple i ab))) :
    (msStrategyMeasurement P hP hcomm (.constraint i)).effect a = 0 := postprocess_effect_eq_zero_of_notMem _
    _ ha

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): the global Magic Square measurement family is
projective at every question. -/
theorem msStrategyMeasurement_projective
    (x : MsType) :
    MIPStarRE.QPBT.Measurement.IsProjective
      (msStrategyMeasurement P hP hcomm x) := by
  cases x with
  | var j =>
      exact postprocess_projective_of_injective _ (hP j)
        MsAnswer.bit bit_embedding_injective
  | constraint i =>
      apply postprocess_projective_of_injective
      · exact fun ab => ((hP _) ab.1).mul ((hP _) ab.2) ((hcomm i 0 1) ab.1 ab.2)
      · exact triple_embedding_injective i

end

end

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): post-processing a measurement along a relabelling
of outcomes preserves symmetry of its effects. -/
theorem postprocess_effect_transpose
    {α β V : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Fintype V] [DecidableEq V]
    (M : Measurement α V) (f : α → β)
    (hM : ∀ a, (M.effect a)ᵀ = M.effect a) (b : β) :
    ((M.postprocess f).effect b)ᵀ = (M.postprocess f).effect b := by
  rw [Measurement.postprocess_effect]
  ext r c
  simp [Matrix.sum_apply]
  congr 1 with a
  exact congrFun (congrFun (hM a) r) c

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): the effects of the joint measurement of the first
two cells of a constraint are symmetric whenever the underlying cell effects
are. -/
theorem msConstraintJoint_effect_transpose
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))
    (hPt : ∀ j b, ((P j).effect b)ᵀ = (P j).effect b)
    (i : Fin 6) (ab : ZMod 2 × ZMod 2) :
    ((msConstraintJoint P hP hcomm i).effect ab)ᵀ =
      (msConstraintJoint P hP hcomm i).effect ab := by
  change ((_ *
    (P (msConstraintVars i 1)).effect ab.2)ᵀ) = _
  simp_all
  exact (hcomm i 0 1 ab.1 ab.2).symm.eq

private theorem msConstraintObservable_product_parity
    {OA OB : Op V} (hOA : OA * OA = 1) (hOB : OB * OB = 1)
    (hac : OA * OB = -(OB * OA)) (i : Fin 6) :
    (msParity i = 0 ∧
      msCellObservable OA OB (msConstraintVars i 0) *
          msCellObservable OA OB (msConstraintVars i 1) *
          msCellObservable OA OB (msConstraintVars i 2) = 1) ∨
    (msParity i = 1 ∧
      msCellObservable OA OB (msConstraintVars i 0) *
          msCellObservable OA OB (msConstraintVars i 1) *
          msCellObservable OA OB (msConstraintVars i 2) = -1) := by
  have hprod := msConstraintObservable_product OA OB hOA hOB hac i
  fin_cases i <;> simpa [msParity] using hprod

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): multiplying a constraint effect at `ab` by the
effect of an incident cell measurement at `b` returns the constraint effect when
`b` is the bit that the parity triple assigns to that cell, and `0` otherwise;
this is the consistency of the constraint answer with its variable answers. -/
theorem msCellConstraintJoint_mul
    (OA OB : Op V) (hOA : OAᴴ = OA) (hOB : OBᴴ = OB)
    (hOA_sq : OA * OA = 1) (hOB_sq : OB * OB = 1)
    (hac : OA * OB = -(OB * OA))
    (i : Fin 6) (k : Fin 3) (ab : ZMod 2 × ZMod 2) (b : ZMod 2) :
    let P := msCellMeasurement OA OB hOA hOB hOA_sq hOB_sq hac
    (msConstraintJoint P
        (msCellMeasurement_projective OA OB hOA hOB hOA_sq hOB_sq hac)
        (fun i k l a b => reflectionEffect_commute
          (msConstraintObservable_commute OA OB hOA_sq hOB_sq hac i k l) a b)
        i).effect ab * (P (msConstraintVars i k)).effect b =
      if parityTriple i ab k = b then
        (msConstraintJoint P
          (msCellMeasurement_projective OA OB hOA hOB hOA_sq hOB_sq hac)
          (fun i k l a b => reflectionEffect_commute
            (msConstraintObservable_commute OA OB hOA_sq hOB_sq hac i k l) a b)
          i).effect ab else 0 := by
  let P := msCellMeasurement OA OB hOA hOB hOA_sq hOB_sq hac
  let hP := msCellMeasurement_projective OA OB hOA hOB hOA_sq hOB_sq hac
  let hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b) :=
    fun i k l => reflectionEffect_commute
    (msConstraintObservable_commute OA OB hOA_sq hOB_sq hac i k l)
  fin_cases k
  · apply binaryJointMeasurement_mul_first
  · change ((P (msConstraintVars i 0)).effect ab.1 * (P (msConstraintVars i 1)).effect ab.2) * (P (msConstraintVars i 1)).effect b =
      if ab.2 = b then (P (msConstraintVars i 0)).effect ab.1 * (P (msConstraintVars i 1)).effect ab.2 else 0
    rw [mul_assoc, binary_effect_mul (P (msConstraintVars i 1)) (hP _)]
    by_cases h : ab.2 = b
    · simp [if_pos]
    · simp [if_neg h]
  let obs := msCellObservable OA OB (msConstraintVars i 1)
  · change
      (reflectionEffect (msCellObservable OA OB (msConstraintVars i 0)) ab.1 *
          reflectionEffect obs ab.2) *
          reflectionEffect (msCellObservable OA OB (msConstraintVars i 2)) b =
        if msParity i - ab.1 - ab.2 = b then
          reflectionEffect (msCellObservable OA OB (msConstraintVars i 0)) ab.1 *
            reflectionEffect obs ab.2
        else 0
    by_cases hb : msParity i - ab.1 - ab.2 = b
    · rw [if_pos hb]
      subst b
      exact reflection_pair_absorbs_parity_effect
        (msCellObservable_sq OA OB hOA_sq hOB_sq hac _)
        (msCellObservable_sq OA OB hOA_sq hOB_sq hac _)
        (msConstraintObservable_commute OA OB hOA_sq hOB_sq hac i 0 1) ab.1 ab.2
        (msConstraintObservable_product_parity hOA_sq hOB_sq hac i)
    · rw [if_neg hb]
      rw [← (reflection_pair_absorbs_parity_effect
        (msCellObservable_sq OA OB hOA_sq hOB_sq hac _)
        (msCellObservable_sq OA OB hOA_sq hOB_sq hac _)
        (msConstraintObservable_commute OA OB hOA_sq hOB_sq hac i 0 1) ab.1 ab.2
        (msConstraintObservable_product_parity hOA_sq hOB_sq hac i)), mul_assoc]
      rw [show reflectionEffect
          (msCellObservable OA OB (msConstraintVars i 2))
            (msParity i - ab.1 - ab.2) *
          reflectionEffect (msCellObservable OA OB (msConstraintVars i 2)) b = 0 by
        change
          (reflectionMeasurement
            (msCellObservable OA OB (msConstraintVars i 2))
            (msCellObservable_conjTranspose OA OB hOA hOB hac _)
            (msCellObservable_sq OA OB hOA_sq hOB_sq hac _)).effect
              (msParity i - ab.1 - ab.2) *
            (reflectionMeasurement
              (msCellObservable OA OB (msConstraintVars i 2))
              (msCellObservable_conjTranspose OA OB hOA hOB hac _)
              (msCellObservable_sq OA OB hOA_sq hOB_sq hac _)).effect b = 0
        rw [binary_effect_mul
          _
          (reflectionMeasurement_projective
            _
            _
            _)
          (msParity i - ab.1 - ab.2) b]
        simp [hb]]
      simp

end

end MIPStarRE.QPBT
