module

public import QPBT.Test.MagicSquareTheorems.PerfectStrategy.Observables
public import QPBT.Games.Sandwich.Support

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

section Joint

variable {V : Type*} [Fintype V] [DecidableEq V]
    (M N : Measurement (ZMod 2) V)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (hN : MIPStarRE.QPBT.Measurement.IsProjective N)
    (hcomm : ∀ a b, Commute (M.effect a) (N.effect b))

include M N hM hN hcomm

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

private theorem binaryJointMeasurement_projective :
    MIPStarRE.QPBT.Measurement.IsProjective
      (binaryJointMeasurement M N hM hN hcomm) :=
  fun ab => (hM ab.1).mul (hN ab.2) (hcomm ab.1 ab.2)

private theorem binaryJointMeasurement_mul_first
    (ab : ZMod 2 × ZMod 2) (b : ZMod 2) :
    (binaryJointMeasurement M N hM hN hcomm).effect ab * M.effect b =
      if ab.1 = b then
        (binaryJointMeasurement M N hM hN hcomm).effect ab else 0 := by
  change (M.effect ab.1 * N.effect ab.2) * M.effect b =
    if ab.1 = b then M.effect ab.1 * N.effect ab.2 else 0
  rw [mul_assoc, (hcomm b ab.2).symm.eq, ← mul_assoc, binary_effect_mul M hM]
  split_ifs <;> simp_all

private theorem binaryJointMeasurement_mul_second
    (ab : ZMod 2 × ZMod 2) (b : ZMod 2) :
    (binaryJointMeasurement M N hM hN hcomm).effect ab * N.effect b =
      if ab.2 = b then
        (binaryJointMeasurement M N hM hN hcomm).effect ab else 0 := by
  change (M.effect ab.1 * N.effect ab.2) * N.effect b =
    if ab.2 = b then M.effect ab.1 * N.effect ab.2 else 0
  rw [mul_assoc, binary_effect_mul N hN]
  simp_all

end Joint

/-- Encode two freely chosen bits as the unique triple of the prescribed parity. -/
def parityTriple (i : Fin 6) (ab : ZMod 2 × ZMod 2) : Fin 3 → ZMod 2 :=
  ![ab.1, ab.2, msParity i - ab.1 - ab.2]

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): the triple encoding two freely chosen bits sums
to the parity `msParity i` prescribed by the constraint. -/
theorem parityTriple_sum (i : Fin 6) (ab : ZMod 2 × ZMod 2) :
    ∑ k : Fin 3, parityTriple i ab k = msParity i := by
  rw [Fin.sum_univ_three]
  simp [parityTriple]
  ring

private theorem bit_embedding_injective :
    Function.Injective (MsAnswer.bit : ZMod 2 → MsAnswer) := by
  intro a b h
  exact MsAnswer.bit.inj h

section

variable {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) (hOA : OAᴴ = OA) (hOB : OBᴴ = OB)
    (hOA_sq : OA * OA = 1) (hOB_sq : OB * OB = 1)
    (hac : OA * OB = -(OB * OA)) (j : Fin 9)
include V OA OB hOA hOB hOA_sq hOB_sq hac j

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

end

section

variable {V : Type*} [Fintype V] [DecidableEq V]
include V

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): each of the nine cell measurements of the Magic
Square strategy is projective. -/
theorem msCellMeasurement_projective
    (OA OB : Op V) (hOA : OAᴴ = OA) (hOB : OBᴴ = OB)
    (hOA_sq : OA * OA = 1) (hOB_sq : OB * OB = 1)
    (hac : OA * OB = -(OB * OA)) (j : Fin 9) :
    MIPStarRE.QPBT.Measurement.IsProjective
      (msCellMeasurement OA OB hOA hOB hOA_sq hOB_sq hac j) :=
  reflectionMeasurement_projective (msCellObservable OA OB j)
    (msCellObservable_conjTranspose OA OB hOA hOB hac j)
    (msCellObservable_sq OA OB hOA_sq hOB_sq hac j)

private theorem reflectionEffect_transpose
    (O : Op V) (hO : Oᵀ = O) (b : ZMod 2) :
    (reflectionEffect O b)ᵀ = reflectionEffect O b := by
  rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
    simp [reflectionEffect, Matrix.transpose_add, Matrix.transpose_sub, hO]

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
  rw [msCellMeasurement_effect]
  exact reflectionEffect_transpose _
    (msCellObservable_transpose OA OB hOA_t hOB_t hac j) b

end

section Constraints

variable {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))

include P hP hcomm

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
      (P j).effect b := by
  exact SandwichProduct.postprocess_effect_of_injective (P j) MsAnswer.bit
    bit_embedding_injective b

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): the global Magic Square measurement family is
projective at every question. -/
theorem msStrategyMeasurement_projective
    (x : MsType) :
    MIPStarRE.QPBT.Measurement.IsProjective
      (msStrategyMeasurement P hP hcomm x) := by
  cases x with
  | var j => exact SandwichProduct.postprocess_isProjective _ (hP j) _
  | constraint i =>
      exact SandwichProduct.postprocess_isProjective _
        (binaryJointMeasurement_projective _ _ (hP _) (hP _) (hcomm i 0 1)) _

end Constraints

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
  simp only [Measurement.postprocess_effect, Matrix.transpose_sum, hM]

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): multiplying a constraint effect at `ab` by the
effect of an incident cell measurement at `b` returns the constraint effect when
`b` is the bit that the parity triple assigns to that cell, and `0` otherwise;
this is the consistency of the constraint answer with its variable answers. -/
theorem msCellConstraintJoint_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) (hOA : OAᴴ = OA) (hOB : OBᴴ = OB)
    (hOA_sq : OA * OA = 1) (hOB_sq : OB * OB = 1)
    (hac : OA * OB = -(OB * OA))
    (i : Fin 6) (k : Fin 3) (ab : ZMod 2 × ZMod 2) (b : ZMod 2) :
    let P := msCellMeasurement OA OB hOA hOB hOA_sq hOB_sq hac
    let J := msConstraintJoint P
      (msCellMeasurement_projective OA OB hOA hOB hOA_sq hOB_sq hac)
      (fun i k l a b => reflectionEffect_commute
        (msConstraintObservable_commute OA OB hac i k l) a b) i
    J.effect ab * (P (msConstraintVars i k)).effect b =
      if parityTriple i ab k = b then J.effect ab else 0 := by
  intro P J
  fin_cases k
  · exact binaryJointMeasurement_mul_first _ _ _ _ _ ab b
  · exact binaryJointMeasurement_mul_second _ _ _ _ _ ab b
  · exact reflection_pair_mul_parity_effect
      (msCellObservable OA OB (msConstraintVars i 0))
      (msCellObservable OA OB (msConstraintVars i 1))
      (msCellObservable OA OB (msConstraintVars i 2))
      (msCellObservable_sq OA OB hOA_sq hOB_sq hac _)
      (msCellObservable_sq OA OB hOA_sq hOB_sq hac _)
      (msConstraintObservable_commute OA OB hac i 0 1)
      (msParity i) ab.1 ab.2 b (msConstraintObservable_product OA OB hOA_sq hOB_sq hac i)


section

variable {α β γ δ V : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    [Fintype V] [DecidableEq V]
    (M : Measurement α V) (N : Measurement β V)
include α β γ δ V M N

/-- Pairwise commuting effects stay commuting under coarse-graining. -/
theorem postprocess_commute_of_commute
    (h : ∀ x y, Commute (M.effect x) (N.effect y))
    (f : α → γ) (g : β → δ) (a : γ) (b : δ) :
    Commute ((M.postprocess f).effect a) ((N.postprocess g).effect b) := by
  rw [Measurement.postprocess_effect, Measurement.postprocess_effect]
  exact Commute.sum_left _ _ _ fun x _ => Commute.sum_right _ _ _ fun y _ => h x y

/-- If every pair of effects in two fibers has zero product, so do the readouts. -/
theorem postprocess_effect_mul_eq_zero (f : α → γ) (g : β → δ) (a : γ) (b : δ)
    (h : ∀ x y, f x = a → g y = b → M.effect x * N.effect y = 0) :
    (M.postprocess f).effect a * (N.postprocess g).effect b = 0 := by
  rw [Measurement.postprocess_effect, Measurement.postprocess_effect, Finset.sum_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_eq_zero fun y hy => h x y (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2

end

private theorem msConstraintVars_injective (i : Fin 6) :
    Function.Injective (msConstraintVars i) := by
  intro k l h
  fin_cases i <;> fin_cases k <;> fin_cases l <;>
    simp [msConstraintVars] at h ⊢

private theorem msConstraintVars_exists_iff
    (i : Fin 6) (k : Fin 3) (β : Fin 3 → ZMod 2) (b : ZMod 2) :
    (∃ l : Fin 3, msConstraintVars i l = msConstraintVars i k ∧ β l = b) ↔
      β k = b := by
  constructor
  · rintro ⟨l, hl, hlb⟩
    simp_all [msConstraintVars_injective i hl]
  · tauto

section Constraints

variable {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → Measurement (ZMod 2) V)
    (hP : ∀ j, MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (msConstraintVars i k)).effect a)
        ((P (msConstraintVars i l)).effect b))

include P hP hcomm

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): the effects of the joint measurement of the first
two cells of a constraint are symmetric whenever the underlying cell effects
are. -/
private theorem msConstraintJoint_effect_transpose
    (hPt : ∀ j b, ((P j).effect b)ᵀ = (P j).effect b)
    (i : Fin 6) (ab : ZMod 2 × ZMod 2) :
    ((msConstraintJoint P hP hcomm i).effect ab)ᵀ =
      (msConstraintJoint P hP hcomm i).effect ab := by
  change (((P (msConstraintVars i 0)).effect ab.1 *
    (P (msConstraintVars i 1)).effect ab.2)ᵀ) = _
  rw [Matrix.transpose_mul, hPt, hPt]
  exact (hcomm i 0 1 ab.1 ab.2).symm.eq

set_option maxHeartbeats 600000 in
-- Synthesizing the joint readout unfolds the measurement families.
/-- Formalization-only auxiliary for the perfect Magic Square strategy and the
proof of `lem:pauli-completeness`: a constraint effect commutes with each
incident variable effect in the measurement family built from commuting
projective cell measurements. -/
theorem msStrategyMeasurement_incident_commute
    (i : Fin 6) (k : Fin 3) (a b : MsAnswer) :
    Commute ((msStrategyMeasurement P hP hcomm (.constraint i)).effect a)
      ((msStrategyMeasurement P hP hcomm
        (.var (msConstraintVars i k))).effect b) := by
  refine postprocess_commute_of_commute (msConstraintJoint P hP hcomm i)
    (P (msConstraintVars i k)) ?_ (fun ab => .triple (parityTriple i ab)) MsAnswer.bit a b
  exact fun ab c => (hcomm i 0 k ab.1 c).mul_left (hcomm i 1 k ab.2 c)

set_option maxHeartbeats 600000 in
-- Elaborating the postprocessing changes the outcome type of both measurements.
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
  refine postprocess_effect_mul_eq_zero (msConstraintJoint P hP hcomm i) (P (msConstraintVars i k))
    (fun ab => .triple (parityTriple i ab)) MsAnswer.bit a b ?_
  rintro ab c rfl rfl
  have hn : parityTriple i ab k ≠ c := by
    simpa [msWinPredicate, parityTriple_sum, msConstraintVars_exists_iff] using hrej
  simp [hmul, hn]

omit P hP hcomm in
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
  rcases Sym2.eq_iff.mp hik with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all

/-- On supported questions, rejected outcomes have zero product. -/
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
    rw [(msStrategyMeasurement_incident_commute P hP hcomm i k b a).symm.eq]
    exact msStrategyMeasurement_rejected_mul P hP hcomm hmul i k b a
      (by simpa only [msWinPredicate_symm] using hrej)

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

end Constraints

end

end MIPStarRE.QPBT
