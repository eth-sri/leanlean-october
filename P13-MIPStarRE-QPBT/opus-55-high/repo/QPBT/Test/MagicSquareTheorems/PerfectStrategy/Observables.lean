module

public import QPBT.Algebra.Pauli
public import QPBT.Test.MagicSquareTheorems.Basic
public import MIPStarRE.Quantum.FiniteMatrix.Order

/-!
# Observables of the perfect Magic Square strategy

This module builds the operator table of `thm:ms-from-ac`.  It records the EPR
state carried by the perfect strategy, the binary reflection effects attached
to a Hermitian involution, the real Pauli matrices on the auxiliary qubit, and
the nine cell observables together with their Hermiticity, involutivity,
commutation, and constraint-product identities.

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


/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): the EPR state on `V` is invariant under
exchanging its two tensor factors. -/
theorem reindexState_prodComm_eprState
    (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V] :
    reindexState (Equiv.prodComm V V) (eprState V) = eprState V := by
  apply (EuclideanSpace.equiv (V × V) ℂ).injective
  grind [reindexState, eprState, ContinuousLinearEquiv.apply_symm_apply, Equiv.prodComm, Equiv.coe_fn_symm_mk]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): a symmetric operator acting on the first factor
of the EPR state acts on it exactly as it does on the second factor. -/
theorem epr_action_eq_of_transpose
    [Nonempty V]
    (E : Op V) (hE : Eᵀ = E) :
    (heteroKron E 1).mulVec (eprState V) =
      (heteroKron 1 E).mulVec (eprState V) := by
  ext p
  rcases p with ⟨i, j⟩
  simpa [heteroKron, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    eprState, Matrix.one_apply] using congrFun (congrFun hE j) i

theorem binary_effects_sum
    (M : Measurement (ZMod 2) V) :
    M.effect 0 + M.effect 1 = 1 := by
  rw [← sum_zmod_two M.effect]
  exact M.sum_eq_one

theorem binary_effects_orthogonal
    (M : Measurement (ZMod 2) V)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    M.effect 0 * M.effect 1 = 0 ∧ M.effect 1 * M.effect 0 = 0 := by
  have hsum := binary_effects_sum M
  have hcomp : M.effect 1 = 1 - M.effect 0 := by
    rw [← hsum]
    abel
  constructor
  · rw [hcomp]
    exact (hM 0).mul_one_sub_self
  · rw [hcomp]
    exact (hM 0).one_sub_mul_self

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): the ±1-valued observable attached to a binary
projective measurement is Hermitian. -/
theorem obsOf_conjTranspose
    (M : Measurement (ZMod 2) V)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    (obsOf M)ᴴ = obsOf M := by
  rw [obsOf, Matrix.conjTranspose_sub,
    (hM 0).isSelfAdjoint.isHermitian.eq,
    (hM 1).isSelfAdjoint.isHermitian.eq]

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): the ±1-valued observable attached to a binary
projective measurement is an involution, that is, it squares to the identity. -/
theorem obsOf_sq
    (M : Measurement (ZMod 2) V)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    obsOf M * obsOf M = 1 := by
  rcases binary_effects_orthogonal M hM with ⟨h01, h10⟩
  calc
    obsOf M * obsOf M =
        M.effect 0 * M.effect 0 - M.effect 0 * M.effect 1 -
          M.effect 1 * M.effect 0 + M.effect 1 * M.effect 1 := by
      simp only [obsOf]
      noncomm_ring
    _ = M.effect 0 + M.effect 1 := by
      rw [(hM 0).isIdempotentElem.eq, (hM 1).isIdempotentElem.eq, h01, h10]
      abel
    _ = 1 := binary_effects_sum M

/-- The effect with eigenvalue `(-1)^b` for a Hermitian involution. -/
noncomputable def reflectionEffect (O : Op V) (b : ZMod 2) : Op V :=
  if b = 0 then (2 : ℂ)⁻¹ • (1 + O) else (2 : ℂ)⁻¹ • (1 - O)

theorem reflectionEffect_isProj
    (O : Op V) (hO : Oᴴ = O) (hO_sq : O * O = 1) (b : ZMod 2) :
    IsProj (reflectionEffect O b) := by
  have hplus : (1 + O) * (1 + O) = (2 : ℂ) • (1 + O) := by
    calc
      (1 + O) * (1 + O) = 1 + O + O + O * O := by noncomm_ring
      _ = (2 : ℂ) • (1 + O) := by rw [hO_sq]; module
  have hminus : (1 - O) * (1 - O) = (2 : ℂ) • (1 - O) := by
    calc
      (1 - O) * (1 - O) = 1 - O - O + O * O := by noncomm_ring
      _ = (2 : ℂ) • (1 - O) := by rw [hO_sq]; module
  refine isStarProjection_iff'.2 ⟨?_, ?_⟩
  · rcases zmod_two_eq_zero_or_one b with rfl | rfl
    · simp only [reflectionEffect, if_pos]
      rw [smul_mul_smul, hplus, smul_smul]
      norm_num
    simp_all [reflectionEffect, one_ne_zero, smul_smul]
  · rcases zmod_two_eq_zero_or_one b with rfl | rfl
    · simp_all [reflectionEffect, Matrix.star_eq_conjTranspose]
    simp_all [reflectionEffect, Matrix.star_eq_conjTranspose]

/-- The binary projective measurement associated with a Hermitian involution. -/
noncomputable def reflectionMeasurement
    (O : Op V) (hO : Oᴴ = O) (hO_sq : O * O = 1) :
    Measurement (ZMod 2) V :=
  Measurement.ofSumEqOne (reflectionEffect O)
    (fun b => by
      exact (reflectionEffect_isProj O hO hO_sq b).nonneg)
    (by
      rw [sum_zmod_two]
      simp [reflectionEffect]
      module)

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): the binary measurement built from a Hermitian
involution is projective. -/
theorem reflectionMeasurement_projective
    (O : Op V) (hO : Oᴴ = O) (hO_sq : O * O = 1) :
    MIPStarRE.QPBT.Measurement.IsProjective
      (reflectionMeasurement O hO hO_sq) :=
  reflectionEffect_isProj O hO hO_sq

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): passing from a binary projective measurement to
its ±1-valued observable and back recovers the original effects. -/
theorem reflectionEffect_obsOf_measurement
    (M : Measurement (ZMod 2) V) (b : ZMod 2) :
    reflectionEffect (obsOf M) b = M.effect b := by
  have hsum := binary_effects_sum M
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · simp only [reflectionEffect, if_pos, obsOf]
    rw [show (1 : Op V) = M.effect 0 + M.effect 1 from hsum.symm]
    module
  · simp only [reflectionEffect, if_neg one_ne_zero, obsOf]
    rw [show (1 : Op V) = M.effect 0 + M.effect 1 from hsum.symm]
    module

local notation "qubitX" => (tauShift (K := ZMod 2) 1)
local notation "qubitZ" => (tauPhase (K := ZMod 2) 1)

theorem heteroKron_transpose
    {V W : Type*} (A : Op V) (B : Op W) :
    (heteroKron A B)ᵀ = heteroKron Aᵀ Bᵀ := by
  rfl

theorem heteroKron_neg_neg
    {V W : Type*} (A : Op V) (B : Op W) :
    heteroKron (-A) (-B) = heteroKron A B := by
  ext i j
  simp [heteroKron]

theorem anti_mul_sq
    (A B : Op V) (hA : A * A = 1) (hB : B * B = 1)
    (hAB : A * B = -(B * A)) :
    (A * B) * (A * B) = -1 := by
  have hBA : B * A = -(A * B) := by
    rw [hAB]
    simp
  calc
    (A * B) * (A * B) = A * (B * A) * B := by noncomm_ring
    _ = -(A * A) * (B * B) := by rw [hBA]; noncomm_ring
    _ = -1 := by simp_all

theorem anti_mul_conjTranspose
    {V : Type*} [Fintype V]
    (A B : Op V) (hA : Aᴴ = A) (hB : Bᴴ = B)
    (hAB : A * B = -(B * A)) :
    (A * B)ᴴ = -(A * B) := by
  simp_all

theorem anti_mul_transpose
    {V : Type*} [Fintype V]
    (A B : Op V) (hA : Aᵀ = A) (hB : Bᵀ = B)
    (hAB : A * B = -(B * A)) :
    (A * B)ᵀ = -(A * B) := by
  simp_all

/-- The nine observables in the operator table of `thm:ms-from-ac`. -/
def msCellObservable
    (OA OB : Op V) : Fin 9 → Op (V × ZMod 2) :=
  ![heteroKron OA 1, heteroKron 1 qubitX, heteroKron OA qubitX,
    heteroKron 1 qubitZ, heteroKron OB 1, heteroKron OB qubitZ,
    heteroKron OA qubitZ, heteroKron OB qubitX,
    heteroKron (OA * OB) (qubitZ * qubitX)]

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): each of the nine cell observables of the operator
table is Hermitian whenever `OA` and `OB` are Hermitian and anticommute. -/
theorem msCellObservable_conjTranspose
    (OA OB : Op V) (hOA : OAᴴ = OA) (hOB : OBᴴ = OB)
    (hac : OA * OB = -(OB * OA)) (j : Fin 9) :
    (msCellObservable OA OB j)ᴴ = msCellObservable OA OB j := by
  have hAB := anti_mul_conjTranspose OA OB hOA hOB hac
  have hZX := anti_mul_conjTranspose qubitZ qubitX binaryTauPhase_conjTranspose
    binaryTauShift_conjTranspose (by
      simp [binaryTauShift_mul_tauPhase])
  fin_cases j <;>
    simp [msCellObservable, heteroKron_conjTranspose, hOA, hOB,
      binaryTauShift_conjTranspose, binaryTauPhase_conjTranspose, hAB, hZX,
      heteroKron_neg_neg]

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): each of the nine cell observables of the operator
table is an involution whenever `OA` and `OB` are anticommuting involutions. -/
theorem msCellObservable_sq
    (OA OB : Op V) (hOA : OA * OA = 1) (hOB : OB * OB = 1)
    (hac : OA * OB = -(OB * OA)) (j : Fin 9) :
    msCellObservable OA OB j * msCellObservable OA OB j = 1 := by
  have hAB := anti_mul_sq OA OB hOA hOB hac
  have hZX := anti_mul_sq qubitZ qubitX binaryTauPhase_sq binaryTauShift_sq (by
    simp [binaryTauShift_mul_tauPhase])
  fin_cases j <;>
    simp [msCellObservable, heteroKron_mul, hOA, hOB, binaryTauShift_sq,
      binaryTauPhase_sq, hAB, hZX, heteroKron_neg_neg, heteroKron_one_one]

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): each of the nine cell observables of the operator
table is symmetric whenever `OA` and `OB` are symmetric and anticommute. -/
theorem msCellObservable_transpose
    (OA OB : Op V) (hOA : OAᵀ = OA) (hOB : OBᵀ = OB)
    (hac : OA * OB = -(OB * OA)) (j : Fin 9) :
    (msCellObservable OA OB j)ᵀ = msCellObservable OA OB j := by
  have hAB := anti_mul_transpose OA OB hOA hOB hac
  have hZX := anti_mul_transpose qubitZ qubitX binaryTauPhase_transpose
    binaryTauShift_transpose (by
      simp [binaryTauShift_mul_tauPhase])
  fin_cases j <;>
    simp [msCellObservable, heteroKron_transpose, hOA, hOB,
      binaryTauShift_transpose, binaryTauPhase_transpose, hAB, hZX,
      heteroKron_neg_neg]

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): the observables attached to any two cells of the
same Magic Square constraint commute. -/
theorem msConstraintObservable_commute
    (OA OB : Op V) (hOA : OA * OA = 1) (hOB : OB * OB = 1)
    (hac : OA * OB = -(OB * OA)) (i : Fin 6) (k l : Fin 3) :
    Commute (msCellObservable OA OB (msConstraintVars i k))
      (msCellObservable OA OB (msConstraintVars i l)) := by
  have hA_BA : OA * (OB * OA) = -OB := by
    calc
      OA * (OB * OA) = (OA * OB) * OA := (mul_assoc _ _ _).symm
      _ = (-(OB * OA)) * OA := by simp_all
      _ = -OB := by simp_all [neg_mul, mul_assoc, mul_one]
  have hBA_A : OB * OA * OA = OB := by rw [mul_assoc, hOA, mul_one]
  have hB_BA : OB * (OB * OA) = OA := by rw [← mul_assoc, hOB, one_mul]
  have hBA_B : OB * OA * OB = -OA := by
    calc
      OB * OA * OB = OB * (OA * OB) := mul_assoc _ _ _
      _ = OB * (-(OB * OA)) := by simp_all
      _ = -OA := by simp_all
  have hZ_ZX : qubitZ * (qubitZ * qubitX) = qubitX := by
    rw [← mul_assoc, binaryTauPhase_sq, one_mul]
  have hZX_Z : qubitZ * qubitX * qubitZ = -qubitX := by
    calc
      qubitZ * qubitX * qubitZ = -(qubitX * qubitZ) * qubitZ := by
        simp [binaryTauShift_mul_tauPhase]
      _ = -qubitX := by rw [neg_mul, mul_assoc, binaryTauPhase_sq, mul_one]
  have hX_ZX : qubitX * (qubitZ * qubitX) = -qubitZ := by
    calc
      qubitX * (qubitZ * qubitX) = (qubitX * qubitZ) * qubitX :=
        (mul_assoc _ _ _).symm
      _ = (-(qubitZ * qubitX)) * qubitX := by rw [binaryTauShift_mul_tauPhase]
      _ = -qubitZ := by rw [neg_mul, mul_assoc, binaryTauShift_sq, mul_one]
  have hZX_X : qubitZ * qubitX * qubitX = qubitZ := by
    rw [mul_assoc, binaryTauShift_sq, mul_one]
  fin_cases i <;> fin_cases k <;> fin_cases l <;>
    simp [commute_iff_eq, msConstraintVars, msCellObservable,
      heteroKron_mul, hOA, hOB, hac, binaryTauShift_sq, binaryTauPhase_sq,
      binaryTauShift_mul_tauPhase, hA_BA, hBA_A, hB_BA, hBA_B, hZ_ZX,
      hZX_Z, hX_ZX, hZX_X, heteroKron_neg_left,
      heteroKron_neg_right]

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): the three observables of a Magic Square
constraint multiply to `1` for the five even constraints and to `-1` for the
last one, which is the anticommuting column of the operator table. -/
theorem msConstraintObservable_product
    (OA OB : Op V) (hOA : OA * OA = 1) (hOB : OB * OB = 1)
    (hac : OA * OB = -(OB * OA)) (i : Fin 6) :
    msCellObservable OA OB (msConstraintVars i 0) *
        msCellObservable OA OB (msConstraintVars i 1) *
    msCellObservable OA OB (msConstraintVars i 2) =
      if i = 5 then -1 else 1 := by
  have hAB := anti_mul_sq OA OB hOA hOB hac
  have hZX := anti_mul_sq qubitZ qubitX binaryTauPhase_sq binaryTauShift_sq (by
    simp [binaryTauShift_mul_tauPhase])
  fin_cases i <;>
    simp [msConstraintVars, msCellObservable, heteroKron_mul, hOA, hOB,
      binaryTauShift_sq, binaryTauPhase_sq, binaryTauShift_mul_tauPhase, hAB, hZX,
      heteroKron_neg_left, heteroKron_neg_right,
      heteroKron_one_one]

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): the two effects of a binary projective
measurement are orthogonal idempotents: their product is the common effect when
the outcomes agree and `0` otherwise. -/
theorem binary_effect_mul
    (M : Measurement (ZMod 2) V)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (a b : ZMod 2) :
    M.effect a * M.effect b = if a = b then M.effect a else 0 := by
  rcases binary_effects_orthogonal M hM with ⟨h01, h10⟩
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
      simp [(hM _).isIdempotentElem.eq, h01, h10]

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): the reflection effects of two commuting Hermitian
involutions commute. -/
theorem reflectionEffect_commute
    {O P : Op V} (hOP : Commute O P) (a b : ZMod 2) :
    Commute (reflectionEffect O a) (reflectionEffect P b) := by
  rw [commute_iff_eq]
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one b with rfl | rfl <;>
      simp only [reflectionEffect, if_pos, if_neg one_ne_zero]
  all_goals rw [smul_mul_smul, smul_mul_smul]
  all_goals noncomm_ring [hOP.eq]

theorem reflectionEffect_commute_obs
    {O P : Op V} (hOP : Commute O P) (a : ZMod 2) :
    Commute (reflectionEffect O a) P := by
  rw [commute_iff_eq]
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;>
    simp only [reflectionEffect, if_pos, if_neg one_ne_zero]
  all_goals rw [smul_mul_assoc, mul_smul_comm]
  all_goals noncomm_ring [hOP.eq]

theorem reflectionEffect_mul_obs_zero
    (O : Op V) (hO : O * O = 1) :
    reflectionEffect O 0 * O = reflectionEffect O 0 := by
  simp only [reflectionEffect, if_pos]
  grind [smul_mul_assoc, add_mul, one_mul]

theorem reflectionEffect_mul_obs_one
    (O : Op V) (hO : O * O = 1) :
    reflectionEffect O 1 * O = -reflectionEffect O 1 := by
  simp only [reflectionEffect, if_neg one_ne_zero]
  rw [smul_mul_assoc, sub_mul, one_mul, hO]
  module

theorem mul_reflectionEffect_zero_of_eigen_pos
    (E O : Op V) (hEO : E * O = E) :
    E * reflectionEffect O 0 = E := by
  simp only [reflectionEffect, if_pos]
  rw [mul_smul_comm, mul_add, mul_one, hEO]
  module

theorem mul_reflectionEffect_one_of_eigen_neg
    (E O : Op V) (hEO : E * O = -E) :
    E * reflectionEffect O 1 = E := by
  simp only [reflectionEffect, if_neg one_ne_zero]
  rw [mul_smul_comm, mul_sub, mul_one, hEO]
  module

theorem reflection_pair_mul_observables
    {V : Type*} [Fintype V]
    (P0 P1 O0 O1 : Op V) (s0 s1 : ℂ)
    (h10 : Commute P1 O0)
    (h0 : P0 * O0 = s0 • P0) (h1 : P1 * O1 = s1 • P1) :
    (P0 * P1) * (O0 * O1) = (s0 * s1) • (P0 * P1) := by
  calc
    (P0 * P1) * (O0 * O1) = P0 * (P1 * O0) * O1 := by noncomm_ring
    _ = P0 * (O0 * P1) * O1 := by grind
    _ = (P0 * O0) * (P1 * O1) := by noncomm_ring
    _ = (s0 • P0) * (s1 • P1) := by simp_all
    _ = (s0 * s1) • (P0 * P1) := by rw [smul_mul_smul]

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): if `O0` and `O1` are commuting involutions and
the product `O0 * O1 * O2` equals `(-1) ^ p`, then the third reflection effect
taken at the outcome `p - b0 - b1` forced by the parity acts as the identity on
the product of the first two reflection effects. -/
theorem reflection_pair_absorbs_parity_effect
    (O0 O1 O2 : Op V)
    (hO0 : O0 * O0 = 1) (hO1 : O1 * O1 = 1)
    (h01 : Commute O0 O1)
    (p b0 b1 : ZMod 2)
    (hp : (p = 0 ∧ O0 * O1 * O2 = 1) ∨
      (p = 1 ∧ O0 * O1 * O2 = -1)) :
    (reflectionEffect O0 b0 * reflectionEffect O1 b1) *
        reflectionEffect O2 (p - b0 - b1) =
      reflectionEffect O0 b0 * reflectionEffect O1 b1 := by
  rcases hp with ⟨rfl, hprod⟩ | ⟨rfl, hprod⟩
  · have hO2eq : O2 = O0 * O1 := by
      calc
        O2 = (O0 * O0) * (O1 * O1) * O2 := by simp_all
        _ = O0 * (O0 * O1) * O1 * O2 := by noncomm_ring
        _ = O0 * (O1 * O0) * O1 * O2 := by grind
        _ = O0 * O1 * (O0 * O1 * O2) := by noncomm_ring
        _ = O0 * O1 := by simp_all
    rcases zmod_two_eq_zero_or_one b0 with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one b1 with rfl | rfl
    · grind [mul_reflectionEffect_zero_of_eigen_pos, reflection_pair_mul_observables, reflectionEffect, reflectionEffect_commute_obs, reflectionEffect_mul_obs_zero]
    · apply mul_reflectionEffect_one_of_eigen_neg
      rw [hO2eq]
      simpa using reflection_pair_mul_observables
        (reflectionEffect O0 0) (reflectionEffect O1 1) O0 O1 1 (-1)
        (reflectionEffect_commute_obs h01.symm 1)
        (by simp_all [reflectionEffect_mul_obs_zero])
        (by simp_all [reflectionEffect_mul_obs_one])
    · apply mul_reflectionEffect_one_of_eigen_neg
      rw [hO2eq]
      simpa using reflection_pair_mul_observables
        (reflectionEffect O0 1) (reflectionEffect O1 0) O0 O1 (-1) 1
        (reflectionEffect_commute_obs h01.symm 0)
        (by simp_all [reflectionEffect_mul_obs_one])
        (by simp_all [reflectionEffect_mul_obs_zero])
    · apply mul_reflectionEffect_zero_of_eigen_pos
      rw [hO2eq]
      simpa using reflection_pair_mul_observables
        (reflectionEffect O0 1) (reflectionEffect O1 1) O0 O1 (-1) (-1)
        (reflectionEffect_commute_obs h01.symm 1)
        (by simp_all [reflectionEffect_mul_obs_one])
        (by simp_all [reflectionEffect_mul_obs_one])
  · have hO2eq : O2 = -(O0 * O1) := by
      calc
        O2 = (O0 * O0) * (O1 * O1) * O2 := by simp_all
        _ = O0 * (O0 * O1) * O1 * O2 := by noncomm_ring
        _ = O0 * (O1 * O0) * O1 * O2 := by grind
        _ = O0 * O1 * (O0 * O1 * O2) := by noncomm_ring
        _ = -(O0 * O1) := by simp_all
    rcases zmod_two_eq_zero_or_one b0 with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one b1 with rfl | rfl
    · apply mul_reflectionEffect_one_of_eigen_neg
      rw [hO2eq, mul_neg]
      grind [reflection_pair_mul_observables, reflectionEffect, reflectionEffect_commute_obs, reflectionEffect_mul_obs_zero]
    · apply mul_reflectionEffect_zero_of_eigen_pos
      have hpair := reflection_pair_mul_observables
        (reflectionEffect O0 0) (reflectionEffect O1 1) O0 O1 1 (-1)
        (reflectionEffect_commute_obs h01.symm 1)
        (by simp_all [reflectionEffect_mul_obs_zero])
        (by simp_all [reflectionEffect_mul_obs_one])
      simp_all
    · apply mul_reflectionEffect_zero_of_eigen_pos
      have hpair := reflection_pair_mul_observables
        (reflectionEffect O0 1) (reflectionEffect O1 0) O0 O1 (-1) 1
        (reflectionEffect_commute_obs h01.symm 0)
        (by simp_all [reflectionEffect_mul_obs_one])
        (by simp_all [reflectionEffect_mul_obs_zero])
      simp_all
    · apply mul_reflectionEffect_one_of_eigen_neg
      have hpair := reflection_pair_mul_observables
        (reflectionEffect O0 1) (reflectionEffect O1 1) O0 O1 (-1) (-1)
        (reflectionEffect_commute_obs h01.symm 1)
        (by simp_all [reflectionEffect_mul_obs_one])
        (by simp_all [reflectionEffect_mul_obs_one])
      simp_all

end

end MIPStarRE.QPBT
