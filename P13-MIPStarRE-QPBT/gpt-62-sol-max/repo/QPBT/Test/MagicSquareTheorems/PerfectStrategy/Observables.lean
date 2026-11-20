module

public import QPBT.Games.EPR
public import QPBT.Games.DistanceTheorems.Support
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

/-- The state of the perfect strategy constructed in `thm:ms-from-ac`. -/
noncomputable def msPerfectState (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] : EuclideanSpace ℂ ((ι × ZMod 2) × (ι × ZMod 2)) :=
  reindexState prodShuffle (vecTensor (eprState ι) (eprState (ZMod 2)))

private theorem binary_effects_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : Measurement (ZMod 2) V) :
    M.effect 0 + M.effect 1 = 1 := by
  rw [← sum_zmod_two M.effect]
  exact M.sum_eq_one

private theorem binary_effects_orthogonal
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : Measurement (ZMod 2) V)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    M.effect 0 * M.effect 1 = 0 ∧ M.effect 1 * M.effect 0 = 0 := by
  exact ⟨DistanceCalculus.projective_effect_mul_effect_eq_zero M hM (by decide),
    DistanceCalculus.projective_effect_mul_effect_eq_zero M hM (by decide)⟩

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): the ±1-valued observable attached to a binary
projective measurement is Hermitian. -/
theorem obsOf_conjTranspose
    {V : Type*} [Fintype V] [DecidableEq V]
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
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : Measurement (ZMod 2) V)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) :
    obsOf M * obsOf M = 1 := by
  rcases binary_effects_orthogonal M hM with ⟨h01, h10⟩
  rw [obsOf, sub_mul, mul_sub, mul_sub, h01, h10,
    (hM 0).isIdempotentElem.eq, (hM 1).isIdempotentElem.eq]
  simpa using binary_effects_sum M

/-- The effect with eigenvalue `(-1)^b` for a Hermitian involution. -/
noncomputable def reflectionEffect {V : Type*} [Fintype V]
    [DecidableEq V] (O : Op V) (b : ZMod 2) : Op V :=
  if b = 0 then (2 : ℂ)⁻¹ • (1 + O) else (2 : ℂ)⁻¹ • (1 - O)

theorem reflectionEffect_eq_sign {V : Type*} [Fintype V] [DecidableEq V]
    (O : Op V) (b : ZMod 2) :
    reflectionEffect O b = (2 : ℂ)⁻¹ • (1 + phaseSign b • O) := by
  by_cases h : b = 0 <;> simp [reflectionEffect, phaseSign, sub_eq_add_neg, h]

private theorem reflectionEffect_isProj
    {V : Type*} [Fintype V] [DecidableEq V]
    (O : Op V) (hO : Oᴴ = O) (hO_sq : O * O = 1) (b : ZMod 2) :
    IsProj (reflectionEffect O b) := by
  rw [reflectionEffect_eq_sign]
  refine isStarProjection_iff'.2 ⟨?_, ?_⟩
  · rw [smul_mul_smul]
    have h : (1 + phaseSign b • O) * (1 + phaseSign b • O) = (2 : ℂ) • (1 + phaseSign b • O) := by
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul, hO_sq,
        phaseSign_mul_self, one_smul]
      module
    rw [h, smul_smul]
    norm_num
  · simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul, star_phaseSign, hO]

/-- The binary projective measurement associated with a Hermitian involution. -/
noncomputable def reflectionMeasurement
    {V : Type*} [Fintype V] [DecidableEq V]
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
    {V : Type*} [Fintype V] [DecidableEq V]
    (O : Op V) (hO : Oᴴ = O) (hO_sq : O * O = 1) :
    MIPStarRE.QPBT.Measurement.IsProjective
      (reflectionMeasurement O hO hO_sq) :=
  reflectionEffect_isProj O hO hO_sq

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): passing from a binary projective measurement to
its ±1-valued observable and back recovers the original effects. -/
theorem reflectionEffect_obsOf_measurement
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : Measurement (ZMod 2) V) (b : ZMod 2) :
    reflectionEffect (obsOf M) b = M.effect b := by
  have hsum := binary_effects_sum M
  rcases zmod_two_eq_zero_or_one b with rfl | rfl
  · simp only [reflectionEffect, if_pos, obsOf]
    rw [show (1 : Op V) = M.effect 0 + M.effect 1 from hsum.symm]
    module
  · simp [reflectionEffect, obsOf]
    rw [show (1 : Op V) = M.effect 0 + M.effect 1 from hsum.symm]
    module

local notation "qubitX" => (tauShift (K := ZMod 2) 1)
local notation "qubitZ" => (tauPhase (K := ZMod 2) 1)

private theorem heteroKron_transpose
    {V W : Type*} (A : Op V) (B : Op W) :
    (heteroKron A B)ᵀ = heteroKron Aᵀ Bᵀ := by rfl

private theorem heteroKron_neg_neg
    {V W : Type*} (A : Op V) (B : Op W) :
    heteroKron (-A) (-B) = heteroKron A B := by
  ext i j
  simp [heteroKron]

private theorem anti_mul_sq
    {V : Type*} [Fintype V] [DecidableEq V]
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

private theorem anti_mul_conjTranspose
    {V : Type*} [Fintype V]
    (A B : Op V) (hA : Aᴴ = A) (hB : Bᴴ = B)
    (hAB : A * B = -(B * A)) :
    (A * B)ᴴ = -(A * B) := by simp_all

private theorem anti_mul_transpose
    {V : Type*} [Fintype V]
    (A B : Op V) (hA : Aᵀ = A) (hB : Bᵀ = B)
    (hAB : A * B = -(B * A)) :
    (A * B)ᵀ = -(A * B) := by simp_all

/-- The nine observables in the operator table of `thm:ms-from-ac`. -/
def msCellObservable
    {V : Type*} [Fintype V] [DecidableEq V]
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
    {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) (hOA : OAᴴ = OA) (hOB : OBᴴ = OB)
    (hac : OA * OB = -(OB * OA)) (j : Fin 9) :
    (msCellObservable OA OB j)ᴴ = msCellObservable OA OB j := by
  have hAB := anti_mul_conjTranspose OA OB hOA hOB hac
  have hZX := anti_mul_conjTranspose qubitZ qubitX binaryTauPhase_conjTranspose
    binaryTauShift_conjTranspose (by simp [binaryTauShift_mul_tauPhase])
  fin_cases j <;>
    simp [msCellObservable, heteroKron_conjTranspose, hOA, hOB,
      binaryTauShift_conjTranspose, binaryTauPhase_conjTranspose, hAB, hZX,
      heteroKron_neg_neg]

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): each of the nine cell observables of the operator
table is an involution whenever `OA` and `OB` are anticommuting involutions. -/
theorem msCellObservable_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) (hOA : OA * OA = 1) (hOB : OB * OB = 1)
    (hac : OA * OB = -(OB * OA)) (j : Fin 9) :
    msCellObservable OA OB j * msCellObservable OA OB j = 1 := by
  have hAB := anti_mul_sq OA OB hOA hOB hac
  have hZX := anti_mul_sq qubitZ qubitX binaryTauPhase_sq binaryTauShift_sq (by simp [binaryTauShift_mul_tauPhase])
  fin_cases j <;>
    simp [msCellObservable, heteroKron_mul, hOA, hOB, binaryTauShift_sq,
      binaryTauPhase_sq, hAB, hZX, heteroKron_neg_neg, heteroKron_one_one]

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): each of the nine cell observables of the operator
table is symmetric whenever `OA` and `OB` are symmetric and anticommute. -/
theorem msCellObservable_transpose
    {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) (hOA : OAᵀ = OA) (hOB : OBᵀ = OB)
    (hac : OA * OB = -(OB * OA)) (j : Fin 9) :
    (msCellObservable OA OB j)ᵀ = msCellObservable OA OB j := by
  have hAB := anti_mul_transpose OA OB hOA hOB hac
  have hZX := anti_mul_transpose qubitZ qubitX binaryTauPhase_transpose
    binaryTauShift_transpose (by simp [binaryTauShift_mul_tauPhase])
  fin_cases j <;>
    simp [msCellObservable, heteroKron_transpose, hOA, hOB,
      binaryTauShift_transpose, binaryTauPhase_transpose, hAB, hZX,
      heteroKron_neg_neg]

/-- The three cell observables of one row or column. -/
abbrev msConstraintObservable {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) (i : Fin 6) (k : Fin 3) :=
  msCellObservable OA OB (msConstraintVars i k)

private theorem msConstraintObservable_commute_first {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) (hac : OA * OB = -(OB * OA)) (i : Fin 6) :
    Commute (msConstraintObservable OA OB i 0) (msConstraintObservable OA OB i 1) := by
  rw [commute_iff_eq]
  fin_cases i <;> simp [msConstraintObservable, msConstraintVars, msCellObservable,
    heteroKron_mul, binaryTauShift_mul_tauPhase, hac, heteroKron_neg_left, heteroKron_neg_right]

private theorem msConstraintObservable_third {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) (i : Fin 6) :
    msConstraintObservable OA OB i 2 = phaseSign (msParity i) •
      (msConstraintObservable OA OB i 0 * msConstraintObservable OA OB i 1) := by
  fin_cases i <;> simp [msConstraintObservable, msConstraintVars, msCellObservable, msParity,
    phaseSign, heteroKron_mul, binaryTauShift_mul_tauPhase, heteroKron_neg_right]

/-- The three observables of each row or column commute. -/
theorem msConstraintObservable_commute {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) (hac : OA * OB = -(OB * OA)) (i : Fin 6) (k l : Fin 3) :
    Commute (msConstraintObservable OA OB i k) (msConstraintObservable OA OB i l) := by
  have h01 := msConstraintObservable_commute_first OA OB hac i
  have h02 : Commute (msConstraintObservable OA OB i 0) (msConstraintObservable OA OB i 2) := by
    rw [msConstraintObservable_third]
    exact ((Commute.refl _).mul_right h01).smul_right _
  have h12 : Commute (msConstraintObservable OA OB i 1) (msConstraintObservable OA OB i 2) := by
    rw [msConstraintObservable_third]
    exact (h01.symm.mul_right (Commute.refl _)).smul_right _
  fin_cases k <;> fin_cases l <;> first
    | exact Commute.refl _
    | exact h01
    | exact h01.symm
    | exact h02
    | exact h02.symm
    | exact h12
    | exact h12.symm

/-- The product of the row or column is its prescribed sign times the identity. -/
theorem msConstraintObservable_product {V : Type*} [Fintype V] [DecidableEq V]
    (OA OB : Op V) (hOA : OA * OA = 1) (hOB : OB * OB = 1)
    (hac : OA * OB = -(OB * OA)) (i : Fin 6) :
    msConstraintObservable OA OB i 0 * msConstraintObservable OA OB i 1 *
      msConstraintObservable OA OB i 2 = phaseSign (msParity i) • 1 := by
  rw [msConstraintObservable_third, mul_smul_comm,
    (msConstraintObservable_commute_first OA OB hac i).symm.mul_mul_mul_comm]
  simp only [msConstraintObservable, msCellObservable_sq OA OB hOA hOB hac, one_mul]

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): the two effects of a binary projective
measurement are orthogonal idempotents: their product is the common effect when
the outcomes agree and `0` otherwise. -/
theorem binary_effect_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : Measurement (ZMod 2) V)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (a b : ZMod 2) :
    M.effect a * M.effect b = if a = b then M.effect a else 0 := by
  split_ifs with h
  · subst b
    exact (hM a).isIdempotentElem.eq
  · exact DistanceCalculus.projective_effect_mul_effect_eq_zero M hM h

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): the reflection effects of two commuting Hermitian
involutions commute. -/
private theorem reflectionEffect_commute_obs
    {V : Type*} [Fintype V] [DecidableEq V]
    {O P : Op V} (hOP : Commute O P) (a : ZMod 2) :
    Commute (reflectionEffect O a) P := by
  rw [reflectionEffect_eq_sign]
  exact ((Commute.one_left P).add_left (hOP.smul_left _)).smul_left _

theorem reflectionEffect_commute
    {V : Type*} [Fintype V] [DecidableEq V]
    {O P : Op V} (hOP : Commute O P) (a b : ZMod 2) :
    Commute (reflectionEffect O a) (reflectionEffect P b) :=
  (reflectionEffect_commute_obs (reflectionEffect_commute_obs hOP a).symm b).symm

private theorem reflectionEffect_mul_obs
    {V : Type*} [Fintype V] [DecidableEq V]
    (O : Op V) (hO : O * O = 1) (b : ZMod 2) :
    reflectionEffect O b * O = phaseSign b • reflectionEffect O b := by
  simp only [reflectionEffect_eq_sign, smul_mul_assoc, add_mul, one_mul,
    hO, smul_add, smul_smul]
  rw [mul_left_comm (phaseSign b) (2 : ℂ)⁻¹, phaseSign_mul_self, mul_one,
    mul_comm (phaseSign b) (2 : ℂ)⁻¹, add_comm]

private theorem reflection_pair_mul_observables
    {V : Type*} [Fintype V]
    (P0 P1 O0 O1 : Op V) (s0 s1 : ℂ)
    (h10 : Commute P1 O0)
    (h0 : P0 * O0 = s0 • P0) (h1 : P1 * O1 = s1 • P1) :
    (P0 * P1) * (O0 * O1) = (s0 * s1) • (P0 * P1) := by
  rw [h10.mul_mul_mul_comm, h0, h1, smul_mul_smul]

/-- The product of the first two spectral effects is supported on the third
outcome dictated by the parity of the three reflections. -/
theorem reflection_pair_mul_parity_effect
    {V : Type*} [Fintype V] [DecidableEq V]
    (O0 O1 O2 : Op V)
    (hO0 : O0 * O0 = 1) (hO1 : O1 * O1 = 1)
    (h01 : Commute O0 O1)
    (p b0 b1 b : ZMod 2) (hp : O0 * O1 * O2 = phaseSign p • 1) :
    let E := reflectionEffect O0 b0 * reflectionEffect O1 b1
    E * reflectionEffect O2 b = if p - b0 - b1 = b then E else 0 := by
  intro E
  have hsq : (O0 * O1) * (O0 * O1) = 1 := by
    rw [h01.symm.mul_mul_mul_comm, hO0, hO1, one_mul]
  have hO2 : O2 = phaseSign p • (O0 * O1) := by
    rw [← mul_one (O0 * O1), ← mul_smul_comm, ← hp, ← mul_assoc, hsq, one_mul]
  have he := reflection_pair_mul_observables _ _ O0 O1 _ _
    (reflectionEffect_commute_obs h01.symm b1)
    (reflectionEffect_mul_obs O0 hO0 b0) (reflectionEffect_mul_obs O1 hO1 b1)
  change E * (O0 * O1) = (phaseSign b0 * phaseSign b1) • E at he
  have hbit : p + (b0 + b1) = p - b0 - b1 :=
    (by decide : ∀ x y z : ZMod 2, x + (y + z) = x - y - z) p b0 b1
  rw [reflectionEffect_eq_sign, mul_smul_comm, mul_add, mul_one,
    mul_smul_comm, hO2, mul_smul_comm, he]
  simp only [smul_smul, ← phaseSign_add, hbit]
  by_cases h : p - b0 - b1 = b
  · have hbb : b + b = 0 := CharTwo.add_self_eq_zero b
    rw [ite_eq_left h, h, hbb]
    simp only [phaseSign, ite_true, one_smul]
    module
  · have hb : b + (p - b0 - b1) = 1 :=
      (by decide : ∀ x y : ZMod 2, y ≠ x → x + y = 1) _ _ h
    simp [h, hb, phaseSign]

end

end MIPStarRE.QPBT
