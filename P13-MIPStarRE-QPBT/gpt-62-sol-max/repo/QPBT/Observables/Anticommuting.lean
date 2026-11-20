module

public import QPBT.Algebra.SelfDualBasisTheorems
public import QPBT.Test.PauliBasisTest

/-!
# Commuting and anticommuting Pauli tuples

This module defines the tuple phase used in the Pauli basis test and the
conditional uniform distributions used by its observable analysis.

## References

The definitions and probability bounds formalize blueprint
`def:anticommuting-tuple` and `fact:omega-anticomm-prob`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:64-95`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

noncomputable section

/-- A tuple `(u_X,u_Z,r_X,r_Z)` over the fixed field model of an admissible
Pauli-test parameter tuple. This is the tuple space of
blueprint `def:anticommuting-tuple`, paper
`14_analysis_of_the_pauli_basis_test.tex:64-68`. -/
abbrev PauliTuple (P : AdmissibleParams) :=
  (PauliPoint P) ×
    (PauliPoint P) × PauliScalar P × PauliScalar P

section

variable {P : AdmissibleParams} (ω : PauliTuple P)
include P ω

/-- Point and scalar coordinates in the indicated basis. -/
abbrev PauliTuple.point (W : PauliKind) :=
  W.component (ω.1, ω.2.1)

abbrev PauliTuple.scalar (W : PauliKind) :=
  W.component ω.2.2

/-- The binary commutation phase of a tuple, and its sign. -/
abbrev PauliTuple.phaseBit :=
  gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2

abbrev PauliTuple.phase := phaseSign ω.phaseBit

/-- A Pauli tuple is anticommuting when its phase bit is nonzero. This is
blueprint `def:anticommuting-tuple`, paper
`14_analysis_of_the_pauli_basis_test.tex:64-68`. -/
def IsAnticommuting : Prop :=
  ω.phaseBit ≠ 0

/-- A Pauli tuple is commuting when its phase bit vanishes. This is the
complementary case in blueprint
`def:anticommuting-tuple`, paper
`14_analysis_of_the_pauli_basis_test.tex:64-68`. -/
def IsCommuting : Prop :=
  ω.phaseBit = 0

end

section

variable (P : AdmissibleParams)
include P

noncomputable instance instDecidablePredPauliTupleIsAnticommuting :
    DecidablePred (@IsAnticommuting P) := Classical.decPred _

noncomputable instance instDecidablePredPauliTupleIsCommuting :
    DecidablePred (@IsCommuting P) := Classical.decPred _

/-- The uniform probability of the anticommuting event. This is the first
quantity in blueprint
`fact:omega-anticomm-prob`, paper
`14_analysis_of_the_pauli_basis_test.tex:70-77`. -/
noncomputable def anticommProb : ℝ :=
  ((Finset.univ.filter (@IsAnticommuting P)).card : ℝ) /
    Fintype.card (PauliTuple P)

/-- The complementary uniform probability of the commuting event in
blueprint `fact:omega-anticomm-prob`,
paper `14_analysis_of_the_pauli_basis_test.tex:70-77`. -/
noncomputable def commProb : ℝ :=
  ((Finset.univ.filter (@IsCommuting P)).card : ℝ) /
    Fintype.card (PauliTuple P)

end

/-! ### Auxiliary counting lemmas

The declarations of this section are formalization-only auxiliaries for the
proof of blueprint
`fact:omega-anticomm-prob`. They record the cardinalities used by the
exact computation of the anticommuting probability. -/

section

variable (P : AdmissibleParams)
include P

/-- Formalization-only auxiliary: the scalar carrier of an admissible parameter
tuple has characteristic two, since it is an algebra over the two-element
field. Blueprint `fact:omega-anticomm-prob`. -/
private theorem pauliScalar_charTwo :
    CharP (PauliScalar P) 2 :=
  (Algebra.charP_iff (ZMod 2) (PauliScalar P) 2).mp (ZMod.charP 2)

/-- Formalization-only auxiliary: the scalar carrier of an admissible parameter
tuple has exactly `q` elements. Blueprint
`fact:omega-anticomm-prob`. -/
private theorem card_pauliScalar :
    Fintype.card (PauliScalar P) = P.q :=
  @FieldModel.card P.q P.model.toFieldModel

/-- The phase bit of a Pauli tuple is the trace of `r_Z r_X` times the product
of the coordinate sums `1 + u_{X,i} + u_{Z,i}`. This is the closed form of
`γ(ω)` derived in the proof of blueprint
`fact:omega-anticomm-prob`. -/
private theorem gammaValue_eq_trace_prod
    (uX uZ : PauliPoint P) (rX rZ : PauliScalar P) :
    gammaValue P uX uZ rX rZ =
      fixedBinTrace P.model (rZ * (rX * ∏ i : Fin P.m, (1 + uX i + uZ i))) := by
  haveI := pauliScalar_charTwo P
  have hprod :=
    sum_indicatorVec_mul_indicatorVec uX uZ
  unfold gammaValue
  congr 1
  rw [← hprod]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- Formalization-only auxiliary: the field trace onto the two-element field
takes each of its two values on exactly half of the scalars. This is the final
step of the proof of blueprint
`fact:omega-anticomm-prob`. -/
private theorem two_mul_card_trace_ne :
    2 * (Finset.univ.filter
        (fun a : PauliScalar P => fixedBinTrace P.model a ≠ 0)).card = P.q := by
  classical
  let trace := fixedBinTrace P.model
  obtain ⟨b, hb⟩ := Algebra.trace_surjective (ZMod 2) (PauliScalar P) (1 : ZMod 2)
  change trace b = 1 at hb
  have h := Fintype.sum_equiv (Equiv.addRight b)
    (fun a => if trace a = 0 then (1 : ℕ) else 0)
    (fun a => if trace a ≠ 0 then (1 : ℕ) else 0) (by
      intro a
      have ht : trace (a + b) = trace a + 1 := by
        rw [← hb]
        exact map_add (Algebra.trace (ZMod 2) (PauliScalar P)) a b
      change (if trace a = 0 then (1 : ℕ) else 0) = (if trace (a + b) ≠ 0 then 1 else 0)
      rw [ht]
      have : ∀ z : ZMod 2, z + 1 ≠ 0 ↔ z = 0 := by decide
      simp only [this])
  simp only [← Finset.card_filter] at h
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun a => trace a = 0)
  rw [Finset.card_univ, card_pauliScalar, h] at hsum
  exact (two_mul _).trans hsum

/-- Formalization-only auxiliary: the number of Pauli tuples. Blueprint
`fact:omega-anticomm-prob`. -/
private theorem card_pauliTuple :
    Fintype.card (PauliTuple P) = P.q ^ P.m * (P.q ^ P.m * (P.q * P.q)) := by simp_all

/-- Twice the number of anticommuting tuples is `q^{m+1}(q-1)^{m+1}`. This is
the exact count established in the proof of blueprint
`fact:omega-anticomm-prob`. -/
private theorem two_mul_card_anticommuting :
    2 * (Finset.univ.filter (@IsAnticommuting P)).card
      = P.q ^ (P.m + 1) * (P.q - 1) ^ (P.m + 1) := by
  classical
  let trace := fixedBinTrace P.model
  have htr0 : trace 0 = 0 := map_zero (Algebra.trace (ZMod 2) (PauliScalar P))
  have htrace (c : PauliScalar P) :
      (∑ r, if fixedBinTrace P.model (r * c) ≠ 0 then (2 : ℕ) else 0) = if c = 0 then 0 else P.q := by
    by_cases hc : c = 0
    · simp [hc, ← show trace = fixedBinTrace P.model from rfl, htr0]
    · rw [ite_eq_right hc, Fintype.sum_equiv (Equiv.mulRight₀ c hc)
        (fun r => if fixedBinTrace P.model (r * c) ≠ 0 then (2 : ℕ) else 0)
        (fun a => if trace a ≠ 0 then (2 : ℕ) else 0) (fun _ => rfl)]
      simp only [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul]
      rw [mul_comm]
      exact two_mul_card_trace_ne P
  have hscale (c : PauliScalar P) :
      (∑ r, if r * c = 0 then (0 : ℕ) else P.q) =
        if c = 0 then 0 else (P.q - 1) * P.q := by
    by_cases hc : c = 0 <;>
      simp [hc, mul_eq_zero, Finset.sum_ite, Finset.filter_ne',
        Finset.card_erase_of_mem, card_pauliScalar]
  have hpoints (uX : PauliPoint P) :
      (∑ uZ : PauliPoint P,
        if (∏ i, (1 + uX i + uZ i)) = 0 then 0 else (P.q - 1) * P.q) =
          (P.q - 1) ^ P.m * ((P.q - 1) * P.q) := by
    have hset : Finset.univ.filter (fun uZ : PauliPoint P =>
        (∏ i, (1 + uX i + uZ i)) ≠ 0) =
          Fintype.piFinset (fun i => Finset.univ.erase (-(1 + uX i))) := by
      ext uZ
      simp [Finset.prod_ne_zero_iff, add_eq_zero_iff_eq_neg']
    rw [Finset.sum_ite]
    simp [hset, Fintype.card_piFinset, Finset.card_erase_of_mem, card_pauliScalar]
  simp only [Finset.card_filter, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_one,
    mul_zero, IsAnticommuting, gammaValue_eq_trace_prod, htrace, hscale, hpoints,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fun, Fintype.card_fin,
    card_pauliScalar]
  rw [pow_succ, pow_succ]
  ring

/-- The anticommuting and commuting events partition the tuple space.
Blueprint `fact:omega-anticomm-prob`. -/
private theorem card_comm_add_card_anticomm :
    (Finset.univ.filter (@IsCommuting P)).card
      + (Finset.univ.filter (@IsAnticommuting P)).card
      = Fintype.card (PauliTuple P) := by
  classical
  have hfil : (Finset.univ.filter (@IsAnticommuting P))
      = Finset.univ.filter (fun ω : PauliTuple P => ¬ (@IsCommuting P ω)) := by
    refine Finset.filter_congr ?_
    intro ω _
    simp [IsAnticommuting, IsCommuting]
  rw [hfil, ← Finset.card_univ]
  exact Finset.card_filter_add_card_filter_not _

/-- Formalization-only auxiliary: the tuple space is nonempty and finite.
Blueprint `fact:omega-anticomm-prob`. -/
private theorem card_pauliTuple_pos :
    0 < Fintype.card (PauliTuple P) := by positivity

end

/-! ### The exact anticommuting probability -/

section

variable (P : AdmissibleParams)
include P

/-- Exact anticommuting probability from blueprint
`fact:omega-anticomm-prob`; its derivation replaces the erroneous
Schwartz--Zippel argument at paper
`14_analysis_of_the_pauli_basis_test.tex:79-93`. -/
theorem anticommProb_eq :
    anticommProb P = (1 - (P.q : ℝ)⁻¹) ^ (P.m + 1) / 2 := by
  have hq2 := P.hq.two_le
  have hqR : (0 : ℝ) < (P.q : ℝ) := by
    have h : 0 < P.q := by omega
    exact_mod_cast h
  have hcast : ((2 * (Finset.univ.filter (@IsAnticommuting P)).card : ℕ) : ℝ)
      = ((P.q ^ (P.m + 1) * (P.q - 1) ^ (P.m + 1) : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (two_mul_card_anticommuting P)
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
    Nat.cast_sub (by omega : 1 ≤ P.q), Nat.cast_one, Nat.cast_ofNat] at hcast
  have hval : ((Finset.univ.filter (@IsAnticommuting P)).card : ℝ)
      = (P.q : ℝ) ^ (P.m + 1) * ((P.q : ℝ) - 1) ^ (P.m + 1) / 2 := by linarith
  have hbase : (1 : ℝ) - (P.q : ℝ)⁻¹ = ((P.q : ℝ) - 1) / (P.q : ℝ) := by
    field_simp
  rw [anticommProb, hval, card_pauliTuple P, hbase, div_pow]
  push_cast
  field_simp
  ring

/-- A tuple is commuting with the probability complementary to the
anticommuting one. This is the complementarity clause of
blueprint `fact:omega-anticomm-prob`,
paper `14_analysis_of_the_pauli_basis_test.tex:70-77`. -/
theorem commProb_eq_one_sub_anticommProb :
    commProb P = 1 - anticommProb P := by
  have hpos : (0 : ℝ) < (Fintype.card (PauliTuple P) : ℝ) := by
    exact_mod_cast card_pauliTuple_pos P
  have hsum : ((Finset.univ.filter (@IsCommuting P)).card : ℝ)
      + ((Finset.univ.filter (@IsAnticommuting P)).card : ℝ)
      = (Fintype.card (PauliTuple P) : ℝ) := by
    exact_mod_cast card_comm_add_card_anticomm P
  rw [commProb, anticommProb, eq_sub_iff_add_eq, ← add_div, hsum,
    div_self hpos.ne']

/-- Formalization-only auxiliary: the base `1 - q^{-1}` of the exact
anticommuting probability lies in the unit interval. Blueprint
`fact:omega-anticomm-prob`. -/
private theorem base_mem_unit_interval :
    (0 : ℝ) ≤ 1 - (P.q : ℝ)⁻¹ ∧ (1 : ℝ) - (P.q : ℝ)⁻¹ ≤ 1 := by
  have hq : (1 : ℝ) ≤ P.q := by exact_mod_cast (show 1 ≤ P.q from P.hq.two_le.trans' (by decide))
  have hi := (inv_le_one₀ (by positivity)).mpr hq
  constructor <;> linarith [inv_nonneg.mpr (Nat.cast_nonneg P.q : (0 : ℝ) ≤ P.q)]

/-- The commuting event has probability at least one half. This is the
complementary bound in blueprint
`fact:omega-anticomm-prob`, paper
`14_analysis_of_the_pauli_basis_test.tex:70-77`. -/
theorem commProb_ge_half : 1 / 2 ≤ commProb P := by
  obtain ⟨h0, h1⟩ := base_mem_unit_interval P
  have hle : (1 - (P.q : ℝ)⁻¹) ^ (P.m + 1) ≤ 1 := pow_le_one₀ h0 h1
  rw [commProb_eq_one_sub_anticommProb, anticommProb_eq]
  linarith

/-- When `m ≤ q`, the anticommuting event has the uniform constant lower
bound added in blueprint
`fact:omega-anticomm-prob`. -/
theorem anticommProb_ge_of_m_le_q (hmq : P.m ≤ P.q) :
    (2 : ℝ) ^ (-4 : ℤ) ≤ anticommProb P := by
  rw [anticommProb_eq]
  suffices h : (1 : ℝ) / 8 ≤ (1 - (P.q : ℝ)⁻¹) ^ (P.m + 1) by norm_num at *; linarith
  obtain ⟨h0, h1⟩ := base_mem_unit_interval P
  rcases P.hq.eq_two_or_eight_dvd with hq | ⟨j, hj⟩
  · have hm : P.m + 1 ≤ 3 := by omega
    rw [hq] at h0 h1 ⊢
    exact (by norm_num : (1 : ℝ) / 8 ≤ (1 - ((2 : ℕ) : ℝ)⁻¹) ^ (3 : ℕ)).trans
      (pow_le_pow_of_le_one h0 h1 hm)
  · have hq := P.hq.two_le
    have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
    let r : ℝ := 1 - (P.q : ℝ)⁻¹
    have hbern : (7 : ℝ) / 8 ≤ r ^ j := by
      have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ - (P.q : ℝ)⁻¹ by linarith) j
      convert h using 1
      · rw [hj, Nat.cast_mul]
        field_simp
        <;> ring
    calc
      _ ≤ ((7 : ℝ) / 8) ^ 9 := by norm_num
      _ ≤ (r ^ j) ^ 9 := by gcongr
      _ = r ^ (j * 9) := (pow_mul ..).symm
      _ ≤ _ := pow_le_pow_of_le_one h0 h1 (by omega)

end

/-! ### Conditional uniform distributions -/

section

variable (P : AdmissibleParams)
include P

/-- The conditional uniform distribution on anticommuting tuples. This is the
sampling convention for the anticommuting cases of
blueprint `lem:qld-win-implications`,
paper `14_analysis_of_the_pauli_basis_test.tex:210-287`. -/
noncomputable def anticommTupleDist :
    Distribution (PauliTuple P) :=
  Distribution.uniformOnFinset (Finset.univ.filter (@IsAnticommuting P))

/-- The conditional uniform distribution on commuting tuples. This is the
sampling convention for the commuting cases of blueprint
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:210-287`. -/
noncomputable def commTupleDist :
    Distribution (PauliTuple P) :=
  Distribution.uniformOnFinset (Finset.univ.filter (@IsCommuting P))

/-- The anticommuting conditional distribution is probabilistic. This is the
well-formedness companion to the conditional sampling in
blueprint `lem:qld-win-implications`. -/
theorem anticommTupleDist_isProbability :
    (anticommTupleDist P).IsProbability := by
  refine Distribution.uniformOnFinset_isProbability _ ?_
  rw [← Finset.card_pos]
  have hq2 := P.hq.two_le
  have hcount := two_mul_card_anticommuting P
  have hpos : 0 < P.q ^ (P.m + 1) * (P.q - 1) ^ (P.m + 1) :=
    Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _)
  omega

/-- The commuting conditional distribution is probabilistic. This is the
well-formedness companion to the conditional sampling in
blueprint `lem:qld-win-implications`. -/
theorem commTupleDist_isProbability :
    (commTupleDist P).IsProbability := by
  refine Distribution.uniformOnFinset_isProbability _ ⟨0, ?_⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  change gammaValue P 0 0 0 0 = 0
  rw [gammaValue_eq_trace_prod]
  simp [fixedBinTrace, binTrace]

end

end

end MIPStarRE.QPBT
