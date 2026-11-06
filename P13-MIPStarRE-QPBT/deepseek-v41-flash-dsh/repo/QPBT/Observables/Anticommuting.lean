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
  (Fin P.m → PauliScalar P) ×
    (Fin P.m → PauliScalar P) × PauliScalar P × PauliScalar P
variable {P : AdmissibleParams}


/-- A Pauli tuple is anticommuting when its phase bit is nonzero. This is
blueprint `def:anticommuting-tuple`, paper
`14_analysis_of_the_pauli_basis_test.tex:64-68`. -/
def IsAnticommuting  (ω : PauliTuple P) : Prop :=
  gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 ≠ 0

/-- A Pauli tuple is commuting when its phase bit vanishes. This is the
complementary case in blueprint
`def:anticommuting-tuple`, paper
`14_analysis_of_the_pauli_basis_test.tex:64-68`. -/
def IsCommuting  (ω : PauliTuple P) : Prop :=
  gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = 0

noncomputable instance instDecidablePredPauliTupleIsAnticommuting (P : AdmissibleParams) :
    DecidablePred (@IsAnticommuting P) := Classical.decPred _

noncomputable instance instDecidablePredPauliTupleIsCommuting (P : AdmissibleParams) :
    DecidablePred (@IsCommuting P) := Classical.decPred _

/-- The uniform probability of the anticommuting event. This is the first
quantity in blueprint
`fact:omega-anticomm-prob`, paper
`14_analysis_of_the_pauli_basis_test.tex:70-77`. -/
noncomputable def anticommProb (P : AdmissibleParams) : ℝ :=
  ((Finset.univ.filter (@IsAnticommuting P)).card : ℝ) /
    Fintype.card (PauliTuple P)

/-- The complementary uniform probability of the commuting event in
blueprint `fact:omega-anticomm-prob`,
paper `14_analysis_of_the_pauli_basis_test.tex:70-77`. -/
noncomputable def commProb (P : AdmissibleParams) : ℝ :=
  ((Finset.univ.filter (@IsCommuting P)).card : ℝ) /
    Fintype.card (PauliTuple P)

/-! ### Auxiliary counting lemmas

The declarations of this section are formalization-only auxiliaries for the
proof of blueprint
`fact:omega-anticomm-prob`. They record the cardinalities used by the
exact computation of the anticommuting probability. -/

/-- Formalization-only auxiliary: the scalar carrier of an admissible parameter
tuple has characteristic two, since it is an algebra over the two-element
field. Blueprint `fact:omega-anticomm-prob`. -/
private theorem pauliScalar_charTwo (P : AdmissibleParams) :
    CharP (PauliScalar P) 2 :=
  (Algebra.charP_iff (ZMod 2) (PauliScalar P) 2).mp (ZMod.charP 2)

/-- Formalization-only auxiliary: the scalar carrier of an admissible parameter
tuple has exactly `q` elements. Blueprint
`fact:omega-anticomm-prob`. -/
private theorem card_pauliScalar (P : AdmissibleParams) :
    Fintype.card (PauliScalar P) = P.q :=
  @FieldModel.card P.q P.model.toFieldModel
variable (P : AdmissibleParams)


/-- The phase bit of a Pauli tuple is the trace of `r_Z r_X` times the product
of the coordinate sums `1 + u_{X,i} + u_{Z,i}`. This is the closed form of
`γ(ω)` derived in the proof of blueprint
`fact:omega-anticomm-prob`. -/
private theorem gammaValue_eq_trace_prod 
    (uX uZ : Fin P.m → PauliScalar P) (rX rZ : PauliScalar P) :
    gammaValue P uX uZ rX rZ =
      fixedBinTrace P.model (rZ * (rX * ∏ i : Fin P.m, (1 + uX i + uZ i))) := by
  haveI := pauliScalar_charTwo P
  have hprod : (∑ y : Cube P.m, indicatorVec uX y * indicatorVec uZ y)
      = ∏ i : Fin P.m, (1 + uX i + uZ i) :=
    sum_indicatorVec_mul_indicatorVec uX uZ
  unfold gammaValue
  congr 1
  rw [← hprod]
  simp [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- Formalization-only auxiliary: the field trace onto the two-element field
takes each of its two values on exactly half of the scalars. This is the final
step of the proof of blueprint
`fact:omega-anticomm-prob`. -/
private theorem two_mul_card_trace_ne  :
    2 * (Finset.univ.filter
        (fun a : PauliScalar P => fixedBinTrace P.model a ≠ 0)).card = P.q := by
  classical
  haveI := pauliScalar_charTwo P
  have hK := card_pauliScalar P
  have hadd : ∀ a c : PauliScalar P,
      fixedBinTrace P.model (a + c)
        = fixedBinTrace P.model a + fixedBinTrace P.model c := by
    intro a c
    simp [fixedBinTrace, binTrace]
  obtain ⟨b, hb⟩ : ∃ b : PauliScalar P, fixedBinTrace P.model b = 1 := by
    have hpos : 0 < P.model.basisDim := by
      obtain ⟨j, hj⟩ := P.model.basisDimOdd
      omega
    exact ⟨P.model.basis ⟨0, hpos⟩,
      fixedFieldModel_trace_basis_eq_one P.model ⟨0, hpos⟩⟩
  have hbb : b + b = 0 := CharTwo.add_self_eq_zero b
  have himg :
      (Finset.univ.filter
          (fun a : PauliScalar P => fixedBinTrace P.model a = 0)).image (fun a => a + b)
        = Finset.univ.filter
            (fun a : PauliScalar P => ¬ (fixedBinTrace P.model a = 0)) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [hadd, hc, hb]
      simp
    · intro ha
      refine ⟨a + b, ?_, ?_⟩
      · rw [hadd, hb]
        have hone : fixedBinTrace P.model a = 1 := by
          revert ha
          generalize fixedBinTrace P.model a = t
          revert t
          decide
        rw [hone]
        decide
      · rw [add_assoc, hbb, add_zero]
  have hinj : Function.Injective (fun a : PauliScalar P => a + b) :=
    fun _ _ h => by simpa using h
  have hcard :
      (Finset.univ.filter (fun a : PauliScalar P => fixedBinTrace P.model a = 0)).card
        = (Finset.univ.filter
            (fun a : PauliScalar P => ¬ (fixedBinTrace P.model a = 0))).card := by
    rw [← himg, Finset.card_image_of_injective _ hinj]
  have hsplit :
      (Finset.univ.filter (fun a : PauliScalar P => fixedBinTrace P.model a = 0)).card
          + (Finset.univ.filter
              (fun a : PauliScalar P => ¬ (fixedBinTrace P.model a = 0))).card
        = Fintype.card (PauliScalar P) :=
    Finset.card_filter_add_card_filter_not _
  rw [hK] at hsplit
  simp only [ne_eq]
  omega

/-- Formalization-only auxiliary: the number of Pauli tuples. Blueprint
`fact:omega-anticomm-prob`. -/
private theorem card_pauliTuple  :
    Fintype.card (PauliTuple P) = P.q ^ P.m * (P.q ^ P.m * (P.q * P.q)) := by
  have hK := card_pauliScalar P
  simp [PauliTuple, Fintype.card_prod, hK]

/-- Twice the number of anticommuting tuples is `q^{m+1}(q-1)^{m+1}`. This is
the exact count established in the proof of blueprint
`fact:omega-anticomm-prob`. -/
private theorem two_mul_card_anticommuting  :
    2 * (Finset.univ.filter (@IsAnticommuting P)).card
      = P.q ^ (P.m + 1) * (P.q - 1) ^ (P.m + 1) := by
  classical
  haveI := pauliScalar_charTwo P
  have h2 : (2 : PauliScalar P) = 0 := CharTwo.two_eq_zero
  have hK := card_pauliScalar P
  have htr0 : fixedBinTrace P.model 0 = 0 := by
    simp [fixedBinTrace, binTrace]
  set N := (Finset.univ.filter
    (fun a : PauliScalar P => fixedBinTrace P.model a ≠ 0)).card with hNdef
  have hN : 2 * N = P.q := two_mul_card_trace_ne P
  -- the innermost sum, over the second scalar coordinate
  have hinner : ∀ c : PauliScalar P,
      (∑ r : PauliScalar P, if fixedBinTrace P.model (r * c) ≠ 0 then (1 : ℕ) else 0)
        = if c = 0 then 0 else N := by
    intro c
    by_cases hc : c = 0
    · subst hc
      simp [htr0]
    · rw [if_neg hc, hNdef, Finset.card_filter]
      exact Fintype.sum_equiv (Equiv.mulRight₀ c hc)
        (fun r => if fixedBinTrace P.model (r * c) ≠ 0 then (1 : ℕ) else 0)
        (fun a => if fixedBinTrace P.model a ≠ 0 then (1 : ℕ) else 0)
        (fun r => rfl)
  -- the sum over the first scalar coordinate
  have hnzcard :
      (Finset.univ.filter (fun x : PauliScalar P => ¬ (x = 0))).card = P.q - 1 := by
    have h1 : (Finset.univ.filter (fun x : PauliScalar P => x ≠ 0))
        = Finset.univ.erase 0 := Finset.filter_ne' _ _
    simp only [ne_eq] at h1
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hK]
  have hmid : ∀ dd : PauliScalar P,
      (∑ rX : PauliScalar P, if rX * dd = 0 then (0 : ℕ) else N)
        = if dd = 0 then 0 else (P.q - 1) * N := by
    intro dd
    by_cases hd : dd = 0
    · subst hd
      simp
    · rw [if_neg hd]
      have hcong : ∀ rX : PauliScalar P,
          (if rX * dd = 0 then (0 : ℕ) else N) = if rX = 0 then 0 else N := by
        intro rX
        by_cases hr : rX = 0
        · simp [hr]
        · rw [if_neg (by simpa using mul_ne_zero hr hd), if_neg hr]
      rw [Finset.sum_congr rfl (fun x _ => hcong x), Finset.sum_ite]
      simp [hnzcard]
  -- the sum over the second point block
  have hDcard : ∀ uX : Fin P.m → PauliScalar P,
      (Finset.univ.filter (fun uZ : Fin P.m → PauliScalar P =>
        ¬ ((∏ i : Fin P.m, (1 + uX i + uZ i)) = 0))).card = (P.q - 1) ^ P.m := by
    intro uX
    have hset : (Finset.univ.filter (fun uZ : Fin P.m → PauliScalar P =>
        ¬ ((∏ i : Fin P.m, (1 + uX i + uZ i)) = 0)))
        = Fintype.piFinset (fun i : Fin P.m => Finset.univ.erase (1 + uX i)) := by
      ext uZ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
        Finset.mem_erase, and_true]
      constructor
      · intro h i hi
        refine h ?_
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        rw [hi]
        linear_combination (1 + uX i) * h2
      · intro h hz
        rw [Finset.prod_eq_zero_iff] at hz
        obtain ⟨i, -, hi⟩ := hz
        exact h i (by linear_combination hi - (1 + uX i) * h2)
    rw [hset, Fintype.card_piFinset]
    simp [Finset.card_erase_of_mem, Finset.card_univ, hK]
  have houter : ∀ uX : Fin P.m → PauliScalar P,
      (∑ uZ : Fin P.m → PauliScalar P,
          if (∏ i : Fin P.m, (1 + uX i + uZ i)) = 0 then (0 : ℕ) else (P.q - 1) * N)
        = (P.q - 1) ^ P.m * ((P.q - 1) * N) := by
    intro uX
    rw [Finset.sum_ite]
    simp [hDcard uX]
  have step1 : ∀ (uX uZ : Fin P.m → PauliScalar P) (rX : PauliScalar P),
      (∑ rZ : PauliScalar P,
          if IsAnticommuting ((uX, uZ, rX, rZ) : PauliTuple P) then (1 : ℕ) else 0)
        = if rX * ∏ i : Fin P.m, (1 + uX i + uZ i) = 0 then 0 else N := by
    intro uX uZ rX
    have hcongr : ∀ rZ : PauliScalar P,
        (if IsAnticommuting ((uX, uZ, rX, rZ) : PauliTuple P) then (1 : ℕ) else 0)
          = if fixedBinTrace P.model
              (rZ * (rX * ∏ i : Fin P.m, (1 + uX i + uZ i))) ≠ 0 then 1 else 0 := by
      intro rZ
      have hiff : IsAnticommuting ((uX, uZ, rX, rZ) : PauliTuple P)
          ↔ fixedBinTrace P.model
              (rZ * (rX * ∏ i : Fin P.m, (1 + uX i + uZ i))) ≠ 0 := by
        unfold IsAnticommuting
        rw [gammaValue_eq_trace_prod]
      by_cases h : fixedBinTrace P.model
          (rZ * (rX * ∏ i : Fin P.m, (1 + uX i + uZ i))) ≠ 0
      · rw [if_pos (hiff.mpr h), if_pos h]
      · rw [if_neg (fun hh => h (hiff.mp hh)), if_neg h]
    rw [Finset.sum_congr rfl (fun x _ => hcongr x), hinner]
  have hcount : (Finset.univ.filter (@IsAnticommuting P)).card
      = P.q ^ P.m * ((P.q - 1) ^ P.m * ((P.q - 1) * N)) := by
    rw [Finset.card_filter]
    simp only [Fintype.sum_prod_type]
    calc (∑ uX : Fin P.m → PauliScalar P, ∑ uZ : Fin P.m → PauliScalar P,
            ∑ rX : PauliScalar P, ∑ rZ : PauliScalar P,
              (if IsAnticommuting ((uX, uZ, rX, rZ) : PauliTuple P) then (1 : ℕ) else 0))
        = ∑ _uX : Fin P.m → PauliScalar P, (P.q - 1) ^ P.m * ((P.q - 1) * N) := by
          refine Finset.sum_congr rfl fun uX _ => ?_
          rw [← houter uX]
          refine Finset.sum_congr rfl fun uZ _ => ?_
          rw [← hmid (∏ i : Fin P.m, (1 + uX i + uZ i))]
          exact Finset.sum_congr rfl fun rX _ => step1 uX uZ rX
      _ = P.q ^ P.m * ((P.q - 1) ^ P.m * ((P.q - 1) * N)) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          congr 1
          simp [hK]
  rw [hcount]
  have hexpand : 2 * (P.q ^ P.m * ((P.q - 1) ^ P.m * ((P.q - 1) * N)))
      = P.q ^ P.m * ((P.q - 1) ^ P.m * ((P.q - 1) * (2 * N))) := by ring
  rw [hexpand, hN, pow_succ, pow_succ]
  ring

/-- The anticommuting and commuting events partition the tuple space.
Blueprint `fact:omega-anticomm-prob`. -/
private theorem card_comm_add_card_anticomm  :
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
private theorem card_pauliTuple_pos  :
    0 < Fintype.card (PauliTuple P) := by
  have hq : 0 < P.q := lt_of_lt_of_le (by norm_num) P.hq.two_le
  rw [card_pauliTuple P]
  exact Nat.mul_pos (pow_pos hq _) (Nat.mul_pos (pow_pos hq _) (Nat.mul_pos hq hq))

/-! ### The exact anticommuting probability -/

/-- Exact anticommuting probability from blueprint
`fact:omega-anticomm-prob`; its derivation replaces the erroneous
Schwartz--Zippel argument at paper
`14_analysis_of_the_pauli_basis_test.tex:79-93`. -/
theorem anticommProb_eq  :
    anticommProb P = (1 - (P.q : ℝ)⁻¹) ^ (P.m + 1) / 2 := by
  have hq2 := P.hq.two_le
  have hqR := by
    have h := by omega
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
theorem commProb_eq_one_sub_anticommProb  :
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
private theorem base_mem_unit_interval  :
    (0 : ℝ) ≤ 1 - (P.q : ℝ)⁻¹ ∧ (1 : ℝ) - (P.q : ℝ)⁻¹ ≤ 1 := by
  have hq2 := P.hq.two_le
  have hqR : (2 : ℝ) ≤ (P.q : ℝ) := by exact_mod_cast hq2
  have hinv : (P.q : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hinv0 : (0 : ℝ) ≤ (P.q : ℝ)⁻¹ := by positivity
  constructor <;> linarith

/-- The commuting event has probability at least one half. This is the
complementary bound in blueprint
`fact:omega-anticomm-prob`, paper
`14_analysis_of_the_pauli_basis_test.tex:70-77`. -/
theorem commProb_ge_half  : 1 / 2 ≤ commProb P := by
  obtain ⟨h0, h1⟩ := base_mem_unit_interval P
  have hle : (1 - (P.q : ℝ)⁻¹) ^ (P.m + 1) ≤ 1 := pow_le_one₀ h0 h1
  rw [commProb_eq_one_sub_anticommProb, anticommProb_eq]
  linarith

/-- When `m ≤ q`, the anticommuting event has the uniform constant lower
bound added in blueprint
`fact:omega-anticomm-prob`. -/
theorem anticommProb_ge_of_m_le_q  (hmq : P.m ≤ P.q) :
    (2 : ℝ) ^ (-4 : ℤ) ≤ anticommProb P := by
  obtain ⟨h0, h1⟩ := base_mem_unit_interval P
  have hq2 := P.hq.two_le
  have hqR : (2 : ℝ) ≤ (P.q : ℝ) := by exact_mod_cast hq2
  have hmain : (1 : ℝ) / 8 ≤ (1 - (P.q : ℝ)⁻¹) ^ (P.m + 1) := by
    rcases P.hq.eq_two_or_eight_dvd with hq | hdvd
    · have hm := hq ▸ hmq
      have hb : (1 : ℝ) - (P.q : ℝ)⁻¹ = 1 / 2 := by
        rw [hq]
        norm_num
      rw [hb]
      calc (1 : ℝ) / 8 = (1 / 2 : ℝ) ^ 3 := by norm_num
        _ ≤ (1 / 2 : ℝ) ^ (P.m + 1) :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    · obtain ⟨j, hj⟩ := hdvd
      have hj1 : 1 ≤ j := by omega
      have hjR : (P.q : ℝ) = 8 * (j : ℝ) := by
        rw [hj]
        push_cast
        ring
      have hbern : (7 : ℝ) / 8 ≤ (1 - (P.q : ℝ)⁻¹) ^ j := by
        have hle : (-2 : ℝ) ≤ -(P.q : ℝ)⁻¹ := by
          have : (0 : ℝ) ≤ (P.q : ℝ)⁻¹ := by positivity
          linarith
        have hb := one_add_mul_le_pow hle j
        have hrw : (1 : ℝ) + (j : ℝ) * (-(P.q : ℝ)⁻¹) = 7 / 8 := by
          rw [hjR]
          field_simp
          ring
        have hbase : (1 : ℝ) + -(P.q : ℝ)⁻¹ = 1 - (P.q : ℝ)⁻¹ := by ring
        rw [hrw, hbase] at hb
        exact hb
      have hexp : P.m + 1 ≤ 9 * j := by omega
      have hstep : (1 - (P.q : ℝ)⁻¹) ^ (9 * j) ≤ (1 - (P.q : ℝ)⁻¹) ^ (P.m + 1) :=
        pow_le_pow_of_le_one h0 h1 hexp
      have hpow : ((7 : ℝ) / 8) ^ 9 ≤ ((1 - (P.q : ℝ)⁻¹) ^ j) ^ 9 := by
        gcongr
      rw [← pow_mul, mul_comm j 9] at hpow
      linarith
  rw [anticommProb_eq]
  have hconst : (2 : ℝ) ^ (-4 : ℤ) = 1 / 8 / 2 := by norm_num
  rw [hconst]
  linarith

/-! ### Conditional uniform distributions -/

/-- The conditional uniform distribution on anticommuting tuples. This is the
sampling convention for the anticommuting cases of
blueprint `lem:qld-win-implications`,
paper `14_analysis_of_the_pauli_basis_test.tex:210-287`. -/
noncomputable def anticommTupleDist (P : AdmissibleParams) :
    Distribution (PauliTuple P) :=
  Distribution.uniformOnFinset (Finset.univ.filter (@IsAnticommuting P))

/-- The conditional uniform distribution on commuting tuples. This is the
sampling convention for the commuting cases of blueprint
`lem:qld-win-implications`, paper
`14_analysis_of_the_pauli_basis_test.tex:210-287`. -/
noncomputable def commTupleDist (P : AdmissibleParams) :
    Distribution (PauliTuple P) :=
  Distribution.uniformOnFinset (Finset.univ.filter (@IsCommuting P))

/-- The anticommuting conditional distribution is probabilistic. This is the
well-formedness companion to the conditional sampling in
blueprint `lem:qld-win-implications`. -/
theorem anticommTupleDist_isProbability  :
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
theorem commTupleDist_isProbability  :
    (commTupleDist P).IsProbability := by
  refine Distribution.uniformOnFinset_isProbability _ ⟨0, ?_⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  change gammaValue P 0 0 0 0 = 0
  rw [gammaValue_eq_trace_prod]
  simp [fixedBinTrace, binTrace]

end

end MIPStarRE.QPBT
