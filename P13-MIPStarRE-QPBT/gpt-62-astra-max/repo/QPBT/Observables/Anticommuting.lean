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

/-- A Pauli tuple is anticommuting when its phase bit is nonzero. This is
blueprint `def:anticommuting-tuple`, paper
`14_analysis_of_the_pauli_basis_test.tex:64-68`. -/
def IsAnticommuting : Prop :=
  gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 ≠ 0

/-- A Pauli tuple is commuting when its phase bit vanishes. This is the
complementary case in blueprint
`def:anticommuting-tuple`, paper
`14_analysis_of_the_pauli_basis_test.tex:64-68`. -/
def IsCommuting : Prop :=
  gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = 0

end

variable (P : AdmissibleParams)

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

/-! ### Auxiliary counting lemmas

The declarations of this section are formalization-only auxiliaries for the
proof of blueprint
`fact:omega-anticomm-prob`. They record the cardinalities used by the
exact computation of the anticommuting probability. -/

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
  unfold gammaValue
  congr 1
  rw [← (sum_indicatorVec_mul_indicatorVec uX uZ)]
  simp [dotProduct, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- Formalization-only auxiliary: the field trace onto the two-element field
takes each of its two values on exactly half of the scalars. This is the final
step of the proof of blueprint
`fact:omega-anticomm-prob`. -/
private theorem two_mul_card_trace_ne :
    2 * (Finset.univ.filter
        (fun a : PauliScalar P => fixedBinTrace P.model a ≠ 0)).card = P.q := by
  classical
  haveI := pauliScalar_charTwo P
  have hadd : ∀ a c : PauliScalar P,
      fixedBinTrace P.model (a + c)
        = fixedBinTrace P.model a + fixedBinTrace P.model c := by
    simp [fixedBinTrace]
  obtain ⟨b, hb⟩ : ∃ b : PauliScalar P, fixedBinTrace P.model b = 1 := by
    have hpos : 0 < P.model.basisDim := by
      obtain ⟨j, hj⟩ := P.model.basisDimOdd
      omega
    exact ⟨P.model.basis ⟨0, hpos⟩,
      by
        apply trace_basis_eq_one_of_selfDual_normal P.model.basisDimOdd P.model.basis
        · exact id P.model.selfDual
        · simpa [Basis.IsNormal, ZMod.card] using P.model.normal⟩
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
      · simp_all
        have hone : fixedBinTrace P.model a = 1 := by
          revert ha
          generalize fixedBinTrace P.model a = t
          revert t
          decide
        rw [hone]
        decide
      · simp [add_assoc, (CharTwo.add_self_eq_zero b)]
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
              _).card
        = Fintype.card (PauliScalar P) :=
    Finset.card_filter_add_card_filter_not _
  rw [(card_pauliScalar P)] at hsplit
  simp
  omega

/-- Formalization-only auxiliary: the number of Pauli tuples. Blueprint
`fact:omega-anticomm-prob`. -/
private theorem card_pauliTuple :
    Fintype.card (PauliTuple P) = P.q ^ P.m * (P.q ^ P.m * (P.q * P.q)) := by
  simp [PauliTuple]

/-- Twice the number of anticommuting tuples is `q^{m+1}(q-1)^{m+1}`. This is
the exact count established in the proof of blueprint
`fact:omega-anticomm-prob`. -/
private theorem two_mul_card_anticommuting :
    2 * (Finset.univ.filter (@IsAnticommuting P)).card
      = P.q ^ (P.m + 1) * (P.q - 1) ^ (P.m + 1) := by
  classical
  haveI := pauliScalar_charTwo P
  have h2 : (2 : PauliScalar P) = 0 := CharTwo.two_eq_zero
  have hK := card_pauliScalar P
  set N := (Finset.univ.filter
    (fun a : PauliScalar P => fixedBinTrace P.model a ≠ 0)).card with hNdef
  have hinner : ∀ c : PauliScalar P,
      (∑ r : PauliScalar P, if fixedBinTrace P.model (r * c) ≠ 0 then 1 else 0)
        = if c = 0 then 0 else N := by
    intro c
    by_cases hc : c = 0
    · subst hc
      simp [fixedBinTrace]
    · rw [if_neg hc, hNdef, Finset.card_filter]
      exact Fintype.sum_equiv (Equiv.mulRight₀ c hc)
        _
        _
        (fun r => rfl)
  -- the sum over the first scalar coordinate
  have hnzcard :
      (Finset.univ.filter (fun x : PauliScalar P => ¬ (x = 0))).card = P.q - 1 := by
    have h1 : (Finset.univ.filter (fun x : PauliScalar P => x ≠ 0))
        = Finset.univ.erase 0 := Finset.filter_ne' _ _
    simp [*]
  have hmid : ∀ dd : PauliScalar P,
      (∑ rX : PauliScalar P, if rX * dd = 0 then 0 else N)
        = if dd = 0 then 0 else (P.q - 1) * N := by
    intro dd
    by_cases hd : dd = 0
    · subst hd
      simp
    · rw [if_neg hd]
      have hcong : ∀ rX : PauliScalar P,
          (if rX * dd = 0 then 0 else N) = if rX = 0 then 0 else N := by
        intro rX
        by_cases hr : rX = 0
        · simp [hr]
        · simp_all
      rw [Finset.sum_congr rfl (fun x _ => hcong x), Finset.sum_ite]
      simp [hnzcard]
  -- the sum over the second point block
  have hDcard : ∀ uX : PauliPoint P,
      (Finset.univ.filter (fun uZ : PauliPoint P =>
        ¬ ((∏ i : Fin P.m, (1 + uX i + uZ i)) = 0))).card = (P.q - 1) ^ P.m := by
    intro uX
    have hset : (Finset.univ.filter (fun uZ : PauliPoint P =>
        ¬ ((∏ i : Fin P.m, (1 + uX i + uZ i)) = 0)))
        = Fintype.piFinset (fun i : Fin P.m => Finset.univ.erase (1 + uX i)) := by
      ext uZ
      simp
      constructor
      · intro h i hi
        apply h
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        rw [hi]
        linear_combination (1 + uX i) * h2
      · intro h hz
        rw [Finset.prod_eq_zero_iff] at hz
        obtain ⟨i, -, hi⟩ := hz
        exact h i (by linear_combination hi - (1 + uX i) * h2)
    rw [hset, Fintype.card_piFinset]
    simp
  have houter : ∀ uX : PauliPoint P,
      (∑ uZ : PauliPoint P,
          if (∏ i : Fin P.m, (1 + uX i + uZ i)) = 0 then 0 else (P.q - 1) * N)
        = (P.q - 1) ^ P.m * ((P.q - 1) * N) := by
    simp [Finset.sum_ite, hDcard]
  have step1 : ∀ (uX uZ : PauliPoint P) (rX : PauliScalar P),
      (∑ rZ : PauliScalar P,
          if IsAnticommuting ((uX, uZ, rX, rZ)) then 1 else 0)
        = if rX * ∏ i : Fin P.m, (1 + uX i + uZ i) = 0 then 0 else N := by
    intro uX uZ rX
    have hcongr : ∀ rZ : PauliScalar P,
        (if IsAnticommuting ((uX, uZ, rX, rZ)) then 1 else 0)
          = if fixedBinTrace P.model
              (rZ * (rX * ∏ i : Fin P.m, (1 + uX i + uZ i))) ≠ 0 then 1 else 0 := by
      simp [IsAnticommuting, gammaValue_eq_trace_prod]
    rw [Finset.sum_congr rfl (fun x _ => hcongr x), hinner]
  have hcount : (Finset.univ.filter (@IsAnticommuting P)).card
      = P.q ^ P.m * ((P.q - 1) ^ P.m * ((P.q - 1) * N)) := by
    rw [Finset.card_filter]
    simp only [Fintype.sum_prod_type]
    calc _
        = ∑ _uX : PauliPoint P, (P.q - 1) ^ P.m * ((P.q - 1) * N) := by
          congr 1 with uX
          rw [← houter]
          congr 1 with uZ
          rw [← hmid]
          exact Finset.sum_congr rfl fun rX _ => step1 uX uZ rX
      _ = _ := by
          simp
  rw [hcount]
  have hexpand : 2 * (P.q ^ P.m * ((P.q - 1) ^ P.m * ((P.q - 1) * N)))
      = P.q ^ P.m * ((P.q - 1) ^ P.m * ((P.q - 1) * (2 * N))) := by ring
  rw [hexpand, (two_mul_card_trace_ne P), pow_succ, pow_succ]
  ring

/-! ### The exact anticommuting probability -/

/-- Exact anticommuting probability from blueprint
`fact:omega-anticomm-prob`; its derivation replaces the erroneous
Schwartz--Zippel argument at paper
`14_analysis_of_the_pauli_basis_test.tex:79-93`. -/
theorem anticommProb_eq :
    anticommProb P = (1 - (P.q : ℝ)⁻¹) ^ (P.m + 1) / 2 := by
  have hq2 := P.hq.two_le
  have hcast := congrArg (fun n : ℕ => (n : ℝ)) (two_mul_card_anticommuting P)
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
    Nat.cast_sub (by omega : 1 ≤ P.q), Nat.cast_one, Nat.cast_ofNat] at hcast
  have hval : (Finset.univ.filter (@IsAnticommuting P)).card
      = P.q ^ (P.m + 1) * ((P.q : ℝ) - 1) ^ (P.m + 1) / 2 := by linarith
  have hbase : 1 - (P.q : ℝ)⁻¹ = (P.q - 1) / P.q := by
    field_simp
  rw [anticommProb, hval, card_pauliTuple, hbase, div_pow]
  push_cast
  field_simp
  ring

/-- A tuple is commuting with the probability complementary to the
anticommuting one. This is the complementarity clause of
blueprint `fact:omega-anticomm-prob`,
paper `14_analysis_of_the_pauli_basis_test.tex:70-77`. -/
theorem commProb_eq_one_sub_anticommProb :
    commProb P = 1 - anticommProb P := by
  have hpos : 0 < (Fintype.card (PauliTuple P) : ℝ) := by
    positivity
  have hsum : (Finset.univ.filter (@IsCommuting P)).card
      + (Finset.univ.filter (@IsAnticommuting P)).card
      = (Fintype.card (PauliTuple P) : ℝ) := by
    exact_mod_cast (by
                     classical
                     have hfil : (Finset.univ.filter (@IsAnticommuting P))
                         = Finset.univ.filter (fun ω : PauliTuple P => ¬ (@IsCommuting P ω)) := by
                       apply Finset.filter_congr
                       simp [IsAnticommuting, IsCommuting]
                     rw [hfil, ← Finset.card_univ]
                     exact Finset.card_filter_add_card_filter_not _)
  rw [commProb, anticommProb, eq_sub_iff_add_eq, ← add_div, hsum,
    div_self hpos.ne']

/-- Formalization-only auxiliary: the base `1 - q^{-1}` of the exact
anticommuting probability lies in the unit interval. Blueprint
`fact:omega-anticomm-prob`. -/
private theorem base_mem_unit_interval :
    (0 : ℝ) ≤ 1 - (P.q : ℝ)⁻¹ ∧ (1 : ℝ) - (P.q : ℝ)⁻¹ ≤ 1 := by
  have hq2 := P.hq.two_le
  have hqR : 2 ≤ (P.q : ℝ) := by exact_mod_cast hq2
  have hinv : (P.q : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hinv0 : 0 ≤ (P.q : ℝ)⁻¹ := by positivity
  constructor <;> linarith

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
  obtain ⟨h0, h1⟩ := base_mem_unit_interval P
  have hq2 := P.hq.two_le
  have hqR : 2 ≤ (P.q : ℝ) := by exact_mod_cast hq2
  have hmain : 1 / 8 ≤ (1 - (P.q : ℝ)⁻¹) ^ (P.m + 1) := by
    rcases P.hq.eq_two_or_eight_dvd with hq | hdvd
    · have hb : 1 - (P.q : ℝ)⁻¹ = 1 / 2 := by
        rw [hq]
        norm_num
      rw [hb]
      calc _ = (1 / 2 : ℝ) ^ 3 := by norm_num
        _ ≤ _ :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    · obtain ⟨j, hj⟩ := hdvd
      have hj1 : 1 ≤ j := by omega
      have hjR : P.q = 8 * (j : ℝ) := by
        simp [hj]
      have hbern : 7 / 8 ≤ (1 - (P.q : ℝ)⁻¹) ^ j := by
        have hle : (-2) ≤ -(P.q : ℝ)⁻¹ := by
          linarith
        have hb := one_add_mul_le_pow hle j
        have hrw : 1 + j * (-(P.q : ℝ)⁻¹) = 7 / 8 := by
          rw [hjR]
          field_simp
          ring
        have hbase : 1 + -(P.q : ℝ)⁻¹ = 1 - (P.q : ℝ)⁻¹ := by ring
        rw [hrw, hbase] at hb
        exact hb
      have hexp : P.m + 1 ≤ 9 * j := by omega
      have hstep :=
        pow_le_pow_of_le_one h0 h1 hexp
      have hpow : (7 / 8) ^ 9 ≤ ((1 - (P.q : ℝ)⁻¹) ^ j) ^ 9 := by
        gcongr
      rw [← pow_mul, mul_comm] at hpow
      linarith
  rw [anticommProb_eq]
  linarith

/-! ### Conditional uniform distributions -/

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
  apply Distribution.uniformOnFinset_isProbability
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
  change _ = 0
  rw [gammaValue_eq_trace_prod]
  simp [fixedBinTrace]

end

end MIPStarRE.QPBT
